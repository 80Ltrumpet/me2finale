//! Outcome data generation

use std::iter::{repeat, zip};
use std::sync::Arc;

use dashmap::DashMap;
use itertools::Itertools;
use rayon::prelude::*;

use crate::ally::{Ally, AllySet};
use crate::death::{self, DeathReason};
use crate::decision::{DecisionPathLedger, FirstLeader, SquadSelection};
use crate::outcome::{DecisionPathMetadata, Outcome, OutcomeMap};

/// Generates an [`OutcomeMap`] by recursively traversing all decision paths.
///
/// # Performance
///
/// This function traverses over 64 _billion_ decision paths, resulting in over 700 _thousand_
/// outcomes. However, the algorithm is significantly accelerated in two ways:
///
/// 1. It uses [`rayon`]'s _parallel iterators_ (via the [`IntoParallelIterator`] and
///    [`ParallelBridge`] traits) in the first three levels of the call stack. Applying this
///    pattern—and [`rayon::join`], where applicable—further in the recursion yields no
///    significant, additional improvement in run time.
/// 2. It uses a shared [`dashmap::DashMap`] to _concurrently_ store [`Outcome`]s and modify their
///    [`DecisionPathMetadata`] values.
///
/// In combination, these modifications decrease the run time by almost an order of magnitude
/// compared to running the same algorithm on a single thread. To put this in real numbers, when
/// measured on the author's system, this took the run time from about 90 minutes down to about
/// 10.5 minutes!
pub fn outcome_map() -> OutcomeMap {
    OutcomeMapGenerator::new()
        .generate()
        .into_iter()
        .par_bridge()
        .collect()
}

/// Implementation detail of the private [`OutcomeMapGenerator`]
type OutcomeDashMap = DashMap<Outcome, DecisionPathMetadata>;

/// Private struct that supports recursive traversal of decision paths
///
/// See [`outcome_map`] for algorithm details.
#[derive(Clone)]
struct OutcomeMapGenerator {
    choices: DecisionPathLedger,
    outcomes: Arc<OutcomeDashMap>,
}

impl OutcomeMapGenerator {
    /// Creates a new [`OutcomeMapGenerator`].
    fn new() -> Self {
        Self {
            choices: Default::default(),
            outcomes: Arc::new(OutcomeDashMap::new()),
        }
    }

    /// Generates outcomes by recursively tracing all possible decision paths.
    fn generate(self) -> OutcomeDashMap {
        // At least three optional allies must be recruited to begin the final mission.
        (3..=AllySet::RECRUITABLE.len())
            .into_par_iter()
            .for_each_init(|| self.clone(), Self::recruitment);

        Arc::try_unwrap(self.outcomes).expect("`outcomes` has only one strong reference")
    }

    /// Selects which optional allies to recruit.
    fn recruitment(&mut self, count: usize) {
        AllySet::RECRUITABLE
            .iter()
            .combinations(count)
            .map(|combo| combo.into_iter().collect::<AllySet>())
            .par_bridge()
            .for_each_init(|| self.clone(), Self::loyalty_missions);
    }

    /// Selects which loyalty missions to complete.
    fn loyalty_missions(&mut self, recruits: AllySet) {
        self.choices.recruitment = recruits;
        let allies = AllySet::REQUIRED | recruits;
        let loyalty_mission_iter = allies
            .iter()
            .powerset()
            .map(|subset| subset.into_iter().collect::<AllySet>());

        zip(repeat(allies), loyalty_mission_iter)
            .par_bridge()
            .for_each_init(|| self.clone(), Self::recruit_morinth);
    }

    /// Chooses whether to recruit Morinth, if Samara's loyalty mission was completed.
    fn recruit_morinth(&mut self, (allies, loyalty_missions): (AllySet, AllySet)) {
        self.choices.loyalty_missions = loyalty_missions;
        self.upgrade_armor(allies);

        if loyalty_missions.contains(Ally::Samara) {
            // Choosing Morinth kills Samara and vice versa.
            self.choices.recruitment ^= AllySet::ASARI;
            self.upgrade_armor(allies ^ AllySet::ASARI);
        }
    }

    /// Returns the set of loyal allies based on completed loyalty missions.
    ///
    /// This method does _not_ take currently surviving allies into account, so its result should
    /// only be used as a filter.
    fn loyal(&self) -> AllySet {
        // Morinth is always loyal.
        self.choices.loyalty_missions | Ally::Morinth
    }

    /// Chooses whether to upgrade _The Normandy_'s armor.
    fn upgrade_armor(&mut self, allies: AllySet) {
        self.choices.upgraded_armor = true;
        self.upgrade_shield(allies);

        self.choices.upgraded_armor = false;
        // If the armor is not upgraded, there will be a victim.
        let victim = DeathReason::NoArmorUpgrade.get_victim(allies);
        self.upgrade_shield(allies - victim);
    }

    /// Chooses whether to upgrade _The Normandy_'s shields and, if not, selects allies for the
    /// squad Shepard brings to defend the cargo bay.
    fn upgrade_shield(&mut self, allies: AllySet) {
        self.choices.cargo_bay_squad = SquadSelection::new();
        self.choices.upgraded_shield = true;
        self.upgrade_weapon(allies);

        self.choices.upgraded_shield = false;
        // If the shield is not upgraded, there will be a victim, but it depends on who is
        // selected for the cargo bay squad.
        let mut potential_victims = allies;
        for _ in 0..3 {
            let victim = DeathReason::NoShieldUpgrade.get_victim(potential_victims);
            self.choices.cargo_bay_squad.add_victim(victim);
            self.upgrade_weapon(allies - victim);
            potential_victims -= victim;
        }
    }

    /// Chooses whether to upgrade _The Normandy_'s weapons.
    fn upgrade_weapon(&mut self, allies: AllySet) {
        self.choices.upgraded_weapon = true;
        self.tech_specialist(allies);

        self.choices.upgraded_weapon = false;
        // If the weapon is not upgraded, there will be a victim.
        let victim = DeathReason::NoWeaponUpgrade.get_victim(allies);
        self.tech_specialist(allies - victim);
    }

    /// Selects a tech specialist.
    fn tech_specialist(&mut self, allies: AllySet) {
        for tech in allies & AllySet::TECHS {
            self.choices.tech_specialist = Some(tech);
            self.first_leader(allies);
        }
    }

    /// Selects a leader for the first fireteam if the tech is loyal and ideal.
    fn first_leader(&mut self, allies: AllySet) {
        self.choices.first_leader = None;

        // If the tech specialist is neither loyal nor ideal, they will die.
        let tech = self.choices.tech_specialist.unwrap();
        if !(self.loyal() & AllySet::IDEAL_TECHS).contains(tech) {
            self.biotic_specialist(allies - tech);
            return;
        }

        // Otherwise, their survival depends on the first fireteam leader.
        let ideal_leaders = (allies - tech) & self.loyal() & AllySet::IDEAL_LEADERS;
        if !ideal_leaders.is_empty() {
            self.choices.first_leader = Some(FirstLeader {
                is_ideal: true,
                ideal_leaders,
            });
            self.biotic_specialist(allies);
        }

        // Choosing a non-ideal leader causes the tech specialist to die.
        self.choices.first_leader = Some(FirstLeader {
            is_ideal: false,
            ideal_leaders,
        });
        self.biotic_specialist(allies - tech);
    }

    /// Selects a biotic specialist.
    fn biotic_specialist(&mut self, allies: AllySet) {
        for biotic in allies & AllySet::BIOTICS {
            self.choices.biotic_specialist = Some(biotic);
            self.second_leader(allies);
        }
    }

    /// Selects a leader for the second fireteam.
    fn second_leader(&mut self, allies: AllySet) {
        let selectable_allies = allies - self.choices.biotic_specialist.unwrap();
        for leader in selectable_allies {
            self.choices.second_leader = Some(leader);
            self.crew_escort(allies);
        }
    }

    /// Optionally selects an available [`Ally`] to escort the crew back to _The Normandy_, if
    /// possible.
    fn crew_escort(&mut self, allies: AllySet) {
        self.choices.crew_escort = None;
        self.the_long_walk(allies);

        // The option to escort the crew is only available if more than four—the minimum
        // possible—allies remain at this point.
        if allies.len() > 4 {
            let selectable_allies = (allies & AllySet::ESCORTS)
                - self.choices.biotic_specialist.unwrap()
                - self.choices.second_leader.unwrap();
            for escort in selectable_allies {
                self.choices.crew_escort = Some(escort);
                // If the escort is not loyal, they will die.
                let disloyal_escort = !self.loyal() & escort;
                self.the_long_walk(allies - disloyal_escort);
            }
        }
    }

    /// If the selected biotic specialist is not loyal or ideal, selects allies for the squad
    /// Shepard brings for _The Long Walk_.
    fn the_long_walk(&mut self, allies: AllySet) {
        self.choices.the_long_walk = SquadSelection::new();

        // If the biotic specialist is loyal and ideal, no one on your squad will die.
        let biotic = self.choices.biotic_specialist.unwrap();
        if (self.loyal() & AllySet::IDEAL_BIOTICS).contains(biotic) {
            self.final_squad(allies);
            return;
        }

        // The biotic specialist, escort (if selected), and second fireteam leader cannot be
        // selected.
        let escort = AllySet::from(self.choices.crew_escort);
        let leader = self.choices.second_leader.unwrap();
        let mut potential_victims = allies - biotic - escort - leader;

        // If too few allies remain to merit a meaningful selection, omit the decision.
        if potential_victims.len() <= 2 {
            let victim = DeathReason::BadBiotic.get_victim(potential_victims);
            self.final_squad(allies - victim);
            return;
        }

        // Otherwise, the victim depends on who is selected for Shepard's squad.
        while potential_victims.len() > 1 {
            let victim = DeathReason::BadBiotic.get_victim(potential_victims);
            self.choices.the_long_walk.add_victim(victim);
            self.final_squad(allies - victim);
            potential_victims -= victim;
        }
    }

    /// Selects allies for the squad Shepard brings to the final battle.
    fn final_squad(&mut self, allies: AllySet) {
        // The crew escort is not active.
        let escort = AllySet::from(self.choices.crew_escort);
        let active_allies = allies - escort;

        // Although the second fireteam leader was selected earlier, their survival can only be
        // determined at this point because they will not die if there are fewer than four
        // available allies, regardless of their loyalty or suitedness to the role.
        let leader = self.choices.second_leader.unwrap();
        let leader_survives = active_allies.len() < 4
            || AllySet::IMMORTAL_LEADERS.contains(leader)
            || (AllySet::IDEAL_LEADERS & self.loyal()).contains(leader);
        let victim = AllySet::from((!leader_survives).then_some(leader));
        let allies = allies - victim;
        let active_allies = active_allies - victim;

        for squad in active_allies
            .iter()
            .combinations(2)
            .map(|combo| combo.into_iter().collect::<AllySet>())
        {
            self.choices.final_squad = squad;
            let defenders = active_allies - squad;
            let victims =
                death::get_defense_victims(defenders, self.loyal()) | (squad - self.loyal());
            self.record_outcome(allies - victims);
        }
    }

    /// Records the final outcome based on the complete decision path and surviving allies.
    fn record_outcome(&mut self, survivors: AllySet) {
        let outcome = Outcome {
            survivors,
            // Loyal allies who are dead do not contribute to a different outcome.
            loyal: survivors & self.loyal(),
            rescued_crew: self.choices.crew_escort.is_some(),
        };
        self.outcomes
            .entry(outcome)
            .and_modify(|metadata| metadata.count += 1)
            .or_insert_with(|| DecisionPathMetadata {
                count: 1,
                example: self.choices.complete(),
            });
    }
}

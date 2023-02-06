//! Decision-related types

use std::fmt::Display;

use serde::{Deserialize, Serialize};

use crate::ally::{Ally, AllySet};

/// Squad selection
///
/// # Context
///
/// There are precisely two contexts in which this type is used:
///
/// 1. The cargo bay squad selection can cause allies to survive that would otherwise die due to
///    not upgrading _The Normandy_'s shields. The survivors must be in Shepard's squad, and the
///    victim must **not** be in the squad.
/// 2. _The Long Walk_ sub-mission's squad selection can cause allies to die that would otherwise
///    have survived if a loyal, ideal biotic specialist had been chosen. The victim must be in
///    Shepard's squad, and the survivors must **not** be in the squad.
#[derive(Clone, Copy, Debug, Default, Deserialize, Serialize)]
pub struct SquadSelection {
    survivors: AllySet,
    victim: Option<Ally>,
}

impl SquadSelection {
    /// Creates an empty [`SquadSelection`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds the given [`Ally`] as the selected victim.
    ///
    /// Any current victim becomes a survivor.
    pub fn add_victim(&mut self, ally: Ally) {
        if let Some(victim) = self.victim {
            self.survivors |= victim;
        }
        self.victim = Some(ally);
    }

    /// Retrieves the allies who survive based on how the squad is selected. See
    /// [Context](#context).
    pub fn survivors(&self) -> AllySet {
        self.survivors
    }

    /// Retrieves the victim based on how the squad is selected. See [Context](#context).
    pub fn victim(&self) -> Option<Ally> {
        self.victim
    }
}

/// Selection parameters for the leader of the first fireteam
///
/// If an ideal tech specialist is selected, the leader of the first fireteam affects whether the
/// tech specialist will survive. If they are ideal (`is_ideal == true`), then the tech specialist
/// will survive. The available ideal leaders at the time this decision is made must be recorded
/// in `ideal_leaders` so that it is clear in the description of this decision who should be
/// selected. If they are _not_ ideal, the tech specialist will die, which means an available ally
/// that is _not_ an ideal leader should be selected.
#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
pub struct FirstLeader {
    /// Was an ideal leader selected?
    pub is_ideal: bool,
    /// Which available allies are ideal leaders?
    pub ideal_leaders: AllySet,
}

/// Complete record of choices for a playthrough of the final mission in _Mass Effect 2_
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct DecisionPath {
    /// Optional allies recruited before the start of the final mission
    pub recruitment: AllySet,
    /// Allies for whom loyalty missions were completed
    pub loyalty_missions: AllySet,
    /// Was _The Normandy_'s _Silaris Armor_ upgrade purchased?
    pub upgraded_armor: bool,
    /// Was _The Normandy_'s _Cyclonic Shields_ upgrade purchased?
    pub upgraded_shield: bool,
    /// Allies selected for Shepard's squad to defend _The Normandy_'s cargo bay
    pub cargo_bay_squad: SquadSelection,
    /// Was _The Normandy_'s _Thanix Cannon_ upgrade purchased?
    pub upgraded_weapon: bool,
    /// [`Ally`] selected as the tech specialist
    pub tech_specialist: Ally,
    /// See [`FirstLeader`].
    pub first_leader: Option<FirstLeader>,
    /// [`Ally`] selected as the biotic specialist
    pub biotic_specialist: Ally,
    /// [`Ally`] selected to lead the second fireteam
    pub second_leader: Ally,
    /// [`Ally`] optionally selected to escort the crew back to _The Normandy_
    pub crew_escort: Option<Ally>,
    /// Allies _not_ selected for Shepard's squad for _The Long Walk_
    pub the_long_walk: SquadSelection,
    /// Allies selected for Shepard's squad for the final battle
    pub final_squad: AllySet,
}

impl Display for DecisionPath {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.upgraded_armor {
            writeln!(f, "Purchase the Silaris Armor upgrade.")?;
        }

        if self.upgraded_shield {
            writeln!(f, "Purchase the Cyclonic Shields upgrade.")?;
        }

        if self.upgraded_weapon {
            writeln!(f, "Purchase the Thanix Cannon upgrade.")?;
        }

        writeln!(f, "Recruit {}.", self.recruitment)?;

        // Perform a small adjustment on loyalty missions for readability.
        let loyalty_mission_allies = match self.loyalty_missions == !Ally::Morinth {
            true => AllySet::EVERYONE,
            false => self.loyalty_missions,
        };
        writeln!(f, "Complete loyalty missions for {loyalty_mission_allies}.")?;

        if loyalty_mission_allies.contains(Ally::Samara) {
            // Note: If `asari` contains more than one `Ally`, this `DecisionPath` is malformed.
            let asari = self.recruitment & AllySet::ASARI;
            writeln!(
                f,
                "- Choose {asari} at the end of Samara's loyalty mission."
            )?;
        }

        if let Some(victim) = self.cargo_bay_squad.victim() {
            let survivors = self.cargo_bay_squad.survivors();
            write!(f, "For the cargo bay squad, ")?;
            if !survivors.is_empty() {
                write!(f, "pick {survivors}")?;
                if survivors.len() == 1 {
                    write!(f, " and ")?;
                }
            }
            if survivors.len() < 2 {
                write!(f, "leave {victim} behind")?;
            }
            writeln!(f, ".")?;
        }

        writeln!(f, "Choose {} as the tech specialist.", self.tech_specialist)?;

        if let Some(first_leader) = self.first_leader {
            writeln!(
                f,
                "Choose {}{} to lead the second fireteam.",
                (!first_leader.is_ideal)
                    .then_some("anyone except ")
                    .unwrap_or_default(),
                first_leader.ideal_leaders.to_string_with_conjunction("or")
            )?;
        } else {
            writeln!(f, "The second fireteam leader does not matter.")?;
        }

        writeln!(
            f,
            "Choose {} as the biotic specialist.",
            self.biotic_specialist
        )?;

        writeln!(
            f,
            "Choose {} to lead the diversion team.",
            self.second_leader
        )?;

        match self.crew_escort {
            Some(escort) => writeln!(f, "Send {escort} to escort the crew.")?,
            None => writeln!(f, "Do not send anyone to escort the crew.")?,
        }

        if let Some(victim) = self.the_long_walk.victim() {
            let survivors = self.the_long_walk.survivors();
            write!(f, "For the squad in the biotic shield, pick {victim}")?;
            if !survivors.is_empty() {
                write!(f, " and leave {survivors} behind")?;
            }
            writeln!(f, ".")?;
        }

        writeln!(f, "For the final squad, pick {}.", self.final_squad)
    }
}

#[cfg(feature = "generate")]
pub(crate) use generate::DecisionPathLedger;

#[cfg(feature = "generate")]
mod generate {
    use super::*;

    /// This struct serves as a running ledger of a [`DecisionPath`]. All fields whose types do not
    /// implement [`Default`] are wrapped in an [`Option`].
    #[derive(Clone, Default)]
    pub struct DecisionPathLedger {
        pub recruitment: AllySet,
        pub loyalty_missions: AllySet,
        pub upgraded_armor: bool,
        pub upgraded_shield: bool,
        pub cargo_bay_squad: SquadSelection,
        pub upgraded_weapon: bool,
        pub tech_specialist: Option<Ally>,
        pub first_leader: Option<FirstLeader>,
        pub biotic_specialist: Option<Ally>,
        pub second_leader: Option<Ally>,
        pub crew_escort: Option<Ally>,
        pub the_long_walk: SquadSelection,
        pub final_squad: AllySet,
    }

    impl DecisionPathLedger {
        /// Copies all fields into a [`DecisionPath`] object.
        ///
        /// # Panics
        ///
        /// This method panics if any of the following fields are [`None`]:
        ///
        /// - `tech_specialist`
        /// - `biotic_specialist`
        /// - `second_leader`
        pub fn complete(&self) -> DecisionPath {
            DecisionPath {
                recruitment: self.recruitment,
                loyalty_missions: self.loyalty_missions,
                upgraded_armor: self.upgraded_armor,
                upgraded_shield: self.upgraded_shield,
                cargo_bay_squad: self.cargo_bay_squad,
                upgraded_weapon: self.upgraded_weapon,
                tech_specialist: self.tech_specialist.expect("tech specialist was selected"),
                first_leader: self.first_leader,
                biotic_specialist: self
                    .biotic_specialist
                    .expect("biotic specialist was selected"),
                second_leader: self.second_leader.expect("second leader was selected"),
                crew_escort: self.crew_escort,
                the_long_walk: self.the_long_walk,
                final_squad: self.final_squad,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn squad() {
        let mut squad = SquadSelection::new();
        assert_eq!(squad.survivors(), AllySet::NOBODY);
        assert_eq!(squad.victim(), None);

        squad.add_victim(Ally::Jack);
        assert_eq!(squad.survivors(), AllySet::NOBODY);
        assert_eq!(squad.victim().unwrap(), Ally::Jack);

        squad.add_victim(Ally::Miranda);
        assert_eq!(squad.survivors(), Ally::Jack.into());
        assert_eq!(squad.victim().unwrap(), Ally::Miranda);

        squad.add_victim(Ally::Legion);
        assert_eq!(squad.survivors(), Ally::Jack | Ally::Miranda);
        assert_eq!(squad.victim().unwrap(), Ally::Legion);

        squad.add_victim(Ally::Thane);
        assert_eq!(squad.survivors(), Ally::Jack | Ally::Miranda | Ally::Legion);
        assert_eq!(squad.victim().unwrap(), Ally::Thane);
    }
}

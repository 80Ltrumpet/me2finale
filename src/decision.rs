//! Decision-related types

use std::fmt::Display;

use serde::{Deserialize, Serialize};

use crate::ally::Ally;
use crate::allyset::AllySet;

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
///
/// See the [`add_victim`](#method.add_victim) method for further explanation and a realistic
/// example of how this type is used.
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
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// use me2finale::decision::SquadSelection;
    ///
    /// let mut selection = SquadSelection::new();
    ///
    /// // Suppose we are selecting the cargo bay squad and know that Kasumi will die if we do not
    /// // select her. This means she is the first victim.
    /// selection.add_victim(Kasumi);
    ///
    /// // If we *do* select Kasumi, however, then someone else *must* die instead. Suppose the
    /// // next victim is Legion.
    /// selection.add_victim(Legion);
    ///
    /// // Querying the selection at this point indicates that Kasumi will survive if we select her
    /// // for the cargo bay squad, but we must *not* select Legion in order for them to die.
    /// assert!(selection.survivors().contains(Kasumi));
    /// assert_eq!(selection.victim(), Some(Legion));
    /// ```
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
    /// Which loyal, ideal leaders were available to lead the second fireteam? If the choice does
    /// not matter, this field is empty.
    pub ideal_second_fireteam_leaders: AllySet,
    /// Was a loyal, ideal leader selected for the second fireteam?
    pub second_fireteam_leader_is_ideal: bool,
    /// [`Ally`] selected as the biotic specialist
    pub biotic_specialist: Ally,
    /// [`Ally`] selected to lead the diversion team
    pub diversion_team_leader: Ally,
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
            let possessive = if asari.contains(Ally::Samara) {
                "her"
            } else {
                "Samara's"
            };
            writeln!(
                f,
                "- Choose {asari} at the end of {possessive} loyalty mission."
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

        if self.ideal_second_fireteam_leaders.is_empty() {
            writeln!(f, "The second fireteam leader does not matter.")?;
        } else {
            let modifier = (!self.second_fireteam_leader_is_ideal)
                .then_some("anyone except ")
                .unwrap_or_default();
            let ideal_leaders = self
                .ideal_second_fireteam_leaders
                .to_string_with_conjunction("or");
            writeln!(
                f,
                "Choose {modifier}{ideal_leaders} to lead the second fireteam."
            )?;
        }

        writeln!(
            f,
            "Choose {} as the biotic specialist.",
            self.biotic_specialist
        )?;

        writeln!(
            f,
            "Choose {} to lead the diversion team.",
            self.diversion_team_leader
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

#[cfg(test)]
mod tests {
    use super::*;
    use Ally::*;

    #[test]
    fn squad() {
        let mut squad = SquadSelection::new();
        assert_eq!(squad.survivors(), AllySet::NOBODY);
        assert_eq!(squad.victim(), None);

        squad.add_victim(Jack);
        assert_eq!(squad.survivors(), AllySet::NOBODY);
        assert_eq!(squad.victim(), Some(Jack));

        squad.add_victim(Miranda);
        assert_eq!(squad.survivors(), Jack.into());
        assert_eq!(squad.victim(), Some(Miranda));

        squad.add_victim(Legion);
        assert_eq!(squad.survivors(), Jack | Miranda);
        assert_eq!(squad.victim(), Some(Legion));

        squad.add_victim(Thane);
        assert_eq!(squad.survivors(), Jack | Miranda | Legion);
        assert_eq!(squad.victim(), Some(Thane));
    }
}

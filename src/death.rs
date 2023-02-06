//! Victim determination rules
//!
//! At certain points in the final mission of _Mass Effect 2_, if certain conditions are met, one
//! or more allies will die. This module enumerates the reasons for which allies may die and
//! codifies the rules by which victims are selected.

use crate::ally::{Ally, AllySet};

/// Enumeration of conditions leading to the death of an ally
#[derive(Debug)]
pub(crate) enum DeathReason {
    /// The _Silaris Armor_ upgrade was not purchased.
    NoArmorUpgrade,
    /// The _Cyclonic Shields_ upgrade was not purchased.
    NoShieldUpgrade,
    /// The _Thanix Cannon_ upgrade was not purchased.
    NoWeaponUpgrade,
    /// A disloyal or non-ideal biotic was chosen as the biotic specialist.
    BadBiotic,
}

impl DeathReason {
    /// Selects the [`Ally`] from the given [`AllySet`] who should die according to this reason.
    ///
    /// # Panics
    ///
    /// This method panics if none of the `allies` are in this reason's victim priority. Such a
    /// condition indicates a bug in the caller.
    pub(crate) fn get_victim(&self, allies: AllySet) -> Ally {
        match self
            .victim_priority()
            .iter()
            .copied()
            .find(|&ally| allies.contains(ally))
        {
            Some(victim) => victim,
            None => panic!("no victim in {allies:?} for {self:?}"),
        }
    }

    /// Returns a slice of [`Ally`] values specifying the order in which victims should be selected.
    fn victim_priority(&self) -> &'static [Ally] {
        match self {
            Self::NoArmorUpgrade => &[Ally::Jack],
            Self::NoShieldUpgrade => &[
                Ally::Kasumi,
                Ally::Legion,
                Ally::Tali,
                Ally::Thane,
                Ally::Garrus,
                Ally::Zaeed,
                Ally::Grunt,
                Ally::Samara,
                Ally::Morinth,
            ],
            Self::NoWeaponUpgrade => &[
                Ally::Thane,
                Ally::Garrus,
                Ally::Zaeed,
                Ally::Grunt,
                Ally::Jack,
                Ally::Samara,
                Ally::Morinth,
            ],
            Self::BadBiotic => &[
                Ally::Thane,
                Ally::Jack,
                Ally::Garrus,
                Ally::Legion,
                Ally::Grunt,
                Ally::Samara,
                Ally::Jacob,
                Ally::Mordin,
                Ally::Tali,
                Ally::Kasumi,
                Ally::Zaeed,
                Ally::Morinth,
            ],
        }
    }
}

/// Selects defending allies who should die.
///
/// Disloyal `defenders` are prioritized as victims over `loyal` ones, hence the additional
/// parameter.
///
/// # Panics
///
/// This function panics if `defenders` is empty. It is not possible to enter the final battle
/// without at least three surviving allies.
pub(crate) fn get_defense_victims(defenders: AllySet, loyal: AllySet) -> AllySet {
    let toll = defense_toll(defenders, loyal);
    let disloyal = defenders - loyal;
    let disloyal_victims = DEFENSE_VICTIM_PRIORITY
        .iter()
        .copied()
        .filter(|&ally| disloyal.contains(ally));
    let loyal = defenders & loyal;
    let loyal_victims = DEFENSE_VICTIM_PRIORITY
        .iter()
        .copied()
        .filter(|&ally| loyal.contains(ally));
    disloyal_victims.chain(loyal_victims).take(toll).collect()
}

/// Victim priority for defending allies in the final battle
const DEFENSE_VICTIM_PRIORITY: &[Ally] = &[
    Ally::Mordin,
    Ally::Tali,
    Ally::Kasumi,
    Ally::Jack,
    Ally::Miranda,
    Ally::Jacob,
    Ally::Garrus,
    Ally::Samara,
    Ally::Morinth,
    Ally::Legion,
    Ally::Thane,
    Ally::Zaeed,
    Ally::Grunt,
];

/// Computes the relative _defensiveness_ of an [`Ally`] based on their loyalty.
fn defense_score(ally: Ally, loyal: AllySet) -> u8 {
    use Ally::*;
    let base_score = match ally {
        Garrus | Grunt | Zaeed => 4,
        Jacob | Legion | Miranda | Morinth | Samara | Thane => 2,
        Jack | Kasumi | Mordin | Tali => 1,
    };
    // If the ally is not loyal, their defense score is reduced by 1.
    let penalty: u8 = (!loyal.contains(ally)).into();
    base_score - penalty
}

/// Computes the number of `defenders` who will die, depending on who is `loyal`.
///
/// # Panics
///
/// This function panics if `defenders` is empty. It is not possible to enter the final battle
/// without at least three surviving allies.
fn defense_toll(defenders: AllySet, loyal: AllySet) -> usize {
    if defenders.is_empty() {
        panic!("zero defenders");
    }
    let defender_count = defenders.len();
    let score = defenders
        .iter()
        .map(|ally| defense_score(ally, loyal))
        .sum::<u8>() as f32
        / defender_count as f32;
    match defender_count {
        0 => unreachable!(),
        1 => (score < 2.).into(),
        2 => {
            if score == 0. {
                2
            } else {
                (score < 2.).into()
            }
        }
        3 => {
            if score == 0. {
                3
            } else if score < 1. {
                2
            } else {
                (score < 2.).into()
            }
        }
        4 => {
            if score == 0. {
                4
            } else if score < 0.5 {
                3
            } else if score <= 1. {
                2
            } else {
                (score < 2.).into()
            }
        }
        _ => {
            if score < 0.5 {
                3
            } else if score < 1.5 {
                2
            } else {
                (score < 2.).into()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Ally::*;

    #[test]
    fn get_victim() {
        // Jack is the only possible victim if the armor was not upgraded.
        assert_eq!(
            Jack,
            DeathReason::NoArmorUpgrade.get_victim(AllySet::REQUIRED)
        );

        let mut allies = Kasumi | Tali | Zaeed;
        assert_eq!(Kasumi, DeathReason::NoShieldUpgrade.get_victim(allies));
        allies -= Kasumi;
        assert_eq!(Tali, DeathReason::NoShieldUpgrade.get_victim(allies));
        allies -= Tali;
        assert_eq!(Zaeed, DeathReason::NoShieldUpgrade.get_victim(allies));
    }

    #[test]
    #[should_panic = "no victim in AllySet(0x0214) for NoWeaponUpgrade"]
    fn get_victim_panic() {
        let _victim = DeathReason::NoWeaponUpgrade.get_victim(Tali | Mordin | Miranda);
    }

    #[test]
    fn defense_victims() {
        let defenders = Garrus | Jack | Morinth | Thane;
        let loyal = defenders - (Garrus | Thane);
        let victims = get_defense_victims(defenders, loyal);
        assert_eq!(AllySet::from(Garrus), victims);

        let defenders = Jacob | Grunt | Mordin | Legion | Kasumi;
        let victims = get_defense_victims(defenders, defenders);
        assert_eq!(AllySet::NOBODY, victims);
    }
}

//! Ally enumeration

use std::fmt::Display;

use serde::{Deserialize, Serialize};

/// Enumeration of all allies in _Mass Effect 2_
///
/// In the context of this crate, an _ally_ is a character who can take part in missions with
/// Commander Shepard.
///
/// For examples of how this enum is used, see [`AllySet`][crate::allyset::AllySet].
#[allow(missing_docs)]
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[must_use]
#[repr(u8)]
pub enum Ally {
    // Required
    // Garrus, Jacob, and Miranda—the ideal leaders—are grouped together for potential optimization.
    Garrus,
    Jacob,
    Miranda,
    Jack,
    Mordin,

    // Optional
    Grunt,
    Kasumi,
    Legion,
    Samara,
    Tali,
    Thane,
    Zaeed,
    // Morinth is last to optimize potential bit packing.
    Morinth,
}

impl Ally {
    /// Returns the name of this [`Ally`] as a static string slice.
    ///
    /// # Example
    ///
    /// ```
    /// # use me2finale::ally::Ally;
    /// assert_eq!(Ally::Miranda.name(), "Miranda");
    /// ```
    pub const fn name(self) -> &'static str {
        match self {
            Self::Garrus => "Garrus",
            Self::Grunt => "Grunt",
            Self::Jack => "Jack",
            Self::Jacob => "Jacob",
            Self::Kasumi => "Kasumi",
            Self::Legion => "Legion",
            Self::Miranda => "Miranda",
            Self::Mordin => "Mordin",
            Self::Morinth => "Morinth",
            Self::Samara => "Samara",
            Self::Tali => "Tali",
            Self::Thane => "Thane",
            Self::Zaeed => "Zaeed",
        }
    }

    /// Converts this [`Ally`] to its bit mask representation.
    ///
    /// This is used to optimize the implementation of [`AllySet`][crate::allyset::AllySet].
    pub(crate) const fn to_bit_mask(self) -> u16 {
        1 << self as u16
    }
}

impl Display for Ally {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

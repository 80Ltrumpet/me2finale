//! Ally enumeration, collection, iteration, and display

use std::cmp::{Ordering, PartialOrd};
use std::fmt::{Debug, Display};
use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub, SubAssign,
};

use serde::{Deserialize, Serialize};

/// Enumeration of all allies in _Mass Effect 2_
#[allow(missing_docs)]
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[must_use]
#[repr(u8)]
pub enum Ally {
    // Required
    // Group Garrus, Jacob, and Miranda—the ideal leaders—together for potential optimization.
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
    /// Returns the name of this [`Ally`] as a string slice.
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
    /// The bit mask is used to optimize the implementation of [`AllySet`].
    const fn to_bit_mask(self) -> u16 {
        1 << self as u16
    }
}

impl Display for Ally {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl<T: Into<AllySet>> BitOr<T> for Ally {
    type Output = AllySet;
    /// Computes the union of this [`Ally`] and an [`AllySet`].
    ///
    /// This allows [`AllySet`]s to be more concisely constructed from individual allies.
    ///
    /// # Example
    ///
    /// ```
    /// # use me2finale::ally::{Ally, AllySet};
    /// let short = Ally::Thane | Ally::Mordin;
    /// let long = AllySet::new([Ally::Thane, Ally::Mordin]);
    /// assert_eq!(short, long);
    /// ```
    fn bitor(self, rhs: T) -> AllySet {
        AllySet(self.to_bit_mask() | rhs.into().0)
    }
}

impl Not for Ally {
    type Output = AllySet;
    /// Creates an [`AllySet`] containing everyone _except_ this [`Ally`].
    fn not(self) -> AllySet {
        AllySet(AllySet::EVERYONE_BITS & !self.to_bit_mask())
    }
}

/// Set-like type optimized for [`Ally`]
///
/// Set-wise operations are implemented as operators (see [Trait Implementations]).
///
/// [Trait Implementations]: #trait-implementations
#[derive(Clone, Copy, Default, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[must_use]
pub struct AllySet(u16);

/// Convenience macro for generating the internal representations of [`AllySet`]s
macro_rules! ally_bits {
    ($($ally:ident),+) => {
        $(Ally::$ally.to_bit_mask()) | +
    };
}

impl AllySet {
    // Bitwise sets
    const EVERYONE_BITS: u16 = (ally_bits!(Morinth) << 1) - 1;
    const IDEAL_BIOTICS_BITS: u16 = ally_bits!(Jack, Samara, Morinth);
    const IDEAL_TECHS_BITS: u16 = ally_bits!(Kasumi, Legion, Tali);
    const OPTIONAL_BITS: u16 = Self::EVERYONE_BITS & !Self::REQUIRED_BITS;
    const REQUIRED_BITS: u16 = ally_bits!(Garrus, Jack, Jacob, Miranda, Mordin);

    /// The empty set of allies
    pub const NOBODY: Self = Self(0);

    /// The comprehensive set of allies
    pub const EVERYONE: Self = Self(Self::EVERYONE_BITS);

    /// The set of allies that are required to begin the final mission
    pub const REQUIRED: Self = Self(Self::REQUIRED_BITS);

    /// The set of allies from whom at least three must be recruited—in addition to the required
    /// allies—to begin the final mission
    pub const OPTIONAL: Self = Self(Self::OPTIONAL_BITS);

    /// The set of _directly_ recruitable, optional allies
    ///
    /// This set excludes Morinth, since she can only be recruited by replacing Samara, who is
    /// optional.
    pub const RECRUITABLE: Self = Self(Self::OPTIONAL_BITS & !ally_bits!(Morinth));

    /// The set of allies who are Asari
    ///
    /// The practical necessity of this constant is for replacing Samara with Morinth at the end
    /// of Samara's loyalty mission.
    pub const ASARI: Self = Self(ally_bits!(Morinth, Samara));

    /// The set of allies who are ideal leaders
    ///
    /// - If any of these allies are loyal and selected as the leader of the second fireteam, the
    ///   death of the selected tech specialist may be avoided.
    /// - If any of these allies are loyal and selected as the leader of the diversion team, their
    ///   death will be avoided.
    /// - If there are only three allies remaining at the end of _The Long Walk_, the diversion
    ///   team leader will always survive.
    ///
    /// > There is no limitation on who can be selected as a leader, as opposed to the tech and
    /// > biotic specialists.
    pub const IDEAL_LEADERS: Self = Self(ally_bits!(Garrus, Jacob, Miranda));

    /// The set of allies who are ideal tech specialists
    ///
    /// If any of these allies are loyal and selected as the tech specialist, their death will be
    /// avoided as long as a loyal, ideal leader is selected for the first fireteam.
    pub const IDEAL_TECHS: Self = Self(Self::IDEAL_TECHS_BITS);

    /// The set of allies who are ideal biotic specialists
    ///
    /// If any of these allies are loyal and selected as the biotic specialist, the death of an
    /// ally will be avoided.
    pub const IDEAL_BIOTICS: Self = Self(Self::IDEAL_BIOTICS_BITS);

    /// The set of allies who may be selected as the tech specialist
    pub const TECHS: Self = Self(Self::IDEAL_TECHS_BITS | ally_bits!(Garrus, Jacob, Mordin, Thane));

    /// The set of allies who may be selected as the biotic specialist
    pub const BIOTICS: Self = Self(Self::IDEAL_BIOTICS_BITS | ally_bits!(Jacob, Miranda, Thane));

    /// The set of allies who may be selected to escort the crew back to _The Normandy_
    ///
    /// Only Miranda may _not_ be selected for this role.
    pub const ESCORTS: Self = Self(Self::EVERYONE_BITS & !ally_bits!(Miranda));

    /// The set of allies who cannot die when selected as the leader of the second fireteam,
    /// regardless of loyalty
    pub const IMMORTAL_LEADERS: Self = Self(ally_bits!(Miranda));

    /// Creates a new [`AllySet`] with the given allies.
    ///
    /// # Example
    ///
    /// ```
    /// # use me2finale::ally::{Ally, AllySet};
    /// let allies = AllySet::new([Ally::Mordin, Ally::Kasumi, Ally::Grunt]);
    /// assert_eq!(allies, Ally::Mordin | Ally::Kasumi | Ally::Grunt);
    /// ```
    pub fn new<T: IntoIterator<Item = Ally>>(allies: T) -> Self {
        allies.into_iter().fold(Self::NOBODY, BitOr::bitor)
    }

    /// Returns `true` if the given [`Ally`] is a member of this set.
    pub const fn contains(self, ally: Ally) -> bool {
        self.0 & ally.to_bit_mask() != 0
    }

    /// Returns `true` if this set contains no allies.
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Returns an iterator over the allies contained in this set.
    ///
    /// Items are yielded in alphabetical order (see [`AllySetIter`]).
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// let mut ally_iter = (Kasumi | Morinth | Jacob).iter();
    /// assert_eq!(ally_iter.next(), Some(Jacob));
    /// assert_eq!(ally_iter.next(), Some(Kasumi));
    /// assert_eq!(ally_iter.next(), Some(Morinth));
    /// assert_eq!(ally_iter.next(), None);
    /// ```
    pub fn iter(self) -> AllySetIter {
        AllySetIter::new(self)
    }

    /// Counts the number of allies contained in this set.
    pub const fn len(self) -> usize {
        self.0.count_ones() as usize
    }

    /// Generates a display-ready string of this set of allies with the specified conjunction, if
    /// applicable.
    ///
    /// The result is always in alphabetical order.
    ///
    /// # Examples
    ///
    /// ```
    /// use me2finale::ally::{Ally::*, AllySet};
    ///
    /// assert_eq!(
    ///     (Tali | Samara | Miranda).to_string_with_conjunction("or"),
    ///     "Miranda, Samara, or Tali"
    /// );
    ///
    /// // The `ToString` implementation calls this method with "and".
    /// assert_eq!((Jacob | Garrus).to_string(), "Garrus and Jacob");
    ///
    /// // If the set only contains one ally, zero allies, all allies, or all allies minus one, the
    /// // conjunction is not used.
    /// assert_eq!(AllySet::from(Mordin).to_string_with_conjunction("foo"), "Mordin");
    /// assert_eq!(AllySet::NOBODY.to_string_with_conjunction("bar"), "nobody");
    /// assert_eq!(AllySet::EVERYONE.to_string_with_conjunction("derp"), "everyone");
    /// assert_eq!((!Jack).to_string_with_conjunction("squee"), "everyone except Jack");
    /// ```
    pub fn to_string_with_conjunction(&self, conjunction: &str) -> String {
        let mut ally_names = self.iter().map(Ally::name);
        match self.len() {
            0 => "nobody".to_string(),
            1 => ally_names.next().unwrap().to_string(),
            2 => {
                let first = ally_names.next().unwrap();
                let second = ally_names.next().unwrap();
                format!("{first} {conjunction} {second}")
            }
            len => {
                if len == Self::EVERYONE.len() {
                    "everyone".to_string()
                } else if len == Self::EVERYONE.len() - 1 {
                    // This probably looks silly, but in practice at least one ally will be missing
                    // from the set. In particular, Morinth and Samara are mutually exclusive, so
                    // this conversion is more readable than a list of twelve names.
                    let excluded_name = (!*self).iter().next().unwrap().name();
                    format!("everyone except {excluded_name}")
                } else {
                    let ally_names = ally_names.map(str::to_string).collect::<Vec<_>>();
                    let comma_separated_list = ally_names[..len - 1].join(", ");
                    let last = ally_names.last().unwrap();
                    // If you think this comma is wrong, **you** are wrong.
                    format!("{comma_separated_list}, {conjunction} {last}")
                }
            }
        }
    }
}

impl Debug for AllySet {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_tuple("AllySet")
            .field(&format_args!("{:#06x}", self.0))
            .finish()
    }
}

impl Display for AllySet {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.to_string_with_conjunction("and"))
    }
}

impl FromIterator<Ally> for AllySet {
    /// Creates a new [`AllySet`] from the allies yielded by the given iterable.
    ///
    /// # Example
    ///
    /// ```
    /// # use me2finale::ally::{Ally, AllySet};
    /// let allies = [Ally::Tali, Ally::Legion].into_iter().collect::<AllySet>();
    /// assert_eq!(allies, Ally::Legion | Ally::Tali);
    /// ```
    fn from_iter<T: IntoIterator<Item = Ally>>(allies: T) -> Self {
        Self::new(allies)
    }
}

impl IntoIterator for AllySet {
    type IntoIter = AllySetIter;
    type Item = Ally;
    /// Creates an iterator over the allies contained in this set.
    fn into_iter(self) -> AllySetIter {
        self.iter()
    }
}

impl PartialOrd for AllySet {
    /// Determines the subset/superset relationship between two [`AllySet`]s.
    ///
    /// # Examples
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// let a = Garrus | Tali | Samara;
    /// let b = Tali | Samara;
    /// let c = Kasumi | Garrus | Morinth;
    /// // `a` is a strict superset of `b`.
    /// assert!(a > b);
    /// // `a` is a superset of `b`.
    /// assert!(a >= b);
    /// // `b` is a subset of `a`.
    /// assert!(b <= a);
    /// // `b` is a strict subset of `a`.
    /// assert!(b < a);
    /// // `a` is neither a subset nor a superset of `c`.
    /// assert!(!(a <= c || a >= c));
    /// // `c` is a subset and a superset of itself.
    /// assert!(c <= c && c >= c);
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let common = *self & *other;
        let ordering = self.len().cmp(&other.len());
        match ordering {
            Ordering::Equal | Ordering::Less => (*self == common).then_some(ordering),
            Ordering::Greater => (*other == common).then_some(ordering),
        }
    }
}

impl From<Ally> for AllySet {
    /// Converts to an [`AllySet`] from an [`Ally`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use me2finale::ally::{Ally, AllySet};
    /// assert!(AllySet::from(Ally::Grunt).contains(Ally::Grunt));
    /// assert!(!AllySet::from(Ally::Mordin).contains(Ally::Morinth));
    /// ```
    fn from(ally: Ally) -> Self {
        Self(ally.to_bit_mask())
    }
}

impl From<Option<Ally>> for AllySet {
    /// Converts to an [`AllySet`] from an [`Option`] that may contain an [`Ally`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use me2finale::ally::{Ally, AllySet};
    /// let mut maybe_ally = Some(Ally::Zaeed);
    /// assert_eq!(AllySet::from(maybe_ally), Ally::Zaeed.into());
    /// maybe_ally = None;
    /// assert_eq!(AllySet::from(maybe_ally), AllySet::NOBODY);
    /// ```
    fn from(optional_ally: Option<Ally>) -> Self {
        Self(optional_ally.map_or(0, Ally::to_bit_mask))
    }
}

impl<T: Into<AllySet>> BitAnd<T> for AllySet {
    type Output = Self;
    /// Computes the intersection of two [`AllySet`]s.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// let intersection = (Jack | Garrus | Samara) & (Zaeed | Jack);
    /// assert_eq!(intersection, Jack.into());
    /// ```
    fn bitand(self, rhs: T) -> Self {
        Self(self.0 & rhs.into().0)
    }
}

impl<T: Into<AllySet>> BitAndAssign<T> for AllySet {
    /// Replaces this set with its common elements within another [`AllySet`].
    fn bitand_assign(&mut self, rhs: T) {
        self.0 &= rhs.into().0;
    }
}

impl<T: Into<AllySet>> BitOr<T> for AllySet {
    type Output = Self;
    /// Computes the union of two [`AllySet`]s.
    ///
    /// # Example
    ///
    /// ```
    /// # use me2finale::ally::{Ally, AllySet};
    /// let cerberus = Ally::Jacob | Ally::Miranda;
    /// let old_pals = Ally::Garrus | Ally::Tali;
    /// let awkward = cerberus | old_pals;
    /// assert_eq!(awkward, Ally::Jacob | Ally::Miranda | Ally::Garrus | Ally::Tali);
    /// ```
    fn bitor(self, rhs: T) -> Self {
        Self(self.0 | rhs.into().0)
    }
}

impl<T: Into<AllySet>> BitOrAssign<T> for AllySet {
    /// Inserts all members of another [`AllySet`] into this one.
    fn bitor_assign(&mut self, rhs: T) {
        self.0 |= rhs.into().0;
    }
}

impl<T: Into<AllySet>> BitXor<T> for AllySet {
    type Output = Self;
    /// Computes the _symmetric_ set difference of two [`AllySet`]s.
    ///
    /// For two sets `a` and `b`, `a ^ b` is equivalent to `(a | b) - (a & b)`.
    fn bitxor(self, rhs: T) -> Self {
        Self(self.0 ^ rhs.into().0)
    }
}

impl<T: Into<AllySet>> BitXorAssign<T> for AllySet {
    /// Toggles the membership of allies in another [`AllySet`] within this set.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::{Ally::*, AllySet};
    /// let mut allies = Samara | Thane;
    /// allies ^= AllySet::ASARI;
    /// assert_eq!(allies, Morinth | Thane);
    /// ```
    fn bitxor_assign(&mut self, rhs: T) {
        self.0 ^= rhs.into().0;
    }
}

impl Not for AllySet {
    type Output = Self;
    /// Computes the complement of an [`AllySet`].
    fn not(self) -> Self {
        Self(Self::EVERYONE_BITS & !self.0)
    }
}

impl<T: Into<AllySet>> Sub<T> for AllySet {
    type Output = Self;
    /// Computes the set difference of two [`AllySet`]s.
    ///
    /// The resulting set contains all allies in `self` that are _not_ contained in `rhs`.
    fn sub(self, rhs: T) -> Self {
        Self(self.0 & !rhs.into().0)
    }
}

impl<T: Into<AllySet>> SubAssign<T> for AllySet {
    /// Removes all members of another [`AllySet`] from this one.
    fn sub_assign(&mut self, rhs: T) {
        self.0 &= !rhs.into().0;
    }
}

/// Order in which [`Ally`] values are produced by an [`AllySetIter`]
static ALLY_ORDER: &[Ally] = &[
    Ally::Garrus,
    Ally::Grunt,
    Ally::Jack,
    Ally::Jacob,
    Ally::Kasumi,
    Ally::Legion,
    Ally::Miranda,
    Ally::Mordin,
    Ally::Morinth,
    Ally::Samara,
    Ally::Tali,
    Ally::Thane,
    Ally::Zaeed,
];

/// [`AllySet`] iterator
///
/// This iterator produces [`Ally`] values from the contained [`AllySet`] sorted by name.
#[derive(Clone)]
#[must_use]
pub struct AllySetIter {
    allies: AllySet,
    order: std::slice::Iter<'static, Ally>,
}

impl AllySetIter {
    fn new(allies: AllySet) -> Self {
        Self {
            allies,
            order: ALLY_ORDER.iter(),
        }
    }
}

impl Iterator for AllySetIter {
    type Item = Ally;
    fn next(&mut self) -> Option<Ally> {
        self.order
            .by_ref()
            .copied()
            .find(|&ally| self.allies.contains(ally))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Ally::*;

    #[test]
    fn ally_set_elementwise_operations() {
        let allies = Jacob | Miranda;
        assert!(!allies.is_empty());
        assert_eq!(allies.len(), 2);
        assert!(allies.contains(Jacob));
        assert!(allies.contains(Miranda));
        assert!(!allies.contains(Kasumi));

        let allies = (allies | Thane) - Jacob;
        let mut iter = allies.iter();
        assert_eq!(iter.next().unwrap(), Miranda);
        assert_eq!(iter.next().unwrap(), Thane);
        assert_eq!(iter.next(), None);

        assert_eq!(allies.to_string(), "Miranda and Thane");

        let allies = Mordin | Zaeed | Samara | Legion;
        assert_eq!(
            allies.to_string_with_conjunction("or"),
            "Legion, Mordin, Samara, or Zaeed"
        );
    }

    #[test]
    fn ally_set_to_string_edge_cases() {
        assert_eq!(AllySet::NOBODY.to_string(), "nobody");
        assert_eq!(AllySet::EVERYONE.to_string(), "everyone");
        assert_eq!(AllySet::from(Morinth).to_string(), "Morinth");
    }

    #[test]
    fn ally_set_intersection() {
        let a = Garrus | Grunt | Zaeed;
        let b = Tali | Garrus;
        assert_eq!(a & b, Garrus.into());

        let c = Legion | Jack | Mordin | Samara;
        assert_eq!(a & c, AllySet::NOBODY);
    }

    #[test]
    fn ally_set_subtraction() {
        let a = Jacob | Thane | Morinth | Grunt;
        let b = Morinth | Jacob | Miranda;
        assert_eq!(a - b, Thane | Grunt);
    }

    #[test]
    fn ally_set_complement() {
        assert_eq!(!AllySet::NOBODY, AllySet::EVERYONE);
        assert_eq!(
            !(Garrus | Jack | Kasumi | Miranda | Morinth | Tali | Zaeed),
            Grunt | Jacob | Legion | Mordin | Samara | Thane
        );
    }
}

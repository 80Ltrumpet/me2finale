//! [`Ally`] collection and iteration

use std::cmp::{Ordering, PartialOrd};
use std::fmt::{Debug, Display};
use std::iter::FusedIterator;
use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub, SubAssign,
};

use serde::{Deserialize, Serialize};

use crate::ally::Ally;

/// Set-like type optimized for [`Ally`]
///
/// Set operations are implemented as overloaded operators (see [Trait Implementations]).
///
/// # Example
///
/// ```
/// use me2finale::ally::Ally::*;
/// use me2finale::allyset::AllySet;
/// 
/// // Create an `AllySet` that includes everyone except for Morinth, then trade Samara for Morinth
/// // using a symmetric difference.
/// let mut allies = !Morinth;
/// allies ^= AllySet::ASARI;
/// assert!(allies.contains(Morinth));
/// assert!(!allies.contains(Samara));
/// ```
///
/// [Trait Implementations]: #trait-implementations
#[derive(Clone, Copy, Default, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[must_use]
pub struct AllySet(u16);

/// Convenience macro for generating the internal representations of [`AllySet`]s
macro_rules! ally_bits {
    ($($ally:ident),+) => {
        $(crate::ally::Ally::$ally.to_bit_mask()) | +
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
    /// avoided as long as a loyal, ideal leader is selected for the second fireteam.
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

    /// The set of allies who cannot die when selected as the leader of the diversion team,
    /// regardless of loyalty
    pub const IMMORTAL_LEADERS: Self = Self(ally_bits!(Miranda));

    /// Creates a new [`AllySet`] with the given allies.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// use me2finale::allyset::AllySet;
    ///
    /// let allies = AllySet::new([Legion, Kasumi, Tali]);
    /// assert_eq!(allies, AllySet::IDEAL_TECHS);
    /// ```
    pub fn new<T: IntoIterator<Item = Ally>>(allies: T) -> Self {
        allies.into_iter().fold(Self::NOBODY, BitOr::bitor)
    }

    /// Returns `true` if the given [`Ally`] is a member of this set.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// use me2finale::allyset::AllySet;
    ///
    /// assert!(AllySet::IDEAL_BIOTICS.contains(Jack));
    /// ```
    pub const fn contains(self, ally: Ally) -> bool {
        self.0 & ally.to_bit_mask() != 0
    }

    /// Returns `true` if this set contains no allies.
    ///
    /// # Example
    ///
    /// ```
    /// # use me2finale::allyset::AllySet;
    /// assert!(AllySet::NOBODY.is_empty());
    /// ```
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Counts the number of allies contained in this set.
    ///
    /// # Example
    ///
    /// ```
    /// # use me2finale::allyset::AllySet;
    /// assert_eq!(AllySet::EVERYONE.len(), 13);
    /// ```
    pub const fn len(self) -> usize {
        self.0.count_ones() as usize
    }

    /// Generates a display-ready string of this set of allies in alphabetical order with the
    /// specified conjunction, if applicable.
    ///
    /// # Examples
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// use me2finale::allyset::AllySet;
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
        let mut ally_names = self.into_iter().map(Ally::name);
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
                    let excluded_name = (!*self).into_iter().next().unwrap().name();
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

impl Extend<Ally> for AllySet {
    fn extend<T: IntoIterator<Item = Ally>>(&mut self, allies: T) {
        *self |= Self::new(allies);
    }
}

impl FromIterator<Ally> for AllySet {
    fn from_iter<T: IntoIterator<Item = Ally>>(allies: T) -> Self {
        Self::new(allies)
    }
}

impl IntoIterator for AllySet {
    type IntoIter = IntoIter;
    type Item = Ally;
    /// Creates an iterator over the allies contained in this set.
    ///
    /// Items are yielded in alphabetical order.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    ///
    /// let mut ally_iter = (Kasumi | Morinth | Jacob).into_iter();
    /// assert_eq!(ally_iter.next(), Some(Jacob));
    /// assert_eq!(ally_iter.next(), Some(Kasumi));
    /// assert_eq!(ally_iter.next(), Some(Morinth));
    /// assert_eq!(ally_iter.next(), None);
    /// ```
    fn into_iter(self) -> IntoIter {
        IntoIter::new(self)
    }
}

impl PartialOrd for AllySet {
    /// Determines the subset/superset relationship between two [`AllySet`]s.
    ///
    /// # Examples
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    ///
    /// let a = Garrus | Tali | Samara;
    /// let b = Tali | Samara;
    /// let c = Kasumi | Garrus | Morinth;
    ///
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
    fn from(ally: Ally) -> Self {
        Self(ally.to_bit_mask())
    }
}

impl From<Option<Ally>> for AllySet {
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
    ///
    /// let intersection = (Jack | Garrus | Samara) & (Zaeed | Jack);
    /// assert_eq!(intersection, Jack.into());
    /// ```
    fn bitand(self, rhs: T) -> Self {
        Self(self.0 & rhs.into().0)
    }
}

impl<T: Into<AllySet>> BitAndAssign<T> for AllySet {
    /// Replaces `self` with its common elements within `rhs`.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// use me2finale::allyset::AllySet;
    ///
    /// let mut allies = AllySet::TECHS;
    /// // Which techs are *also* biotics?
    /// allies &= AllySet::BIOTICS;
    /// assert_eq!(allies, Jacob | Thane);
    /// ```
    fn bitand_assign(&mut self, rhs: T) {
        self.0 &= rhs.into().0;
    }
}

impl<T: Into<AllySet>> BitOr<T> for Ally {
    type Output = AllySet;
    /// Computes the union of a set containing this [`Ally`] and an [`AllySet`].
    ///
    /// This allows [`AllySet`]s to be more concisely constructed from individual allies.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    ///
    /// // This is an `AllySet`!
    /// let allies = Thane | Mordin;
    /// assert_eq!(allies.len(), 2);
    /// ```
    fn bitor(self, rhs: T) -> AllySet {
        AllySet(self.to_bit_mask() | rhs.into().0)
    }
}

impl<T: Into<AllySet>> BitOr<T> for AllySet {
    type Output = Self;
    /// Computes the union of two [`AllySet`]s.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    ///
    /// let cerberus_agents = Jacob | Miranda;
    /// let old_pals = Garrus | Tali;
    /// let awkward = cerberus_agents | old_pals;
    /// assert_eq!(awkward, Jacob | Miranda | Garrus | Tali);
    /// ```
    fn bitor(self, rhs: T) -> Self {
        Self(self.0 | rhs.into().0)
    }
}

impl<T: Into<AllySet>> BitOrAssign<T> for AllySet {
    /// Inserts all members of `rhs` into `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use me2finale::allyset::AllySet;
    /// let mut allies = AllySet::REQUIRED;
    /// allies |= AllySet::OPTIONAL;
    /// assert_eq!(allies, AllySet::EVERYONE);
    /// ```
    fn bitor_assign(&mut self, rhs: T) {
        self.0 |= rhs.into().0;
    }
}

impl<T: Into<AllySet>> BitXor<T> for AllySet {
    type Output = Self;
    /// Computes the [_symmetric difference_] of two [`AllySet`]s.
    ///
    /// For two sets `a` and `b`, `a ^ b` is equivalent to `(a | b) - (a & b)`.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// use me2finale::allyset::AllySet;
    ///
    /// // Who are ideal leaders or biotics but not both?
    /// let allies = AllySet::IDEAL_LEADERS ^ AllySet::BIOTICS;
    /// assert_eq!(allies, Garrus | Jack | Morinth | Samara | Thane);
    /// ```
    ///
    /// [_symmetric difference_]: https://en.wikipedia.org/wiki/Symmetric_difference
    fn bitxor(self, rhs: T) -> Self {
        Self(self.0 ^ rhs.into().0)
    }
}

impl<T: Into<AllySet>> BitXorAssign<T> for AllySet {
    /// Toggles the membership of allies in `rhs` within `self`.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    ///
    /// let mut allies = Tali | Mordin | Grunt;
    /// allies ^= Grunt | Garrus;
    /// assert_eq!(allies, Garrus | Mordin | Tali);
    /// ```
    fn bitxor_assign(&mut self, rhs: T) {
        self.0 ^= rhs.into().0;
    }
}

impl Not for Ally {
    type Output = AllySet;
    /// Creates an [`AllySet`] containing everyone _except_ this [`Ally`].
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// use me2finale::allyset::AllySet;
    ///
    /// // Morinth is the only ally who is neither required nor directly recruitable.
    /// assert_eq!(!Morinth, AllySet::REQUIRED | AllySet::RECRUITABLE);
    /// ```
    fn not(self) -> AllySet {
        AllySet(AllySet::EVERYONE_BITS & !self.to_bit_mask())
    }
}

impl Not for AllySet {
    type Output = Self;
    /// Computes the complement of an [`AllySet`].
    ///
    /// # Example
    ///
    /// ```
    /// # use me2finale::allyset::AllySet;
    /// // By definition, allies that are not required are optional.
    /// assert_eq!(!AllySet::REQUIRED, AllySet::OPTIONAL);
    /// ```
    fn not(self) -> Self {
        Self(Self::EVERYONE_BITS & !self.0)
    }
}

impl<T: Into<AllySet>> Sub<T> for AllySet {
    type Output = Self;
    /// Computes the difference of two [`AllySet`]s.
    ///
    /// The resulting set contains all allies in `self` that are _not_ contained in `rhs`.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// use me2finale::allyset::AllySet;
    ///
    /// // Which recruitable allies are not techs?
    /// let allies = AllySet::RECRUITABLE - AllySet::TECHS;
    /// assert_eq!(allies, Grunt | Samara | Zaeed);
    /// ```
    fn sub(self, rhs: T) -> Self {
        Self(self.0 & !rhs.into().0)
    }
}

impl<T: Into<AllySet>> SubAssign<T> for AllySet {
    /// Removes all members of `rhs` from `self`.
    ///
    /// # Example
    ///
    /// ```
    /// use me2finale::ally::Ally::*;
    /// use me2finale::allyset::AllySet;
    ///
    /// let mut allies = Jacob | Mordin | Zaeed | Grunt;
    /// allies -= AllySet::REQUIRED;
    /// assert_eq!(allies, Grunt | Zaeed);
    /// ```
    fn sub_assign(&mut self, rhs: T) {
        self.0 &= !rhs.into().0;
    }
}

/// Order in which [`Ally`] values are produced by [`Iter`]
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
pub struct IntoIter {
    allies: AllySet,
    order: std::slice::Iter<'static, Ally>,
}

impl IntoIter {
    fn new(allies: AllySet) -> Self {
        Self {
            allies,
            order: ALLY_ORDER.iter(),
        }
    }
}

impl Iterator for IntoIter {
    type Item = Ally;
    fn next(&mut self) -> Option<Ally> {
        let ally = self
            .order
            .by_ref()
            .copied()
            .find(|&ally| self.allies.contains(ally));
        self.allies -= ally;
        ally
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.allies.len();
        (size, Some(size))
    }
}

impl DoubleEndedIterator for IntoIter {
    fn next_back(&mut self) -> Option<Ally> {
        let ally = self
            .order
            .by_ref()
            .copied()
            .rfind(|&ally| self.allies.contains(ally));
        self.allies -= ally;
        ally
    }
}

impl ExactSizeIterator for IntoIter {}
impl FusedIterator for IntoIter {}

#[cfg(test)]
mod tests {
    use super::*;
    use Ally::*;

    #[test]
    fn elementwise_operations() {
        let allies = Jacob | Miranda;
        assert!(!allies.is_empty());
        assert_eq!(allies.len(), 2);
        assert!(allies.contains(Jacob));
        assert!(allies.contains(Miranda));
        assert!(!allies.contains(Kasumi));

        let allies = (allies | Thane) - Jacob;
        let mut iter = allies.into_iter();
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
    fn to_string_edge_cases() {
        assert_eq!(AllySet::NOBODY.to_string(), "nobody");
        assert_eq!(AllySet::EVERYONE.to_string(), "everyone");
        assert_eq!(AllySet::from(Morinth).to_string(), "Morinth");
    }

    #[test]
    fn intersection() {
        let a = Garrus | Grunt | Zaeed;
        let b = Tali | Garrus;
        assert_eq!(a & b, Garrus.into());

        let c = Legion | Jack | Mordin | Samara;
        assert_eq!(a & c, AllySet::NOBODY);
    }

    #[test]
    fn difference() {
        let a = Jacob | Thane | Morinth | Grunt;
        let b = Morinth | Jacob | Miranda;
        assert_eq!(a - b, Thane | Grunt);
    }

    #[test]
    fn complement() {
        assert_eq!(!AllySet::NOBODY, AllySet::EVERYONE);
        assert_eq!(
            !(Garrus | Jack | Kasumi | Miranda | Morinth | Tali | Zaeed),
            Grunt | Jacob | Legion | Mordin | Samara | Thane
        );
    }

    #[test]
    fn symmetric_difference() {
        let a = Legion | Thane | Jack | Morinth;
        let b = Thane | Garrus | Zaeed;
        assert_eq!(a ^ b, Garrus | Jack | Legion | Morinth | Zaeed);
    }

    #[test]
    fn iter() {
        let mut iter = (Tali | Grunt | Kasumi | Samara | Jacob).into_iter();
        assert_eq!(iter.next(), Some(Grunt));
        assert_eq!(iter.next_back(), Some(Tali));
        assert_eq!(iter.next(), Some(Jacob));
        assert_eq!(iter.next_back(), Some(Samara));
        assert_eq!(iter.next(), Some(Kasumi));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
    }
}

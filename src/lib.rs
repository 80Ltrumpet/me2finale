#![warn(missing_docs)]
//! # _Mass Effect 2_ Final Mission Analysis
//!
//! This crate defines types that encode _decision paths_ and _outcomes_ related to the final
//! mission of [_Mass Effect 2_]. Although the game presents many, many choices to the player,
//! only certain ones affect the survival of your allies into and through _Mass Effect 3_, if you
//! transfer your save file. This crate is only concerned with those aspects of the game.
//!
//! Particulars of decision paths and outcomes are documented in
//! [`DecisionPath`][crate::decision::DecisionPath] and [`Outcome`], respectively.
//!
//! The [`generate::outcome_map`] function traverses all possible decision paths, determines their
//! outcomes, and returns an [`OutcomeMap`]—a [`HashMap`] keyed by [`Outcome`]. Instead of storing
//! _all_ [`DecisionPath`]s that led to each [`Outcome`], the [`OutcomeMap`]'s values contain _one_
//! such decision path and a count. The reason for this is limited memory, as there are over 64
//! **billion** possible decision paths.
//!
//! The allies involved in the choices and tabulated in the outcomes are encoded in the [`Ally`]
//! enum and its dedicated collection type, [`AllySet`]. To effect your own queries of the outcome
//! data, you will want a passing familiarity with these types. The following example determines
//! how often Tali, the Quarian, survives out of all possibilities—that is, her _absolute survival
//! rate_.
//!
//! ```no_run
//! # use std::error::Error;
//! #
//! use me2finale::prelude::*;
//! 
//! # fn main() -> Result<(), Box<dyn Error>> {
//! #
//! #[cfg(feature = "generate")]
//! let outcome_map = me2finale::generate::outcome_map();
//!
//! #[cfg(not(feature = "generate"))]
//! let outcome_map = {
//!     use serde::Deserialize;
//!     let file = std::fs::File::open("outcome_map.rmp")?;
//!     let mut deserializer = rmp_serde::Deserializer::new(file);
//!     OutcomeMap::deserialize(&mut deserializer)?
//! };
//!
//! let total_traversals = outcome_map
//!     .values()
//!     .map(|metadata| metadata.count)
//!     .sum::<usize>();
//!
//! let tali_survivals = outcome_map
//!     .iter()
//!     .filter_map(|(outcome, metadata)| {
//!         outcome
//!             .survivors
//!             .contains(Ally::Tali)
//!             .then_some(metadata.count)
//!     })
//!     .sum::<usize>();
//!
//! let tali_survival_rate = tali_survivals as f32 / total_traversals as f32;
//! println!("Tali's absolute survival rate is {tali_survival_rate}.");
//! #
//! # Ok(())
//! # }
//! ```
//!
//! ## Optional Features
//!
//! By default, this crate supports merely exposes types and facilities necessary to query and
//! serialize/deserialize (via [`serde`] traits) _existing_ outcome data. If you wish to generate
//! the outcome data yourself, you must enable the `generate` feature. Doing so adds a few external
//! dependencies and gives access to [`generate::outcome_map`].
//!
//! ## More Examples
//!
//! The [`me2finale` repository] includes examples for generating and analyzing outcome data.
//!
//! [_Mass Effect 2_]: https://en.wikipedia.org/wiki/Mass_Effect_2
//! [`HashMap`]: std::collections::HashMap
//! [`DecisionPath`]: crate::decision::DecisionPath
//! [`me2finale` repository]: https://github.com/80Ltrumpet/me2finale

pub mod ally;
pub mod decision;
#[cfg(feature = "generate")]
pub mod generate;
pub mod outcome;

#[cfg(feature = "generate")]
mod death;

#[doc(inline)]
pub use ally::Ally;
#[doc(inline)]
pub use ally::AllySet;
#[doc(inline)]
pub use outcome::Outcome;
#[doc(inline)]
pub use outcome::OutcomeMap;

/// Commonly used types
pub mod prelude {
    pub use crate::ally::{Ally, AllySet};
    pub use crate::outcome::{Outcome, OutcomeMap};
}

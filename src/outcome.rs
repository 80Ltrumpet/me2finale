//! Outcome data types

use std::collections::HashMap;
use std::fmt::Display;

use serde::{Deserialize, Serialize};

use crate::allyset::AllySet;
use crate::decision::DecisionPath;

/// [`HashMap`] of [`Outcome`]s to [metadata][DecisionPathMetadata] describing the [`DecisionPath`]s
/// from which they were produced
pub type OutcomeMap = HashMap<Outcome, DecisionPathMetadata>;

/// Result of one or more complete decision paths
#[derive(Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct Outcome {
    /// Allies who survived the final mission
    pub survivors: AllySet,
    /// Loyal allies who survived the final mission
    pub loyal: AllySet,
    /// Was the crew of _The Normandy_ rescued?
    pub rescued_crew: bool,
}

impl Display for Outcome {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "Survivors: {}", self.survivors)?;
        write!(f, "Loyal:     ")?;
        if self.loyal.len() == self.survivors.len() {
            writeln!(f, "all survivors")?;
        } else {
            writeln!(f, "{}", self.loyal)?;
        }
        let past_tense_verb = if self.rescued_crew {
            "rescued"
        } else {
            "abandoned"
        };
        writeln!(f, "The crew was {past_tense_verb}.")
    }
}

/// [`OutcomeMap`] value
#[derive(Debug, Deserialize, Serialize)]
pub struct DecisionPathMetadata {
    /// Number of distinct decision paths that led to the same [`Outcome`]
    pub count: usize,
    /// One example of a decision path that led to an [`Outcome`]
    pub example: DecisionPath,
}

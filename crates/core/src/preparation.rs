//! Preparation precedes every business write. Governed by BeliefEmbedding.agda.
use crate::{
    documents::DocumentChunk,
    graph::{Belief, Probability},
    interaction::{CorrectionItem, Location, NeedsInput},
    learning::IndependentProvenance,
    validation::{Code, Fault, Segment},
};

/// Only preparation or a pre-write check may produce this outcome. A database
/// error after publication was attempted must retain its uncertain outcome.
#[derive(Debug)]
pub struct PreparationRequired {
    correction: NeedsInput,
}

impl PreparationRequired {
    pub(crate) fn new(location: Location, path: Vec<Segment>, code: Code, message: String) -> Self {
        let item = CorrectionItem::new(location, Fault { path, code, message },
            "A complete embedding and a supporting passage from an indexed, project-compatible document before this belief is stored.".into(),
            "Open a dialog with the user explaining the missing prerequisite. Ask whether to repair the configured backend, index a supporting document, revise the belief, or cancel. Do not guess, silently shorten the content, change the model, or store an ungrounded belief.".into())
            .expect("compiled preparation guidance contains all required explanations");
        Self {
            correction: NeedsInput::new(item, vec![])
                .expect("preparation provides one explained issue"),
        }
    }

    pub fn correction(&self) -> &NeedsInput {
        &self.correction
    }
}

impl std::fmt::Display for PreparationRequired {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match serde_json::to_string(&self.correction) {
            Ok(report) => formatter.write_str(&report),
            Err(_) => formatter
                .write_str("Belief preparation requires a user decision; no belief was stored."),
        }
    }
}

impl std::error::Error for PreparationRequired {}

#[derive(Clone, Debug)]
pub(crate) struct SupportingPassage {
    pub(crate) chunk: DocumentChunk,
    pub(crate) weight: Probability,
}

/// Fields stay private to this crate. Public callers cannot declare that their
/// own arbitrary vector or passage list constitutes successful preparation.
#[derive(Clone, Debug)]
pub struct PreparedBelief {
    pub(crate) belief: Belief,
    pub(crate) provenance: Option<IndependentProvenance>,
    pub(crate) vector: Vec<f32>,
    pub(crate) support: Vec<SupportingPassage>,
}

impl PreparedBelief {
    pub fn belief(&self) -> &Belief {
        &self.belief
    }
}

pub(crate) fn usable_vector(vector: &[f32]) -> bool {
    vector.iter().all(|value| value.is_finite()) && vector.iter().any(|value| *value != 0.0)
}

pub(crate) fn compatible_projects(first: Option<&str>, second: Option<&str>) -> bool {
    match (first, second) {
        (Some(first), Some(second)) => first == second,
        _ => true,
    }
}

#[cfg(test)]
mod tests;

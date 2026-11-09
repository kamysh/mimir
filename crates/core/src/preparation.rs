//! Preparation precedes every business write. Governed by BeliefEmbedding.agda.
use crate::{
    config::{EmbeddingBackend, EmbeddingsConfig},
    documents::DocumentChunk,
    graph::{Belief, Probability},
    interaction::{CorrectionItem, Location, NeedsInput},
    learning::IndependentProvenance,
    validation::{Code, Fault, Segment},
};

/// Semantic provider choices for the immutable operation binding. Credentials,
/// cache location and execution batching are deliberately absent.
pub(crate) fn operation_settings(configured: Option<&EmbeddingsConfig>) -> serde_json::Value {
    let identity = configured.map(|settings| match settings.backend {
        EmbeddingBackend::Local => serde_json::json!({
            "backend":"local", "model":crate::embed::HF_MODEL_ID
        }),
        EmbeddingBackend::Voyage => serde_json::json!({
            "backend":"voyage", "model":settings.model,
            "input_type":"document", "truncation":false
        }),
        EmbeddingBackend::OpenAi => serde_json::json!({
            "backend":"openai", "model":settings.model
        }),
    });
    serde_json::json!({"embeddings":identity})
}

/// Only preparation or a pre-write check may produce this outcome. A database
/// error after publication was attempted must retain its uncertain outcome.
#[derive(Debug)]
pub struct PreparationRequired {
    correction: NeedsInput,
}

impl PreparationRequired {
    pub(crate) fn backfill(code: Code, message: String) -> Self {
        let item=CorrectionItem::new(Location::Configuration,
            Fault {path:vec![Segment::Key("embeddings".into())],code,message},
            "Exactly one complete, finite, nonzero embedding for this stored belief before reporting it embedded.".into(),
            "Open a dialog with the user to repair the configured embedding backend or cancel. Do not silently shorten the content, change the model, or count this belief as embedded.".into())
            .expect("compiled backfill guidance contains the problem and repair path");
        Self {
            correction: NeedsInput::new(item, vec![]).expect("one explained backfill issue"),
        }
    }

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

    pub(crate) fn for_review_candidate(&self, index: usize, key: &str) -> Self {
        let mut items = self.correction.issues().iter().map(|item| {
            let mut fault = item.fault().clone();
            if item.location() == Location::Arguments {
                let mut path = vec![
                    Segment::Key("review".into()),
                    Segment::Key("candidates".into()),
                    Segment::Index(index),
                ];
                path.extend(fault.path);
                fault.path = path;
            }
            fault.message = format!("Review candidate {key} at index {index}: {}", fault.message);
            CorrectionItem::new(
                item.location(),
                fault,
                item.expected().into(),
                item.suggested_correction().into(),
            )
            .expect("an existing checked issue retains all explanations")
        });
        let first = items.next().expect("checked response has an issue");
        Self {
            correction: NeedsInput::new(first, items.collect())
                .expect("checked candidate guidance"),
        }
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

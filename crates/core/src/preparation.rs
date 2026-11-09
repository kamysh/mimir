//! Preparation precedes every business write. Governed by BeliefEmbedding.agda.
use crate::{
    config::{EmbeddingBackend, EmbeddingsConfig},
    documents::DocumentChunk,
    graph::Belief,
    interaction::{CorrectionItem, Location, NeedsInput},
    learning::IndependentProvenance,
    validation::{Code, Fault, Segment},
};

/// The submitting agent cites an indexed passage and explains its support.
/// The explanation is retained as that agent's account, not certified truth.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IndexedSupport {
    pub chunk_id: uuid::Uuid,
    pub document_path: String,
    pub quotation: String,
    pub explanation: String,
}

impl IndexedSupport {
    pub(crate) fn validate_fields(&self, index: usize) -> anyhow::Result<()> {
        for (field, value) in [
            ("document_path", &self.document_path),
            ("quotation", &self.quotation),
            ("explanation", &self.explanation),
        ] {
            if value.trim().is_empty() {
                return Err(PreparationRequired::new(Location::Arguments,
                    vec![Segment::Key("grounding".into()), Segment::Index(index), Segment::Key(field.into())],
                    Code::EmptyText,
                    format!("grounding[{index}].{field} must contain nonblank text. Cite the actual indexed document and an exact supporting quotation, then explain why it supports this belief. If support is unclear, open the user dialog before publication.")).into());
            }
        }
        Ok(())
    }
}

/// Bound to a concrete indexed source read. A caller cannot construct this
/// receipt through the public write API or substitute its own document text.
#[derive(Clone, Debug)]
pub(crate) struct ValidatedSupport {
    pub(crate) chunk: DocumentChunk,
    pub(crate) citation: IndexedSupport,
}

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

/// Validate only the captured semantic identity; never accept credentials or
/// infer a replacement model from the current configuration.
pub(crate) fn validate_operation_settings(value: &serde_json::Value) -> anyhow::Result<()> {
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Settings {
        embeddings: mimir_json::Document,
    }
    #[derive(serde::Deserialize)]
    #[serde(tag = "backend", rename_all = "lowercase", deny_unknown_fields)]
    enum Identity {
        Local {
            model: String,
        },
        Voyage {
            model: String,
            input_type: String,
            truncation: bool,
        },
        #[serde(rename = "openai")]
        OpenAi {
            model: String,
        },
    }
    let settings: Settings = mimir_json::decode_ref(value)?;
    if !settings.embeddings.is_null() {
        match mimir_json::decode_ref::<Identity>(&settings.embeddings)? {
            Identity::Local { model } => anyhow::ensure!(model == crate::embed::HF_MODEL_ID,
                "Retain the actual configured local BGE model; read the original binding before choosing a different model"),
            Identity::Voyage { model, input_type, truncation } => {
                anyhow::ensure!(input_type == "document" && !truncation,
                    "Retain Voyage document input without truncation from the original binding");
                let _ = model;
            }
            Identity::OpenAi { model } => { let _ = model; }
        }
    }
    Ok(())
}

/// Only preparation or a pre-write check may produce this outcome. A database
/// error after publication was attempted must retain its uncertain outcome.
#[derive(Debug)]
pub struct PreparationRequired {
    correction: NeedsInput,
}

impl PreparationRequired {
    pub(crate) fn document(
        location: Location,
        path: Vec<Segment>,
        code: Code,
        message: String,
    ) -> Self {
        let item = CorrectionItem::new(location, Fault { path, code, message },
            "The original readable document, its saved preparation and a complete usable embedding for each chunk before replacing the index.".into(),
            "Explain the reported problem and open a user dialog to repair the source or configured backend. Keep this operation's original token and saved outcome; do not silently substitute a file, model or new token, and do not publish a partial replacement.".into())
            .expect("compiled document guidance provides the problem and repair path");
        Self {
            correction: NeedsInput::new(item, vec![])
                .expect("document preparation reports one explained issue"),
        }
    }

    pub(crate) fn bound_request(code: Code, message: String) -> Self {
        let item=CorrectionItem::new(Location::Request,
            Fault {path:vec![Segment::Key("operation_token".into())],code,message},
            "The original immutable belief request, with its declared fields and server-selected settings.".into(),
            "Read this token's saved binding and outcome. If its arguments are wrong, ask the user to explicitly cancel unfinished work before reserving a corrected request. Do not rewrite a bound request, silently cancel it, or invent a replacement token.".into())
            .expect("bound-request guidance names the original record and the authorized correction path");
        Self {
            correction: NeedsInput::new(item, vec![]).expect("one explained bound-request issue"),
        }
    }

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
        match mimir_json::to_string(&self.correction) {
            Ok(report) => formatter.write_str(&report),
            Err(_) => formatter
                .write_str("Belief preparation requires a user decision; no belief was stored."),
        }
    }
}

impl std::error::Error for PreparationRequired {}

/// Fields stay private to this crate. Public callers cannot declare that their
/// own arbitrary vector or passage list constitutes successful preparation.
#[derive(Clone, Debug)]
pub struct PreparedBelief {
    pub(crate) belief: Belief,
    pub(crate) provenance: Option<IndependentProvenance>,
    pub(crate) vector: Vec<f32>,
    pub(crate) support: Vec<ValidatedSupport>,
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

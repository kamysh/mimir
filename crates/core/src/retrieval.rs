//! Explain the matching actually performed for the complete submitted context.
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SemanticSearch {
    pub status: String,
    pub reason: String,
    pub cause: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RetrievalCoverage {
    pub context: String,
    pub semantic_search: SemanticSearch,
    pub matching_performed: String,
    pub message: String,
    pub coverage: String,
    pub next_step: String,
}

pub(crate) enum SemanticObservation {
    Evaluated,
    Unconfigured,
    NoEligibleBeliefs,
    EmbeddingFailed(String),
    UnusableQueryVector(String),
}

impl RetrievalCoverage {
    pub(crate) fn observed(context: &str, observed: SemanticObservation) -> Self {
        use SemanticObservation::*;
        let (status, reason, cause, method, message, coverage, next_step) = match observed {
            Evaluated => (
                "available", "evaluated", None, "keyword_and_semantic",
                "Semantic search and keyword matching were performed for this context.".into(),
                "Results combine semantic and literal matches with any graph expansion and ranking.",
                "Inspect the returned beliefs and supporting evidence before relying on them.",
            ),
            Unconfigured => (
                "unavailable", "not_configured", None, "keyword",
                "Semantic search was not performed because no embedding backend is configured. These results use keyword matching; semantic similarity was not evaluated.".into(),
                "Results cover literal matches and any graph connections derived from them. Beliefs related only by semantic similarity may be missing.",
                "Use these results for literal matching. If semantic matching is needed, ask the user to configure an embedding backend and repeat this query.",
            ),
            NoEligibleBeliefs => (
                "not_performed", "no_eligible_beliefs", None, "none",
                "No eligible stored beliefs exist in the requested scope. Semantic search and keyword matching were not performed.".into(),
                "No searchable beliefs were available in this scope; this does not establish that the context has no useful meaning.",
                "Check the requested project and the stored belief inventory. Do not infer that no relevant knowledge exists outside this scope.",
            ),
            EmbeddingFailed(cause) => (
                "unavailable", "embedding_failed", Some(cause.clone()), "keyword",
                format!("Semantic search was not performed because the configured embedding backend failed for this context: {cause}. These results use keyword matching; semantic similarity was not evaluated."),
                "Results cover literal matches and any graph connections derived from them. Beliefs related only by semantic similarity may be missing.",
                "Use the stated cause to resolve the backend problem and repeat this query if semantic coverage is needed. Keyword results remain usable for literal matching.",
            ),
            UnusableQueryVector(cause) => (
                "unavailable", "unusable_query_vector", Some(cause.clone()), "keyword",
                format!("Semantic search was not performed because the configured backend did not return a usable query vector: {cause}. These results use keyword matching; semantic similarity was not evaluated."),
                "Results cover literal matches and any graph connections derived from them. Beliefs related only by semantic similarity may be missing.",
                "Check the backend's response for the complete submitted context and repeat this query if semantic coverage is needed. Do not silently shorten the input.",
            ),
        };
        Self {
            context: context.into(),
            semantic_search: SemanticSearch {
                status: status.into(),
                reason: reason.into(),
                cause,
            },
            matching_performed: method.into(),
            message,
            coverage: coverage.into(),
            next_step: next_step.into(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct RetrievalReport<T> {
    pub beliefs: Vec<T>,
    pub retrieval: RetrievalCoverage,
}

//! Server-captured source selection. This module does not run a provider or
//! decide what to do when another writer changes a captured source/vector.
use super::{operation_plans::CapturedSelection, AgeStore, OperationBindingRequest, PlanDecision};
use crate::operation_catalogue::CommitSite;
use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::BTreeSet;
use uuid::Uuid;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Source {
    id: Uuid,
    content: String,
    // Value deliberately requires the field, including an explicit null.
    project: Value,
    already_embedded: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Capture {
    beliefs: Vec<Source>,
}

pub(super) fn pending_keys(value: &Value) -> Result<Vec<String>> {
    let captured: Capture = mimir_json::from_value(value.clone())?;
    let mut previous = None;
    let mut pending = Vec::new();
    for source in &captured.beliefs {
        ensure!(
            source.project.is_null() || source.project.is_string(),
            "A captured belief project must be its original string or null"
        );
        ensure!(
            previous.is_none_or(|id| id < source.id),
            "Captured belief IDs must be unique and in their original UUID order"
        );
        previous = Some(source.id);
        if !source.already_embedded {
            pending.push(source.id.to_string());
        }
    }
    // UUID parsing also accepts alternate spellings; persisted snapshots use
    // the one canonical representation produced by the server.
    ensure!(
        mimir_json::to_value(&captured)? == *value,
        "The captured source selection does not use its canonical stored representation"
    );
    Ok(pending)
}

impl AgeStore {
    pub(crate) async fn prepare_reembed_plan(
        &self,
        token: Uuid,
        expected: &OperationBindingRequest,
    ) -> Result<PlanDecision> {
        ensure!(
            expected.operation() == "reembed" && expected.arguments() == &serde_json::json!({}),
            "Backfill must retain its original reembed request with no per-call overrides"
        );
        crate::preparation::validate_operation_settings(expected.settings())?;
        let source = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        self.prepare_operation_captured(token, expected, move |tx, _| {
            Box::pin(async move {
                let mut beliefs = source.list_beliefs_on(tx).await?;
                let embedded: BTreeSet<Uuid> = tx
                    .query("SELECT belief_id FROM belief_embeddings", &[])
                    .await?
                    .iter()
                    .map(|row| row.try_get(0))
                    .collect::<std::result::Result<_, _>>()?;
                beliefs.sort_by_key(|belief| belief.id);
                let capture = Capture {
                    beliefs: beliefs
                        .into_iter()
                        .map(|belief| Source {
                            id: belief.id,
                            content: belief.content,
                            project: mimir_json::to_value(belief.project)
                                .expect("optional string is JSON"),
                            already_embedded: embedded.contains(&belief.id),
                        })
                        .collect(),
                };
                let value = mimir_json::to_value(capture)?;
                let pending = pending_keys(&value)?;
                Ok(CapturedSelection {
                    selections: vec![(CommitSite::BeliefVectorPublication, pending)],
                    capture: Some(value),
                })
            })
        })
        .await
    }
}

#[cfg(test)]
#[path = "backfill_tests.rs"]
mod tests;

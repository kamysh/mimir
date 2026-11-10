//! Observe complete, ordered source references, including references whose
//! graph nodes are missing.
use anyhow::{Context, Result};
use mimir_core::preparation::IndexedSupport;
use serde::Serialize;
use tokio_postgres::Transaction;
use uuid::Uuid;

#[derive(Debug, PartialEq, Serialize)]
pub struct SourceRow {
    pub key: Uuid,
    pub value: Vec<IndexedSupport>,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Vec<SourceRow>> {
    tx.query(
        "SELECT belief_id, citations::text FROM public.mimir_belief_sources ORDER BY belief_id",
        &[],
    )
    .await?
    .into_iter()
    .map(|row| {
        let key = row.try_get(0)?;
        let citations: String = row.try_get(1)?;
        Ok(SourceRow {
            key,
            value: serde_json::from_str(&citations).context("invalid stored belief citations")?,
        })
    })
    .collect()
}

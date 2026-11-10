//! Gather the graph-related observations from one consistent database view.
#[path = "belief_link_observation.rs"]
pub mod belief_links;
#[path = "belief_metadata_observation.rs"]
pub mod belief_metadata;
#[path = "chunk_observation.rs"]
pub mod chunks;
#[path = "grounding_observation.rs"]
pub mod grounds;
#[path = "node_observation.rs"]
pub mod nodes;
#[path = "source_observation.rs"]
pub mod sources;
#[path = "vector_observation.rs"]
pub mod vectors;

use anyhow::{bail, Result};
use tokio_postgres::Transaction;

#[derive(Debug, PartialEq)]
pub struct GraphObservation {
    pub nodes: nodes::Nodes,
    pub belief_metadata: Vec<belief_metadata::BeliefMetadata>,
    pub chunks: Vec<chunks::StoredChunk>,
    pub belief_links: Vec<belief_links::BeliefLink>,
    pub grounds: Vec<grounds::Ground>,
    pub sources: Vec<sources::SourceRow>,
    pub vectors: vectors::StoredVectors,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<GraphObservation> {
    let isolation: String = tx
        .query_one("SHOW transaction_isolation", &[])
        .await?
        .try_get(0)?;
    if isolation != "repeatable read" && isolation != "serializable" {
        bail!("Use one repeatable-read or serializable transaction to observe the database consistently");
    }
    Ok(GraphObservation {
        nodes: nodes::observe(tx).await?,
        belief_metadata: belief_metadata::observe(tx).await?,
        chunks: chunks::observe(tx).await?,
        belief_links: belief_links::observe(tx).await?,
        grounds: grounds::observe(tx).await?,
        sources: sources::observe(tx).await?,
        vectors: vectors::observe(tx).await?,
    })
}

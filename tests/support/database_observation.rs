//! Read graph, learning and operation records from the same database view.
#[path = "graph_observation.rs"]
pub mod graph;
#[path = "learning_observation.rs"]
pub mod learning;
#[path = "operation_observation.rs"]
pub mod operations;

use anyhow::Result;
use tokio_postgres::Transaction;

#[derive(Debug, PartialEq)]
pub struct DatabaseObservation {
    pub graph: graph::GraphObservation,
    pub learning: learning::LearningObservation,
    pub operations: operations::Operations,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<DatabaseObservation> {
    Ok(DatabaseObservation {
        graph: graph::observe(tx).await?,
        learning: learning::observe(tx).await?,
        operations: operations::observe(tx).await?,
    })
}

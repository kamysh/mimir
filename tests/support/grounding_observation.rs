//! Observe grounding links independently of vector and source-reference rows.
use anyhow::{Context, Result};
use serde::Serialize;
use tokio_postgres::Transaction;
use uuid::Uuid;

#[derive(Debug, PartialEq, Serialize)]
pub struct Ground {
    pub chunk: Uuid,
    pub belief: Uuid,
    pub weight: f64,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Vec<Ground>> {
    let graph: String = tx
        .query_one("SELECT current_database()", &[])
        .await?
        .try_get(0)?;
    let graph = graph.replace('\'', "''");
    let sql = format!(
        r#"SELECT chunk::text, belief::text, weight::text
FROM ag_catalog.cypher('{graph}', $$
  MATCH (c:DocumentChunk)-[r:GROUNDS]->(b:Belief)
  RETURN c.id, b.id, r.weight
$$) AS (chunk text, belief text, weight text)
ORDER BY chunk::text, belief::text, weight::text"#
    );
    tx.query(&sql, &[])
        .await?
        .into_iter()
        .map(|row| {
            let chunk: String = row.try_get("chunk")?;
            let belief: String = row.try_get("belief")?;
            let weight: String = row.try_get("weight")?;
            Ok(Ground {
                chunk: Uuid::parse_str(&chunk).context("invalid grounding chunk identity")?,
                belief: Uuid::parse_str(&belief).context("invalid grounding belief identity")?,
                weight: weight.parse().context("invalid grounding weight")?,
            })
        })
        .collect()
}

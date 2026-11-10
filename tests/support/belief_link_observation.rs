//! Read belief links directly, retaining duplicate links and their owners.
use anyhow::{Context, Result};
use mimir_core::graph::EdgeType;
use serde::Serialize;
use tokio_postgres::Transaction;
use uuid::Uuid;

#[derive(Debug, PartialEq, Serialize)]
pub struct BeliefLink {
    pub owner: Option<Uuid>,
    pub from: Uuid,
    pub to: Uuid,
    pub relation: EdgeType,
    pub weight: f64,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Vec<BeliefLink>> {
    let graph: String = tx
        .query_one("SELECT current_database()", &[])
        .await?
        .try_get(0)?;
    let graph = graph.replace('\'', "''");
    let sql = format!(
        r#"SELECT owner::text, source::text, target::text, relation::text, weight::text
FROM ag_catalog.cypher('{graph}', $$
  MATCH (a:Belief)-[r]->(b:Belief)
  RETURN r.experience_id, a.id, b.id, type(r), r.weight
$$) AS (owner text, source text, target text, relation text, weight text)
ORDER BY source, target, relation, owner, weight"#
    );
    tx.query(&sql, &[])
        .await?
        .into_iter()
        .map(|row| {
            let owner: Option<String> = row.try_get("owner")?;
            let source: String = row.try_get("source")?;
            let target: String = row.try_get("target")?;
            let relation: String = row.try_get("relation")?;
            let weight: String = row.try_get("weight")?;
            Ok(BeliefLink {
                owner: owner
                    .map(|value| Uuid::parse_str(&value))
                    .transpose()
                    .context("invalid belief link owner")?,
                from: Uuid::parse_str(&source).context("invalid belief link source")?,
                to: Uuid::parse_str(&target).context("invalid belief link target")?,
                relation: relation.parse().context("invalid belief link relation")?,
                weight: weight.parse().context("invalid belief link weight")?,
            })
        })
        .collect()
}

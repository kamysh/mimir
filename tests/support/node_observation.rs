//! Read graph nodes without recalculating stored probabilities or counters.
use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use serde::Serialize;
use tokio_postgres::{Row, Transaction};
use uuid::Uuid;

#[derive(Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct BeliefNode {
    pub identity: Uuid,
    pub content: String,
    pub project: Option<String>,
    pub memory: String,
    pub created: DateTime<Utc>,
    pub activated: DateTime<Utc>,
    pub decay_accounted_at: DateTime<Utc>,
    pub probability: f64,
    pub confidence: f64,
    pub alpha: f64,
    pub beta: f64,
    pub alpha0: f64,
    pub beta0: f64,
}

#[derive(Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PatternNode {
    pub identity: Uuid,
    pub situation: String,
    pub approach: String,
    pub project: Option<String>,
    pub created: DateTime<Utc>,
    pub activation_count: u64,
    pub success_rate: f64,
}

#[derive(Debug, PartialEq)]
pub struct Nodes {
    pub beliefs: Vec<BeliefNode>,
    pub patterns: Vec<PatternNode>,
}

fn parse<T: std::str::FromStr>(row: &Row, name: &str) -> Result<T>
where
    T::Err: std::error::Error + Send + Sync + 'static,
{
    let value: String = row.try_get(name)?;
    value
        .parse()
        .with_context(|| format!("invalid stored {name}"))
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Nodes> {
    let graph: String = tx
        .query_one("SELECT current_database()", &[])
        .await?
        .try_get(0)?;
    let graph = graph.replace('\'', "''");
    let beliefs = format!(
        r#"SELECT * FROM ag_catalog.cypher('{graph}', $$
      MATCH (b:Belief)
      RETURN b.id,b.content,b.project,b.memory_type,b.created_at,b.last_activated_at,b.decay_accounted_at,
        b.probability,b.confidence,b.alpha,b.beta,b.alpha0,b.beta0
      $$) AS (id text,content text,project text,memory text,created text,activated text,accounted text,
        probability text,confidence text,alpha text,beta text,alpha0 text,beta0 text) ORDER BY id"#
    );
    let patterns = format!(
        r#"SELECT * FROM ag_catalog.cypher('{graph}', $$
      MATCH (p:Pattern) RETURN p.id,p.situation,p.approach,p.project,p.created_at,p.activation_count,p.success_rate
      $$) AS (id text,situation text,approach text,project text,created text,activation_count text,success_rate text) ORDER BY id"#
    );
    let beliefs = tx
        .query(&beliefs, &[])
        .await?
        .into_iter()
        .map(|row| {
            Ok(BeliefNode {
                identity: parse(&row, "id")?,
                content: row.try_get("content")?,
                project: row.try_get("project")?,
                memory: row.try_get("memory")?,
                created: parse(&row, "created")?,
                activated: parse(&row, "activated")?,
                decay_accounted_at: parse(&row, "accounted")?,
                probability: parse(&row, "probability")?,
                confidence: parse(&row, "confidence")?,
                alpha: parse(&row, "alpha")?,
                beta: parse(&row, "beta")?,
                alpha0: parse(&row, "alpha0")?,
                beta0: parse(&row, "beta0")?,
            })
        })
        .collect::<Result<_>>()?;
    let patterns = tx
        .query(&patterns, &[])
        .await?
        .into_iter()
        .map(|row| {
            Ok(PatternNode {
                identity: parse(&row, "id")?,
                situation: row.try_get("situation")?,
                approach: row.try_get("approach")?,
                project: row.try_get("project")?,
                created: parse(&row, "created")?,
                activation_count: parse(&row, "activation_count")?,
                success_rate: parse(&row, "success_rate")?,
            })
        })
        .collect::<Result<_>>()?;
    Ok(Nodes { beliefs, patterns })
}

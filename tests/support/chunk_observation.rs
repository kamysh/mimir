//! Observe document chunks without joining them to vector rows.
use anyhow::{Context, Result};
use serde::Serialize;
use tokio_postgres::Transaction;
use uuid::Uuid;

#[derive(Debug, PartialEq, Serialize)]
pub struct StoredChunk {
    pub identity: Uuid,
    pub document: String,
    pub section: Vec<String>,
    pub content: String,
    pub parent: Option<Uuid>,
    pub project: Option<String>,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Vec<StoredChunk>> {
    let graph: String = tx
        .query_one("SELECT current_database()", &[])
        .await?
        .try_get(0)?;
    // AGE graph names equal the database name. Quote it as an SQL literal;
    // graph contents are never interpolated into the query.
    let graph = graph.replace('\'', "''");
    let sql = format!(
        r#"SELECT id::text, document_path, section_path, content::text, parent_id, project::text
FROM ag_catalog.cypher('{graph}', $$
  MATCH (c:DocumentChunk)
  RETURN c.id, c.documentPath, c.sectionPath, c.content, c.parentId, c.project
$$) AS (id text, document_path text, section_path text, content text, parent_id text, project text)
ORDER BY id"#
    );
    tx.query(&sql, &[])
        .await?
        .into_iter()
        .map(|row| {
            let identity: String = row.try_get("id")?;
            let section: String = row.try_get("section_path")?;
            let parent: Option<String> = row.try_get("parent_id")?;
            Ok(StoredChunk {
                identity: Uuid::parse_str(&identity).context("invalid stored chunk identity")?,
                document: row.try_get("document_path")?,
                section: serde_json::from_str(&section).context("invalid stored section path")?,
                content: row.try_get("content")?,
                parent: parent
                    .map(|value| Uuid::parse_str(&value))
                    .transpose()
                    .context("invalid stored parent identity")?,
                project: row.try_get("project")?,
            })
        })
        .collect()
}

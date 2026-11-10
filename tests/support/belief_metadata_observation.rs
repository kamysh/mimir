//! Preserve provenance and retirement properties exactly as stored by AGE.
use anyhow::{Context, Result};
use tokio_postgres::Transaction;
use uuid::Uuid;

#[derive(Debug, PartialEq)]
pub struct BeliefMetadata {
    pub identity: Uuid,
    pub origin_basis_raw: Option<String>,
    pub origin_reference_raw: Option<String>,
    pub first_defeated_at_raw: Option<String>,
    pub legacy_defeat_expired_raw: Option<String>,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Vec<BeliefMetadata>> {
    let graph: String = tx
        .query_one("SELECT current_database()", &[])
        .await?
        .try_get(0)?;
    let graph = graph.replace('\'', "''");
    let sql = format!(
        r#"SELECT id::text, ag_catalog.agtype_out(basis)::text, ag_catalog.agtype_out(reference)::text,
      ag_catalog.agtype_out(first)::text, ag_catalog.agtype_out(legacy)::text
    FROM ag_catalog.cypher('{graph}', $$
      MATCH (b:Belief) RETURN b.id,b.origin_basis,b.origin_reference,b.first_defeated_at,b.legacy_defeat_expired
    $$) AS (id text,basis ag_catalog.agtype,reference ag_catalog.agtype,first ag_catalog.agtype,legacy ag_catalog.agtype)
    ORDER BY id"#
    );
    tx.query(&sql, &[])
        .await?
        .into_iter()
        .map(|row| {
            let id: String = row.try_get(0)?;
            Ok(BeliefMetadata {
                identity: Uuid::parse_str(&id).context("invalid stored belief identity")?,
                origin_basis_raw: row.try_get(1)?,
                origin_reference_raw: row.try_get(2)?,
                first_defeated_at_raw: row.try_get(3)?,
                legacy_defeat_expired_raw: row.try_get(4)?,
            })
        })
        .collect()
}

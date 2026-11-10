//! Read every stored vector, including vectors with no remaining graph owner.
//! The caller supplies its read-only snapshot so this observation can be
//! combined with graph and learning observations from the same database view.
use serde::Serialize;
use tokio_postgres::Transaction;
use uuid::Uuid;

#[derive(Debug, PartialEq, Serialize)]
pub struct VectorRow {
    pub id: Uuid,
    pub vector: Vec<f32>,
}

#[derive(Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct StoredVectors {
    pub belief_vectors: Vec<VectorRow>,
    pub chunk_vectors: Vec<VectorRow>,
}

async fn rows(tx: &Transaction<'_>, sql: &str) -> Result<Vec<VectorRow>, tokio_postgres::Error> {
    tx.query(sql, &[])
        .await?
        .into_iter()
        .map(|row| {
            Ok(VectorRow {
                id: row.try_get(0)?,
                vector: row.try_get::<_, pgvector::Vector>(1)?.to_vec(),
            })
        })
        .collect()
}

pub async fn observe(tx: &Transaction<'_>) -> Result<StoredVectors, tokio_postgres::Error> {
    Ok(StoredVectors {
        belief_vectors: rows(
            tx,
            "SELECT belief_id, embedding FROM public.belief_embeddings ORDER BY belief_id",
        )
        .await?,
        chunk_vectors: rows(
            tx,
            "SELECT chunk_id, embedding FROM public.chunk_embeddings ORDER BY chunk_id",
        )
        .await?,
    })
}

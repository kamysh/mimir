#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
#[path = "../../../tests/support/vector_observation.rs"]
mod vector_observation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;
use vector_observation::{observe, VectorRow};

#[tokio::test]
async fn observes_all_vectors_even_when_owners_are_missing() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
    let tx = client
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .start()
        .await?;
    let ids = tx
        .query_one("SELECT gen_random_uuid(), gen_random_uuid()", &[])
        .await?;
    let belief: Uuid = ids.get(0);
    let chunk: Uuid = ids.get(1);
    let first = pgvector::Vector::from(vec![0.25_f32, -0.5, 1.0]);
    let second = pgvector::Vector::from(vec![0.75_f32, 0.125]);
    tx.execute(
        "INSERT INTO public.belief_embeddings (belief_id, embedding) VALUES ($1, $2)",
        &[&belief, &first],
    )
    .await?;
    tx.execute(
        "INSERT INTO public.chunk_embeddings (chunk_id, embedding) VALUES ($1, $2)",
        &[&chunk, &second],
    )
    .await?;

    let snapshot = observe(&tx).await?;
    assert!(snapshot.belief_vectors.contains(&VectorRow {
        id: belief,
        vector: first.to_vec()
    }));
    assert!(snapshot.chunk_vectors.contains(&VectorRow {
        id: chunk,
        vector: second.to_vec()
    }));
    let wire = serde_json::to_value(&snapshot)?;
    assert!(wire["beliefVectors"]
        .as_array()
        .unwrap()
        .iter()
        .any(|row| row["id"] == belief.to_string()
            && row["vector"] == serde_json::json!([0.25, -0.5, 1.0])));
    assert!(wire["chunkVectors"]
        .as_array()
        .unwrap()
        .iter()
        .any(|row| row["id"] == chunk.to_string()
            && row["vector"] == serde_json::json!([0.75, 0.125])));
    tx.execute(
        "DELETE FROM public.belief_embeddings WHERE belief_id = $1",
        &[&belief],
    )
    .await?;
    let after = observe(&tx).await?;
    assert!(!after.belief_vectors.iter().any(|row| row.id == belief));
    assert_eq!(after.chunk_vectors, snapshot.chunk_vectors);
    tx.rollback().await?;
    Ok(())
}

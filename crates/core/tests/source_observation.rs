#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
#[path = "../../../tests/support/source_observation.rs"]
mod source_observation;

use anyhow::Result;
use mimir_core::{db, preparation::IndexedSupport};
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_complete_ordered_sources_without_graph_nodes() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
    let tx = client
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .start()
        .await?;
    let ids = tx
        .query_one(
            "SELECT gen_random_uuid(), gen_random_uuid(), gen_random_uuid()",
            &[],
        )
        .await?;
    let belief: Uuid = ids.get(0);
    let first: Uuid = ids.get(1);
    let second: Uuid = ids.get(2);
    let vector = pgvector::Vector::from(vec![0.5_f32]);
    tx.execute(
        "INSERT INTO public.belief_embeddings (belief_id, embedding) VALUES ($1, $2)",
        &[&belief, &vector],
    )
    .await?;
    let citations = vec![
        IndexedSupport {
            chunk_id: first,
            document_path: "one".into(),
            quotation: "first passage".into(),
            explanation: "first reason".into(),
        },
        IndexedSupport {
            chunk_id: second,
            document_path: "two".into(),
            quotation: "second passage".into(),
            explanation: "second reason".into(),
        },
    ];
    let serialized = serde_json::to_string(&citations)?;
    tx.execute("INSERT INTO public.mimir_belief_sources (belief_id, citations) VALUES ($1, $2::text::jsonb)", &[&belief, &serialized]).await?;
    let sources = source_observation::observe(&tx).await?;
    let found = sources
        .iter()
        .find(|row| row.key == belief)
        .expect("stored citations missing");
    assert_eq!(found.value, citations);
    let wire = serde_json::to_value(found)?;
    assert_eq!(wire["key"], belief.to_string());
    assert_eq!(wire["value"], serde_json::to_value(&citations)?);
    tx.rollback().await?;
    Ok(())
}

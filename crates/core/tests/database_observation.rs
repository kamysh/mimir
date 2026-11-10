#[allow(dead_code)]
#[path = "../../../tests/support/database_observation.rs"]
mod database_observation;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn combines_graph_learning_and_operation_records() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
    let weak = client.transaction().await?;
    assert!(database_observation::observe(&weak).await.is_err());
    weak.rollback().await?;
    let tx = client
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .start()
        .await?;
    let ids = tx
        .query_one("SELECT gen_random_uuid(),gen_random_uuid()", &[])
        .await?;
    let experience: Uuid = ids.get(0);
    let vector_owner: Uuid = ids.get(1);
    let token: Uuid = tx.query_one("INSERT INTO public.mimir_operation_reservations DEFAULT VALUES RETURNING operation_token", &[]).await?.get(0);
    tx.execute(
        "INSERT INTO public.mimir_experiences (id,project,revision) VALUES ($1,'combined-test',1)",
        &[&experience],
    )
    .await?;
    let vector = pgvector::Vector::from(vec![0.5_f32]);
    tx.execute(
        "INSERT INTO public.belief_embeddings (belief_id,embedding) VALUES ($1,$2)",
        &[&vector_owner, &vector],
    )
    .await?;
    let observed = database_observation::observe(&tx).await?;
    assert!(observed
        .graph
        .vectors
        .belief_vectors
        .iter()
        .any(|row| row.id == vector_owner));
    assert!(observed
        .learning
        .history
        .heads
        .iter()
        .any(|row| row.identity == experience));
    assert!(observed
        .operations
        .reservations
        .iter()
        .any(|row| row.token == token));
    tx.rollback().await?;
    Ok(())
}

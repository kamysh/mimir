#[path = "../../../tests/support/grounding_observation.rs"]
mod grounding_observation;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_grounding_without_vectors_or_sources() -> Result<()> {
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
    let chunk: Uuid = ids.get(0);
    let belief: Uuid = ids.get(1);
    let graph = database.dbname.replace('\'', "''");
    let create = format!(
        r#"SELECT * FROM ag_catalog.cypher('{graph}', $$
      CREATE (c:DocumentChunk {{id: '{chunk}'}}), (b:Belief {{id: '{belief}'}}), (c)-[:GROUNDS {{weight: 0.625}}]->(b)
      RETURN c.id $$) AS (id ag_catalog.agtype)"#
    );
    tx.query(&create, &[]).await?;
    let grounds = grounding_observation::observe(&tx).await?;
    assert!(grounds.contains(&grounding_observation::Ground {
        chunk,
        belief,
        weight: 0.625
    }));
    let counts = tx.query_one("SELECT (SELECT count(*) FROM public.chunk_embeddings WHERE chunk_id = $1), (SELECT count(*) FROM public.belief_embeddings WHERE belief_id = $2), (SELECT count(*) FROM public.mimir_belief_sources WHERE belief_id = $2)", &[&chunk, &belief]).await?;
    assert_eq!(
        (
            counts.get::<_, i64>(0),
            counts.get::<_, i64>(1),
            counts.get::<_, i64>(2)
        ),
        (0, 0, 0)
    );
    tx.rollback().await?;
    Ok(())
}

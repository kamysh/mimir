#[path = "../../../tests/support/chunk_observation.rs"]
mod chunk_observation;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_chunks_even_without_vectors() -> Result<()> {
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
    let id: Uuid = ids.get(0);
    let parent: Uuid = ids.get(1);
    let graph = database.dbname.replace('\'', "''");
    let create = format!(
        r#"SELECT * FROM ag_catalog.cypher('{graph}', $$
      CREATE (c:DocumentChunk {{id: '{id}', documentPath: 'notes/example', sectionPath: ['First', 'Second'], content: 'Full passage', parentId: '{parent}', project: 'observation-test'}})
      RETURN c.id $$) AS (id ag_catalog.agtype)"#
    );
    tx.query(&create, &[]).await?;
    let chunks = chunk_observation::observe(&tx).await?;
    let observed = chunks
        .iter()
        .find(|chunk| chunk.identity == id)
        .expect("chunk missing from observation");
    assert_eq!(observed.document, "notes/example");
    assert_eq!(observed.section, ["First", "Second"]);
    assert_eq!(observed.content, "Full passage");
    assert_eq!(observed.parent, Some(parent));
    assert_eq!(observed.project.as_deref(), Some("observation-test"));
    let vectors: i64 = tx
        .query_one(
            "SELECT count(*) FROM public.chunk_embeddings WHERE chunk_id = $1",
            &[&id],
        )
        .await?
        .get(0);
    assert_eq!(vectors, 0);
    tx.rollback().await?;
    Ok(())
}

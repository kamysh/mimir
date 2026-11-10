#[allow(dead_code)]
#[path = "../../../tests/support/graph_observation.rs"]
mod graph_observation;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::{db, preparation::IndexedSupport};
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn combines_graph_and_vector_rows_from_one_view() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
    let weak = client.transaction().await?;
    assert!(graph_observation::observe(&weak).await.is_err());
    weak.rollback().await?;
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
    let other: Uuid = ids.get(1);
    let chunk: Uuid = ids.get(2);
    let graph = database.dbname.replace('\'', "''");
    let create = format!(
        r#"SELECT * FROM ag_catalog.cypher('{graph}', $$
      CREATE (b:Belief {{id:'{belief}', content:'belief', memory_type:'Fact',
        created_at:'2026-01-01T00:00:00Z', last_activated_at:'2026-01-01T00:00:00Z', decay_accounted_at:'2026-01-01T00:00:00Z',
        probability:0.5, confidence:0.5, alpha:1.0, beta:1.0, alpha0:1.0, beta0:1.0}}),
      (a:Belief {{id:'{other}', content:'other', memory_type:'Fact',
        created_at:'2026-01-01T00:00:00Z', last_activated_at:'2026-01-01T00:00:00Z', decay_accounted_at:'2026-01-01T00:00:00Z',
        probability:0.5, confidence:0.5, alpha:1.0, beta:1.0, alpha0:1.0, beta0:1.0}}),
      (c:DocumentChunk {{id:'{chunk}', documentPath:'doc', sectionPath:['section'], content:'passage'}}),
      (c)-[:GROUNDS {{weight:0.5}}]->(b), (a)-[:SUPPORTS {{weight:0.75}}]->(b)
      RETURN b.id $$) AS (id ag_catalog.agtype)"#
    );
    tx.query(&create, &[]).await?;
    let vector = pgvector::Vector::from(vec![0.25_f32]);
    tx.execute(
        "INSERT INTO public.belief_embeddings (belief_id, embedding) VALUES ($1, $2)",
        &[&belief, &vector],
    )
    .await?;
    let citation = IndexedSupport {
        chunk_id: chunk,
        document_path: "doc".into(),
        quotation: "passage".into(),
        explanation: "supports it".into(),
    };
    let citations = serde_json::to_string(&vec![citation])?;
    tx.execute("INSERT INTO public.mimir_belief_sources (belief_id, citations) VALUES ($1, $2::text::jsonb)", &[&belief, &citations]).await?;

    let observed = graph_observation::observe(&tx).await?;
    assert!(observed
        .nodes
        .beliefs
        .iter()
        .any(|row| row.identity == belief));
    assert!(observed
        .belief_metadata
        .iter()
        .any(|row| row.identity == belief));
    assert!(observed.chunks.iter().any(|row| row.identity == chunk));
    assert!(observed
        .belief_links
        .iter()
        .any(|row| row.from == other && row.to == belief));
    assert!(observed
        .grounds
        .iter()
        .any(|row| row.chunk == chunk && row.belief == belief));
    assert!(observed
        .sources
        .iter()
        .any(|row| row.key == belief && row.value.len() == 1));
    assert!(observed
        .vectors
        .belief_vectors
        .iter()
        .any(|row| row.id == belief));
    assert!(!observed
        .vectors
        .chunk_vectors
        .iter()
        .any(|row| row.id == chunk));
    tx.rollback().await?;
    Ok(())
}

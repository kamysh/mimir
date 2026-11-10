#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
#[path = "../../../tests/support/node_observation.rs"]
mod node_observation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_stored_belief_values_and_patterns_without_vectors() -> Result<()> {
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
    let pattern: Uuid = ids.get(1);
    let graph = database.dbname.replace('\'', "''");
    let create = format!(
        r#"SELECT * FROM ag_catalog.cypher('{graph}', $$
      CREATE (b:Belief {{id:'{belief}', content:'original belief', project:'node-test', memory_type:'Fact',
        created_at:'2026-01-01T00:00:00Z', last_activated_at:'2026-01-02T00:00:00Z', decay_accounted_at:'2026-01-03T00:00:00Z',
        probability:0.4, confidence:0.3, alpha:7.0, beta:2.0, alpha0:1.5, beta0:1.25}}),
      (p:Pattern {{id:'{pattern}', situation:'situation', approach:'approach', project:'node-test',
        created_at:'2026-01-04T00:00:00Z', activation_count:3, success_rate:0.75}})
      RETURN b.id $$) AS (id ag_catalog.agtype)"#
    );
    tx.query(&create, &[]).await?;
    let nodes = node_observation::observe(&tx).await?;
    let b = nodes
        .beliefs
        .iter()
        .find(|row| row.identity == belief)
        .expect("belief missing");
    assert_eq!(
        (b.content.as_str(), b.project.as_deref(), b.memory.as_str()),
        ("original belief", Some("node-test"), "Fact")
    );
    assert_eq!(
        (
            b.probability,
            b.confidence,
            b.alpha,
            b.beta,
            b.alpha0,
            b.beta0
        ),
        (0.4, 0.3, 7.0, 2.0, 1.5, 1.25)
    );
    assert_eq!(b.created.to_rfc3339(), "2026-01-01T00:00:00+00:00");
    let wire = serde_json::to_value(b)?;
    assert_eq!(wire["identity"], belief.to_string());
    assert_eq!(wire["probability"], serde_json::json!(0.4));
    assert!(wire.get("decayAccountedAt").is_some());
    assert_eq!(b.activated.to_rfc3339(), "2026-01-02T00:00:00+00:00");
    assert_eq!(
        b.decay_accounted_at.to_rfc3339(),
        "2026-01-03T00:00:00+00:00"
    );
    let p = nodes
        .patterns
        .iter()
        .find(|row| row.identity == pattern)
        .expect("pattern missing");
    assert_eq!(
        (
            p.situation.as_str(),
            p.approach.as_str(),
            p.project.as_deref()
        ),
        ("situation", "approach", Some("node-test"))
    );
    assert_eq!((p.activation_count, p.success_rate), (3, 0.75));
    assert_eq!(p.created.to_rfc3339(), "2026-01-04T00:00:00+00:00");
    let vectors: i64 = tx
        .query_one(
            "SELECT count(*) FROM public.belief_embeddings WHERE belief_id=$1",
            &[&belief],
        )
        .await?
        .get(0);
    assert_eq!(vectors, 0);
    tx.rollback().await?;
    Ok(())
}

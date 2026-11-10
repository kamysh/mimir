#[path = "../../../tests/support/belief_metadata_observation.rs"]
mod belief_metadata_observation;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_provenance_and_retirement_without_guessing_legacy_values() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
    let tx = client
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .start()
        .await?;
    let ids = tx
        .query_one("SELECT gen_random_uuid(),gen_random_uuid()", &[])
        .await?;
    let dated: Uuid = ids.get(0);
    let legacy: Uuid = ids.get(1);
    let graph = database.dbname.replace('\'', "''");
    let create = format!(
        r#"SELECT * FROM ag_catalog.cypher('{graph}', $$
      CREATE (a:Belief {{id:'{dated}',origin_basis:'user_instruction',origin_reference:'original source',first_defeated_at:'2026-01-01T00:00:00Z'}}),
      (b:Belief {{id:'{legacy}',legacy_defeat_expired:true}}) RETURN a.id $$) AS (id ag_catalog.agtype)"#
    );
    tx.query(&create, &[]).await?;
    let rows = belief_metadata_observation::observe(&tx).await?;
    let first = rows
        .iter()
        .find(|row| row.identity == dated)
        .expect("dated belief missing");
    assert_eq!(
        first.origin_basis_raw.as_deref(),
        Some("\"user_instruction\"")
    );
    assert_eq!(
        first.origin_reference_raw.as_deref(),
        Some("\"original source\"")
    );
    assert_eq!(
        first.first_defeated_at_raw.as_deref(),
        Some("\"2026-01-01T00:00:00Z\"")
    );
    assert_eq!(first.legacy_defeat_expired_raw, None);
    let second = rows
        .iter()
        .find(|row| row.identity == legacy)
        .expect("legacy belief missing");
    assert_eq!(second.origin_basis_raw, None);
    assert_eq!(second.first_defeated_at_raw, None);
    assert_eq!(second.legacy_defeat_expired_raw.as_deref(), Some("true"));
    tx.rollback().await?;
    Ok(())
}

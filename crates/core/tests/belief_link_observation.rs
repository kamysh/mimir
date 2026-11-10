#[path = "../../../tests/support/belief_link_observation.rs"]
mod belief_link_observation;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::{db, graph::EdgeType};
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_both_owned_and_independent_parallel_links() -> Result<()> {
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
    let source: Uuid = ids.get(0);
    let target: Uuid = ids.get(1);
    let owner: Uuid = ids.get(2);
    let graph = database.dbname.replace('\'', "''");
    let create = format!(
        r#"SELECT * FROM ag_catalog.cypher('{graph}', $$
      CREATE (a:Belief {{id: '{source}'}}), (b:Belief {{id: '{target}'}}),
        (a)-[:SUPPORTS {{weight: 0.5}}]->(b),
        (a)-[:SUPPORTS {{weight: 0.5, experience_id: '{owner}'}}]->(b)
      RETURN a.id $$) AS (id ag_catalog.agtype)"#
    );
    tx.query(&create, &[]).await?;
    let links = belief_link_observation::observe(&tx).await?;
    let relevant: Vec<_> = links
        .iter()
        .filter(|link| link.from == source && link.to == target)
        .collect();
    assert_eq!(relevant.len(), 2);
    assert!(relevant.iter().any(|link| link.owner == None
        && link.relation == EdgeType::Supports
        && link.weight == 0.5));
    assert!(relevant.iter().any(|link| link.owner == Some(owner)
        && link.relation == EdgeType::Supports
        && link.weight == 0.5));
    tx.rollback().await?;
    Ok(())
}

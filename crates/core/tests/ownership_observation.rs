#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
#[path = "../../../tests/support/ownership_observation.rs"]
mod ownership_observation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_keyed_and_legacy_item_owners() -> Result<()> {
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
    let experience: Uuid = ids.get(0);
    let keyed: Uuid = ids.get(1);
    let legacy: Uuid = ids.get(2);
    tx.execute(
        "INSERT INTO public.mimir_experiences (id, project, revision) VALUES ($1, 'owner-test', 1)",
        &[&experience],
    )
    .await?;
    tx.execute("INSERT INTO public.mimir_learning_item_owners (item_id, experience_id, source_ref, actor, item_key) VALUES ($1, $3, 'source one', 'agent one', 'local-key'), ($2, $3, 'older source', 'agent two', NULL)", &[&keyed, &legacy, &experience]).await?;
    let rows = ownership_observation::observe(&tx).await?;
    assert!(rows.contains(&ownership_observation::ItemOwner {
        identity: keyed,
        experience,
        source_ref: "source one".into(),
        actor: "agent one".into(),
        item_key: Some("local-key".into())
    }));
    assert!(rows.contains(&ownership_observation::ItemOwner {
        identity: legacy,
        experience,
        source_ref: "older source".into(),
        actor: "agent two".into(),
        item_key: None
    }));
    tx.rollback().await?;
    Ok(())
}

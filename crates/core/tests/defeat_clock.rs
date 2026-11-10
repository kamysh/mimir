//! First defeat dates are server observations, not source creation proxies.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::Result;
use chrono::{Duration, TimeZone, Utc};
use mimir_core::{
    config::Config,
    db,
    graph::{Belief, Edge, EdgeType, MemoryType},
    store::*,
    MimirService,
};
use serde_json::json;
use uuid::Uuid;

fn config(hours: Option<f64>) -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: hours.map(|hours| {
            let mut value = toml::Table::new();
            value.insert("grace_hours".into(), toml::Value::Float(hours));
            toml::Value::Table(value)
        }),
    }
}
async fn store() -> Result<AgeStore> {
    let cfg = config(None);
    AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)
}
async fn identity() -> Result<Uuid> {
    Ok(db::connect(&config(None).database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0))
}
async fn belief(store: &AgeStore, project: &str, low: bool) -> Result<Belief> {
    let now = Utc.timestamp_opt(0, 0).unwrap();
    let belief = Belief::from_stored(
        identity().await?,
        "dated defeat fixture".into(),
        if low { 1.0 } else { 99.0 },
        if low { 99.0 } else { 1.0 },
        1.0,
        1.0,
        now,
        now,
        now,
        MemoryType::Fact,
        Some(project.into()),
    )?;
    store.insert_belief(&belief).await?;
    Ok(belief)
}
async fn raw_edge(from: Uuid, to: Uuid) -> Result<()> {
    let cfg = config(None);
    db::connect(&cfg.database).await?.query(&format!(
        "SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (a:Belief {{id:'{from}'}}),(b:Belief {{id:'{to}'}}) CREATE (a)-[:DEFEATS {{weight:1.0}}]->(b) RETURN b.id $$) AS (id ag_catalog.agtype)", cfg.database.dbname), &[]).await?;
    Ok(())
}

#[tokio::test]
async fn first_server_date_survives_later_defeats_and_saved_step_replay() -> Result<()> {
    let service = MimirService::connect(&config(Some(24.0))).await?;
    let store = store().await?;
    let project = format!("first-defeat-{}", identity().await?);
    let source = belief(&store, &project, false).await?;
    let later = belief(&store, &project, false).await?;
    let target = belief(&store, &project, true).await?;
    let audit = db::connect(&config(None).database).await?;
    let before: chrono::DateTime<Utc> = audit
        .query_one("SELECT clock_timestamp()", &[])
        .await?
        .get(0);
    let reserved = service
        .reserve_operation(&identity().await?.to_string())
        .await?;
    let request = OperationBindingRequest::new(
        "record_defeat".into(),
        json!({"from_id":source.id,"to_id":target.id,"weight":1.0}),
        json!({}),
    )?;
    service
        .bind_operation_request(reserved.operation_token, &request)
        .await?;
    let PlanDecision::Ready(plan) = service
        .prepare_operation(reserved.operation_token, &request, |_, _| {
            Box::pin(async { Ok(vec![]) })
        })
        .await?
    else {
        panic!("ready plan")
    };
    let first = plan.steps().remove(0);
    let original = store.commit_defeat_step(&first).await?;
    let after: chrono::DateTime<Utc> = audit
        .query_one("SELECT clock_timestamp()", &[])
        .await?
        .get(0);
    let edges = store
        .get_defeats_with_timestamps_by_project(&project)
        .await?;
    let DefeatClock::Recorded(received) = edges[0].2 else {
        panic!("new defeat cannot be legacy")
    };
    assert!(received >= before && received <= after);
    assert!(received > source.created_at + Duration::days(1));
    assert_eq!(store.commit_defeat_step(&first).await?, original);
    store
        .insert_edge(&Edge::new(later.id, target.id, EdgeType::Defeats, 1.0)?)
        .await?;
    let edges = store
        .get_defeats_with_timestamps_by_project(&project)
        .await?;
    assert_eq!(edges.len(), 2);
    assert!(edges
        .iter()
        .all(|(_, _, clock)| *clock == DefeatClock::Recorded(received)));
    assert_eq!(
        service.sweep_expired_defeated(0.3, Some(&project)).await?,
        0,
        "old source creation must not bypass a new grace period"
    );
    assert!(store.get_belief(target.id).await?.is_some());
    store.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn missing_post_upgrade_metadata_requires_repair_without_deletion_or_reset() -> Result<()> {
    let service = MimirService::connect(&config(Some(0.0))).await?;
    let store = store().await?;
    let project = format!("missing-defeat-clock-{}", identity().await?);
    let source = belief(&store, &project, false).await?;
    let target = belief(&store, &project, true).await?;
    raw_edge(source.id, target.id).await?;
    let error = store
        .get_defeats_with_timestamps_by_project(&project)
        .await
        .unwrap_err();
    assert!(format!("{error:#}").contains("user dialog"));
    assert!(service
        .sweep_expired_defeated(0.3, Some(&project))
        .await
        .is_err());
    assert!(store
        .insert_edge(&Edge::new(source.id, target.id, EdgeType::Defeats, 1.0)?)
        .await
        .is_err());
    assert!(store.get_belief(target.id).await?.is_some());
    assert!(
        store
            .get_defeats_with_timestamps_by_project(&project)
            .await
            .is_err(),
        "a later write must not manufacture a new date or legacy marker"
    );
    let audit = db::connect(&config(None).database).await?;
    audit.query(&format!("SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (n:Belief {{id:'{}'}}) SET n.legacy_defeat_expired='true' RETURN n.id $$) AS (id ag_catalog.agtype)",config(None).database.dbname,target.id),&[]).await?;
    let wrong_type = store
        .get_defeats_with_timestamps_by_project(&project)
        .await
        .unwrap_err();
    assert!(wrong_type
        .downcast_ref::<RetirementMetadataIssue>()
        .is_some());
    assert!(wrong_type.to_string().contains(&target.id.to_string()));
    assert!(service
        .sweep_expired_defeated(0.3, Some(&project))
        .await
        .is_err());
    assert!(
        store.get_belief(target.id).await?.is_some(),
        "a string marker cannot grant legacy expiry"
    );
    store.delete_project(&project).await?;
    Ok(())
}

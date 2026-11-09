//! Stored evidence must be admitted before clamped display values can hide it.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::Result;
use chrono::{TimeZone, Utc};
use mimir_core::{
    config::Config,
    db,
    graph::{Belief, Edge, EdgeType, MemoryType, StoredBeliefIssue},
    store::*,
    MimirService,
};
use uuid::Uuid;

fn config() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: Some(toml::Value::Table(toml::Table::from_iter([(
            "grace_hours".into(),
            toml::Value::Float(0.0),
        )]))),
    }
}
async fn identity() -> Result<Uuid> {
    Ok(db::connect(&config().database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0))
}
async fn store() -> Result<AgeStore> {
    let cfg = config();
    AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)
}
async fn node(store: &AgeStore, project: &str, low: bool) -> Result<Uuid> {
    let old = Utc.timestamp_opt(0, 0).unwrap();
    let (a, b) = if low { (1.0, 99.0) } else { (99.0, 1.0) };
    let belief = Belief::from_stored(
        identity().await?,
        "owned count-admission fixture".into(),
        a,
        b,
        a,
        b,
        old,
        old,
        old,
        MemoryType::Fact,
        Some(project.into()),
    )?;
    store.insert_belief(&belief).await?;
    Ok(belief.id)
}
async fn properties(id: Uuid, change: &str) -> Result<()> {
    db::connect(&config().database).await?.query(&format!(
        "SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (n:Belief {{id:'{id}'}}) {change} RETURN n.id $$) AS(id ag_catalog.agtype)",config().database.dbname),&[]).await?;
    Ok(())
}
fn reconstructed(id: Uuid, current: (f64, f64), prior: (f64, f64)) -> Result<Belief> {
    let old = Utc.timestamp_opt(0, 0).unwrap();
    Belief::from_stored(
        id,
        "stored-count boundary".into(),
        current.0,
        current.1,
        prior.0,
        prior.1,
        old,
        old,
        old,
        MemoryType::Fact,
        None,
    )
}

#[test]
fn reconstruction_refuses_invalid_current_and_original_counts_without_forbidding_empty_evidence() {
    let id = Uuid::nil();
    for (current, prior, field) in [
        ((-1.0, 1.0), (1.0, 1.0), "alpha"),
        ((1.0, -1.0), (1.0, 1.0), "beta"),
        ((1.0, 1.0), (-1.0, 1.0), "alpha0"),
        ((1.0, 1.0), (1.0, -1.0), "beta0"),
        ((f64::NAN, 1.0), (1.0, 1.0), "alpha"),
        ((1.0, f64::INFINITY), (1.0, 1.0), "beta"),
        ((1.0, 1.0), (f64::NEG_INFINITY, 1.0), "alpha0"),
        ((f64::MAX, f64::MAX), (1.0, 1.0), "alpha"),
        ((1.0, 1.0), (f64::MAX, f64::MAX), "alpha0"),
    ] {
        let error = reconstructed(id, current, prior).unwrap_err();
        let issue = error
            .downcast_ref::<StoredBeliefIssue>()
            .expect("identified stored-value diagnostic");
        assert_eq!(issue.belief_id(), id);
        assert_eq!(issue.field(), field);
        assert!(issue.issue().suggested_correction().contains("user"));
        assert!(issue
            .issue()
            .suggested_correction()
            .contains("Do not clamp"));
    }
    let empty = reconstructed(id, (0.0, 0.0), (0.0, 0.0)).unwrap();
    assert_eq!(empty.probability.value(), 0.5);
    assert_eq!(empty.confidence.value(), 0.0);
    assert!(
        reconstructed(id, (f64::MAX, 0.0), (0.0, f64::MAX)).is_ok(),
        "finite nonnegative evidence has no invented quota"
    );
}

#[tokio::test]
async fn extended_and_simple_rows_reject_present_bad_counts_but_preserve_absent_legacy_fallback(
) -> Result<()> {
    let store = store().await?;
    let project = format!("stored-row-counts-{}", identity().await?);
    let id = node(&store, &project, false).await?;
    for value in ["-1.0", "'broken'", "'NaN'"] {
        properties(id, &format!("SET n.alpha0={value}")).await?;
        for error in [
            store.get_belief(id).await.unwrap_err(),
            store.list_beliefs_by_project(&project).await.unwrap_err(),
        ] {
            let issue = error
                .downcast_ref::<StoredBeliefIssue>()
                .expect("both row adapters retain typed source");
            assert_eq!(issue.belief_id(), id);
            assert_eq!(issue.field(), "alpha0");
        }
    }
    properties(id, "SET n.alpha0=99.0 REMOVE n.alpha").await?;
    let decoded = store.get_belief(id).await?.unwrap();
    assert_eq!(
        decoded.alpha, decoded.alpha0,
        "absence alone keeps the explicit legacy rule"
    );
    for (field, value) in [("probability", "2.0"), ("confidence", "-1.0")] {
        properties(id, &format!("SET n.{field}={value}")).await?;
        let error = store.get_belief(id).await.unwrap_err();
        let issue = error.downcast_ref::<StoredBeliefIssue>().unwrap();
        assert_eq!(issue.field(), field);
        properties(id, &format!("SET n.{field}=0.5")).await?;
    }
    store.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn invalid_original_prior_blocks_the_whole_sweep_before_a_business_answer() -> Result<()> {
    let service = MimirService::connect(&config()).await?;
    let store = store().await?;
    let project = format!("stored-sweep-counts-{}", identity().await?);
    let source = node(&store, &project, false).await?;
    let first = node(&store, &project, true).await?;
    let second = node(&store, &project, true).await?;
    for target in [first, second] {
        store
            .insert_edge(&Edge::new(source, target, EdgeType::Defeats, 1.0)?)
            .await?;
        store.insert_belief_embedding(target, &[1.0, 0.0]).await?;
    }
    let other = format!("{project}-survivor");
    let child = node(&store, &other, false).await?;
    store
        .insert_edge(&Edge::new(first, child, EdgeType::Supports, 1.0)?)
        .await?;
    properties(child, "SET n.alpha0=-1.0").await?;
    let token = service
        .reserve_operation(&identity().await?.to_string())
        .await?
        .operation_token;
    let error = service
        .sweep_operation(token, 0.3, Some(&project))
        .await
        .unwrap_err();
    let issue = error
        .downcast_ref::<StoredBeliefIssue>()
        .expect("corrupt prior opens the repair path");
    assert_eq!(issue.belief_id(), child);
    assert_eq!(issue.field(), "alpha0");
    let audit = db::connect(&config().database).await?;
    let graph = &config().database.dbname;
    let rows=audit.query(&format!("SELECT id::text FROM ag_catalog.cypher('{graph}', $$ MATCH (n:Belief) WHERE n.project='{project}' RETURN n.id $$) AS(id ag_catalog.agtype)"),&[]).await?;
    assert_eq!(
        rows.len(),
        3,
        "no target can disappear before the invalid prior is resolved"
    );
    let vectors: i64 = audit
        .query_one(
            "SELECT count(*) FROM belief_embeddings WHERE belief_id=ANY($1)",
            &[&vec![first, second]],
        )
        .await?
        .get(0);
    assert_eq!(vectors, 2);
    let answers: i64 = audit
        .query_one(
            "SELECT count(*) FROM mimir_operation_step_replies WHERE operation_token=$1",
            &[&token],
        )
        .await?
        .get(0);
    assert_eq!(answers, 0);
    let retained=audit.query(&format!("SELECT a::text FROM ag_catalog.cypher('{graph}', $$ MATCH (a:Belief {{id:'{first}'}})-[:SUPPORTS]->(b:Belief {{id:'{child}'}}) RETURN a.id $$) AS(a ag_catalog.agtype)"),&[]).await?;
    assert_eq!(
        retained.len(),
        1,
        "preview deletion must not strand the survivor's incoming edge"
    );
    properties(child, "SET n.alpha0=99.0").await?;
    let OperationOutcome::Completed { outcome, .. } =
        service.sweep_operation(token, 0.3, Some(&project)).await?
    else {
        panic!("repaired pending work completes")
    };
    assert_eq!(outcome.reply()["deleted"], 2);
    store.delete_project(&project).await?;
    store.delete_project(&other).await?;
    Ok(())
}

#[tokio::test]
async fn invalid_proposed_counts_cannot_partially_update_a_batch_and_zero_counts_remain_usable(
) -> Result<()> {
    let store = store().await?;
    let project = format!("proposed-counts-{}", identity().await?);
    let first = node(&store, &project, false).await?;
    let second = node(&store, &project, false).await?;
    let before = store.get_belief(first).await?.unwrap();
    for pair in [(-1.0, 1.0), (f64::INFINITY, 1.0), (f64::MAX, f64::MAX)] {
        let error = store
            .update_beliefs_beta(&[(first, 7.0, 3.0), (second, pair.0, pair.1)])
            .await
            .unwrap_err();
        assert!(error
            .downcast_ref::<mimir_core::validation::Refusal>()
            .is_some());
        let current = store.get_belief(first).await?.unwrap();
        assert_eq!((current.alpha, current.beta), (before.alpha, before.beta));
    }
    let mut invalid = store.get_belief(first).await?.unwrap();
    invalid.id = identity().await?;
    invalid.alpha0 = -1.0;
    assert!(store.insert_belief(&invalid).await.is_err());
    assert!(store.get_belief(invalid.id).await?.is_none());
    store.update_beliefs_beta(&[(first, 0.0, 0.0)]).await?;
    let empty = store.get_belief(first).await?.unwrap();
    assert_eq!((empty.alpha, empty.beta), (0.0, 0.0));
    assert_eq!(empty.probability.value(), 0.5);
    store.delete_project(&project).await?;
    Ok(())
}

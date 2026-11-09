//! A sweep publishes its complete selected set and original answer together.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use chrono::{TimeZone, Utc};
use mimir_core::{
    config::Config,
    db,
    graph::{Belief, Edge, EdgeType, MemoryType},
    store::*,
    MimirService,
};
use serde_json::{json, Value};
use uuid::Uuid;

fn config(hours: Option<f64>) -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: hours.map(|hours| {
            toml::Value::Table(toml::Table::from_iter([(
                "grace_hours".into(),
                toml::Value::Float(hours),
            )]))
        }),
    }
}
async fn identity() -> Result<Uuid> {
    Ok(db::connect(&config(None).database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0))
}
async fn store() -> Result<AgeStore> {
    let cfg = config(None);
    AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)
}
async fn node(store: &AgeStore, project: &str, low: bool) -> Result<Uuid> {
    let old = Utc.timestamp_opt(0, 0).unwrap();
    let (alpha, beta) = if low { (1.0, 99.0) } else { (99.0, 1.0) };
    let belief = Belief::from_stored(
        identity().await?,
        "owned sweep fixture".into(),
        alpha,
        beta,
        alpha,
        beta,
        old,
        old,
        old,
        MemoryType::Fact,
        Some(project.into()),
    )?;
    store.insert_belief(&belief).await?;
    Ok(belief.id)
}
async fn target(store: &AgeStore, project: &str, source: Uuid) -> Result<Uuid> {
    let id = node(store, project, true).await?;
    store
        .insert_edge(&Edge::new(source, id, EdgeType::Defeats, 1.0)?)
        .await?;
    store.insert_belief_embedding(id, &[1.0, 0.0]).await?;
    Ok(id)
}
async fn token(service: &MimirService, project: &str) -> Result<(Uuid, OperationBindingRequest)> {
    let id = service
        .reserve_operation(&identity().await?.to_string())
        .await?
        .operation_token;
    let request = OperationBindingRequest::new(
        "sweep_expired_defeated".into(),
        json!({"prob_threshold":0.3,"project":project}),
        json!({"retirement":{"grace_hours":0.0}}),
    )?;
    service.bind_operation_request(id, &request).await?;
    Ok((id, request))
}
fn completed(outcome: OperationOutcome) -> Value {
    match outcome {
        OperationOutcome::Completed { outcome, .. } => outcome.reply().clone(),
        other => panic!("expected an acknowledged original completion, got {other:?}"),
    }
}
async fn vector_count(ids: &[Uuid]) -> Result<i64> {
    Ok(db::connect(&config(None).database)
        .await?
        .query_one(
            "SELECT count(*) FROM public.belief_embeddings WHERE belief_id=ANY($1)",
            &[&ids],
        )
        .await?
        .get(0))
}
async fn saved_count(token: Uuid) -> Result<i64> {
    Ok(db::connect(&config(None).database)
        .await?
        .query_one(
            "SELECT count(*) FROM mimir_operation_step_replies WHERE operation_token=$1",
            &[&token],
        )
        .await?
        .get(0))
}

#[tokio::test]
async fn whole_set_and_answer_commit_once_and_replay_before_current_policy() -> Result<()> {
    let service = MimirService::connect(&config(Some(0.0))).await?;
    let store = store().await?;
    let project = format!("sweep-whole-set-{}", identity().await?);
    let source = node(&store, &project, false).await?;
    let first = target(&store, &project, source).await?;
    let second = target(&store, &project, source).await?;
    let (token, _) = token(&service, &project).await?;
    let answer = completed(service.sweep_operation(token, 0.3, Some(&project)).await?);
    let mut expected = vec![first, second];
    expected.sort_unstable();
    assert_eq!(answer, json!({"deleted":2,"selected":expected}));
    assert!(store.get_belief(first).await?.is_none());
    assert!(store.get_belief(second).await?.is_none());
    assert!(store.get_belief(source).await?.is_some());
    assert_eq!(vector_count(&expected).await?, 0);
    assert_eq!(
        saved_count(token).await?,
        2,
        "business step and final answer share the publication"
    );
    let later = target(&store, &project, source).await?;
    for hours in [None, Some(48.0)] {
        let reloaded = MimirService::connect(&config(hours)).await?;
        assert_eq!(
            completed(reloaded.sweep_operation(token, 0.3, Some(&project)).await?),
            answer
        );
        assert!(
            store.get_belief(later).await?.is_some(),
            "historical replay cannot select newly eligible work"
        );
    }
    assert_eq!(saved_count(token).await?, 2);
    assert_eq!(vector_count(&[later]).await?, 1);
    store.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn changed_or_unset_policy_pauses_pending_work_and_restoration_resumes() -> Result<()> {
    let service = MimirService::connect(&config(Some(0.0))).await?;
    let store = store().await?;
    let project = format!("sweep-original-policy-{}", identity().await?);
    let source = node(&store, &project, false).await?;
    let selected = target(&store, &project, source).await?;
    let (token, request) = token(&service, &project).await?;
    for hours in [Some(48.0), None] {
        let reloaded = MimirService::connect(&config(hours)).await?;
        let error = reloaded
            .sweep_operation(token, 0.3, Some(&project))
            .await
            .unwrap_err();
        if hours.is_some() {
            assert!(
                error.downcast_ref::<SweepPolicyIssue>().is_some(),
                "{error:#}"
            );
        } else {
            assert!(
                error
                    .downcast_ref::<mimir_core::config::RetirementIssue>()
                    .is_some(),
                "{error:#}"
            );
        }
        assert!(store.get_belief(selected).await?.is_some());
        assert_eq!(vector_count(&[selected]).await?, 1);
        assert_eq!(saved_count(token).await?, 0);
        assert!(matches!(
            service
                .read_operation_outcome(token, Some(&request))
                .await?,
            OperationOutcome::AwaitingPlan(_)
        ));
    }
    assert_eq!(
        completed(service.sweep_operation(token, 0.3, Some(&project)).await?)["deleted"],
        1
    );
    assert!(store.get_belief(selected).await?.is_none());
    store.delete_project(&project).await?;
    Ok(())
}

async fn old_plan(token: Uuid, steps: Value, result: Option<Value>) -> Result<()> {
    let plan = json!({"operation":"sweep_expired_defeated","shape":[{"site":"store.delete_belief","may_repeat":true}],"steps":steps});
    let mut client = db::connect(&config(None).database).await?;
    let tx = client.transaction().await?;
    tx.execute(
        "INSERT INTO mimir_operation_plans(operation_token,plan) VALUES($1,$2::text::jsonb)",
        &[&token, &plan.to_string()],
    )
    .await?;
    if let Some(result) = result {
        tx.execute("INSERT INTO mimir_operation_step_replies(operation_token,step,reply) VALUES($1,'@operation-result',$2::text::jsonb)",&[&token,&result.to_string()]).await?;
    }
    tx.commit().await?;
    Ok(())
}

#[tokio::test]
async fn old_completed_answer_stays_readable_but_old_unfinished_plan_cannot_execute() -> Result<()>
{
    let service = MimirService::connect(&config(Some(0.0))).await?;
    let store = store().await?;
    let project = format!("sweep-old-plan-{}", identity().await?);
    let source = node(&store, &project, false).await?;
    let (finished, _) = token(&service, &project).await?;
    // The historical empty selection truly did no business work. A later
    // eligible target must not turn its saved count into a new deletion.
    old_plan(finished, json!([]), Some(json!({"deleted":0}))).await?;
    let selected = target(&store, &project, source).await?;
    let reloaded = MimirService::connect(&config(None)).await?;
    assert_eq!(
        completed(
            reloaded
                .sweep_operation(finished, 0.3, Some(&project))
                .await?
        ),
        json!({"deleted":0})
    );
    let (unfinished, request) = token(&service, &project).await?;
    let id = json!(["store.delete_belief", selected.to_string()]).to_string();
    old_plan(
        unfinished,
        json!([{"site":"store.delete_belief","key":selected.to_string(),"id":id}]),
        None,
    )
    .await?;
    let error = service
        .sweep_operation(unfinished, 0.3, Some(&project))
        .await
        .unwrap_err();
    ensure!(
        error
            .downcast_ref::<mimir_core::interaction::RequestCorrection>()
            .is_some(),
        "{error:#}"
    );
    assert!(
        format!("{error:#}").contains("earlier Mimir version"),
        "{error:#}"
    );
    assert!(matches!(
        service
            .read_operation_outcome(unfinished, Some(&request))
            .await?,
        OperationOutcome::Pending { .. }
    ));
    assert!(store.get_belief(selected).await?.is_some());
    assert_eq!(vector_count(&[selected]).await?, 1);
    assert_eq!(saved_count(unfinished).await?, 0);
    store.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn actual_repeated_survivor_counts_roll_back_every_selected_target_and_answer() -> Result<()>
{
    let service = MimirService::connect(&config(Some(0.0))).await?;
    let store = store().await?;
    let project = format!("sweep-rollback-{}", identity().await?);
    let other = format!("{project}-survivor");
    let source = node(&store, &project, false).await?;
    let first = target(&store, &project, source).await?;
    let second = target(&store, &project, source).await?;
    let mut cycle = Vec::new();
    for _ in 0..2 {
        let old = Utc.timestamp_opt(0, 0).unwrap();
        let belief = Belief::from_stored(
            identity().await?,
            "actual repeated count fixture".into(),
            0.2,
            1.8,
            0.2,
            1.8,
            old,
            old,
            old,
            MemoryType::Fact,
            Some(other.clone()),
        )?;
        store.insert_belief(&belief).await?;
        cycle.push(belief.id);
    }
    cycle.sort_unstable();
    let child = cycle[0];
    store
        .insert_edge(&Edge::new(cycle[1], cycle[0], EdgeType::Defeats, 0.7)?)
        .await?;
    store
        .insert_edge(&Edge::new(cycle[0], cycle[1], EdgeType::Supports, 1.0)?)
        .await?;
    store
        .insert_edge(&Edge::new(first, child, EdgeType::Supports, 1.0)?)
        .await?;
    let audit = db::connect(&config(None).database).await?;
    let (token, _) = token(&service, &project).await?;
    let error = service
        .sweep_operation(token, 0.3, Some(&project))
        .await
        .unwrap_err();
    assert!(
        error
            .downcast_ref::<mimir_core::inference::NumericalDecision>()
            .is_some(),
        "{error:#}"
    );
    for selected in [first, second] {
        assert!(store.get_belief(selected).await?.is_some());
    }
    assert_eq!(vector_count(&[first, second]).await?, 2);
    assert_eq!(saved_count(token).await?, 0);
    let rows=audit.query(&format!("SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (a:Belief {{id:'{first}'}})-[:SUPPORTS]->(b:Belief {{id:'{child}'}}) RETURN a.id $$) AS (id ag_catalog.agtype)",config(None).database.dbname),&[]).await?;
    assert_eq!(
        rows.len(),
        1,
        "rolled-back detach must retain outgoing edges"
    );
    store.delete_project(&other).await?;
    assert_eq!(
        completed(service.sweep_operation(token, 0.3, Some(&project)).await?)["deleted"],
        2
    );
    store.delete_project(&project).await?;
    Ok(())
}

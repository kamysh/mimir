//! Current counts retain their accounted time across writes and retries.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::Result;
use chrono::{DateTime, Duration, Utc};
use mimir_core::{
    config::Config,
    db,
    documents::DocumentChunk,
    graph::{Belief, MemoryType},
    store::*,
    MimirService,
};
use serde_json::{json, Value};
use uuid::Uuid;

fn config() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    }
}
async fn setup() -> Result<(AgeStore, MimirService)> {
    let service = MimirService::connect(&config()).await?;
    let cfg = config();
    Ok((
        AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)?,
        service,
    ))
}
async fn identity() -> Result<Uuid> {
    Ok(db::connect(&config().database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0))
}
async fn plan(
    service: &MimirService,
    token: Uuid,
    operation: &str,
    args: Value,
) -> Result<RegisteredStep> {
    let binding = OperationBindingRequest::new(operation.into(), args, json!({}))?;
    service.bind_operation_request(token, &binding).await?;
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &binding, |_, _| Box::pin(async { Ok(vec![]) }))
        .await?
    else {
        panic!("plan missing")
    };
    Ok(plan.steps().remove(0))
}
async fn reservation(service: &MimirService) -> Result<OperationReservation> {
    service
        .reserve_operation(&identity().await?.to_string())
        .await
}
async fn belief_at(
    store: &AgeStore,
    id: Uuid,
    time: DateTime<Utc>,
    project: &str,
    memory: MemoryType,
) -> Result<Belief> {
    let belief = Belief::from_stored(
        id,
        "time-accounted fact".into(),
        100.0,
        10.0,
        1.0,
        1.0,
        time,
        time,
        time,
        memory,
        Some(project.into()),
    )?;
    store.insert_belief(&belief).await?;
    Ok(belief)
}
async fn pending(service: &MimirService, token: Uuid, step: &RegisteredStep) -> Result<()> {
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    assert!(service
        .read_operation_step(token, "@operation-result")
        .await?
        .is_none());
    assert!(
        matches!(service.read_operation_outcome(token,None).await?,OperationOutcome::Pending{saved_replies,..} if saved_replies.is_empty())
    );
    Ok(())
}
async fn completed(service: &MimirService, step: &RegisteredStep) -> Result<StepReceipt> {
    let StepDecision::Done(answer) = service.decay_operation(step).await? else {
        panic!("completion missing")
    };
    assert_eq!(
        service
            .read_operation_step(answer.operation_token, "@operation-result")
            .await?
            .unwrap()
            .reply,
        answer.reply
    );
    Ok(answer)
}

#[tokio::test]
async fn different_tokens_at_one_time_charge_one_interval_and_retries_keep_original_answer(
) -> Result<()> {
    let (store, service) = setup().await?;
    let mut audit = db::connect(&config().database).await?;
    let tx = audit.transaction().await?;
    let mut tokens = vec![];
    for _ in 0..2 {
        let row=tx.query_one("INSERT INTO mimir_operation_reservations DEFAULT VALUES RETURNING operation_token,reserved_at",&[]).await?;
        let token: Uuid = row.get(0);
        let time: DateTime<Utc> = row.get(1);
        tx.execute(
            "INSERT INTO mimir_operation_request_keys(request_key,operation_token) VALUES($1,$2)",
            &[&format!("decay-clock-{token}"), &token],
        )
        .await?;
        tokens.push((token, time));
    }
    assert_eq!(tokens[0].1, tokens[1].1);
    tx.commit().await?;
    let time = tokens[0].1;
    let project = format!("decay-accounting-{}", identity().await?);
    let fact = belief_at(
        &store,
        identity().await?,
        time - Duration::days(1),
        &project,
        MemoryType::Fact,
    )
    .await?;
    let exempt = belief_at(
        &store,
        identity().await?,
        time - Duration::days(1),
        &project,
        MemoryType::Experiential,
    )
    .await?;
    let unrelated = belief_at(
        &store,
        identity().await?,
        time - Duration::days(1),
        &format!("other-{project}"),
        MemoryType::Fact,
    )
    .await?;
    let exempt_before = serde_json::to_value(store.get_belief(exempt.id).await?)?;
    let unrelated_before = serde_json::to_value(store.get_belief(unrelated.id).await?)?;
    let first = plan(
        &service,
        tokens[0].0,
        "decay_all",
        json!({"decay_factor":0.5,"project":project}),
    )
    .await?;
    let second = plan(
        &service,
        tokens[1].0,
        "decay_all",
        json!({"decay_factor":0.5,"project":project}),
    )
    .await?;
    let original = completed(&service, &first).await?;
    assert_eq!(original.reply, json!({"decayed":1}));
    let after = store.get_belief(fact.id).await?.unwrap();
    assert_eq!((after.alpha, after.beta), (50.5, 5.5));
    assert_eq!(after.decay_accounted_at, time);
    assert_eq!(after.last_activated_at, fact.last_activated_at);
    assert_eq!(
        completed(&service, &second).await?.reply,
        json!({"decayed":0})
    );
    assert_eq!(
        serde_json::to_value(store.get_belief(fact.id).await?)?,
        serde_json::to_value(Some(after))?
    );
    drop(service);
    let reopened = MimirService::connect(&config()).await?;
    assert_eq!(completed(&reopened, &first).await?, original);
    assert_eq!(
        serde_json::to_value(store.get_belief(exempt.id).await?)?,
        exempt_before
    );
    assert_eq!(
        serde_json::to_value(store.get_belief(unrelated.id).await?)?,
        unrelated_before
    );
    store.delete_project(&project).await?;
    store.delete_belief(unrelated.id).await?;
    Ok(())
}

#[tokio::test]
async fn final_answer_rejection_restores_counts_baseline_and_pending_status() -> Result<()> {
    let (store, service) = setup().await?;
    let reserved = reservation(&service).await?;
    let project = format!("decay-rollback-{}", reserved.operation_token);
    let belief = belief_at(
        &store,
        identity().await?,
        reserved.reserved_at - Duration::days(1),
        &project,
        MemoryType::Fact,
    )
    .await?;
    let before = serde_json::to_value(store.get_belief(belief.id).await?)?;
    let step = plan(
        &service,
        reserved.operation_token,
        "decay_all",
        json!({"decay_factor":0.5,"project":project}),
    )
    .await?;
    let audit = db::connect(&config().database).await?;
    let constraint = format!("reject_decay_{}", reserved.operation_token.simple());
    audit.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies ADD CONSTRAINT {constraint} CHECK (operation_token <> '{}'::uuid OR step <> '@operation-result') NOT VALID",reserved.operation_token)).await?;
    let attempted = service.decay_operation(&step).await;
    audit
        .batch_execute(&format!(
            "ALTER TABLE mimir_operation_step_replies DROP CONSTRAINT {constraint}"
        ))
        .await?;
    assert!(attempted.is_err());
    assert_eq!(
        serde_json::to_value(store.get_belief(belief.id).await?)?,
        before
    );
    pending(&service, reserved.operation_token, &step).await?;
    assert_eq!(
        completed(&service, &step).await?.reply,
        json!({"decayed":1})
    );
    let after = store.get_belief(belief.id).await?.unwrap();
    assert_eq!((after.alpha, after.beta), (50.5, 5.5));
    assert_eq!(after.decay_accounted_at, reserved.reserved_at);
    store.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn an_old_reserved_time_cannot_rewind_a_later_posterior_publication() -> Result<()> {
    let (store, service) = setup().await?;
    let reserved = reservation(&service).await?;
    let project = format!("decay-old-clock-{}", reserved.operation_token);
    let belief = belief_at(
        &store,
        identity().await?,
        reserved.reserved_at - Duration::days(1),
        &project,
        MemoryType::Fact,
    )
    .await?;
    let step = plan(
        &service,
        reserved.operation_token,
        "decay_all",
        json!({"decay_factor":0.5,"project":project}),
    )
    .await?;
    store.update_belief_beta(belief.id, 100.0, 10.0).await?;
    let current = store.get_belief(belief.id).await?.unwrap();
    assert!(current.decay_accounted_at >= reserved.reserved_at);
    assert_eq!(
        completed(&service, &step).await?.reply,
        json!({"decayed":0})
    );
    assert_eq!(
        serde_json::to_value(store.get_belief(belief.id).await?)?,
        serde_json::to_value(Some(current))?
    );
    store.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn grounding_publication_and_removal_reconcile_the_time_of_their_new_counts() -> Result<()> {
    let (store, service) = setup().await?;
    let reserved = reservation(&service).await?;
    let project = format!("decay-grounding-{}", reserved.operation_token);
    let belief = belief_at(
        &store,
        identity().await?,
        reserved.reserved_at - Duration::days(1),
        &project,
        MemoryType::Fact,
    )
    .await?;
    let chunk = DocumentChunk::with_id(
        identity().await?,
        format!("/mimir-test/{project}.md"),
        vec![],
        "Indexed supporting passage".into(),
        None,
        Some(project.clone()),
    );
    store.insert_document_chunk(&chunk).await?;
    let step = plan(
        &service,
        reserved.operation_token,
        "add_evidence",
        json!({"belief_id":belief.id,"chunk_id":chunk.id,"weight":1.0}),
    )
    .await?;
    assert!(matches!(
        service.change_evidence_operation(&step).await?,
        StepDecision::Done(_)
    ));
    let after = store.get_belief(belief.id).await?.unwrap();
    assert_eq!(after.decay_accounted_at, reserved.reserved_at);
    assert_eq!((after.alpha, after.beta), (2.0, 1.0));
    store.delete_evidence(chunk.id, belief.id).await?;
    let removed = store.get_belief(belief.id).await?.unwrap();
    assert!(removed.decay_accounted_at >= after.decay_accounted_at);
    assert_eq!((removed.alpha, removed.beta), (1.0, 1.0));
    store.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn migration_preserves_existing_counts_and_never_resets_an_existing_baseline() -> Result<()> {
    let (store, service) = setup().await?;
    let reserved = reservation(&service).await?;
    let project = format!("decay-migration-{}", reserved.operation_token);
    let belief = belief_at(
        &store,
        identity().await?,
        reserved.reserved_at - Duration::days(1),
        &project,
        MemoryType::Fact,
    )
    .await?;
    let retained = belief_at(
        &store,
        identity().await?,
        reserved.reserved_at - Duration::days(2),
        &project,
        MemoryType::Fact,
    )
    .await?;
    let retained_before = serde_json::to_value(store.get_belief(retained.id).await?)?;
    let audit = db::connect(&config().database).await?;
    audit.query(&format!("SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (n:Belief {{id:'{}'}}) SET n.decay_accounted_at = NULL RETURN n.id $$) AS (id ag_catalog.agtype)",config().database.dbname,belief.id),&[]).await?;
    let sql = include_str!("../migrations/020_decay_accounting.sql")
        .split_once(';')
        .unwrap()
        .1;
    audit.batch_execute(sql).await?;
    let after = store.get_belief(belief.id).await?.unwrap();
    assert_eq!(
        (after.alpha, after.beta, after.alpha0, after.beta0),
        (100.0, 10.0, 1.0, 1.0)
    );
    assert_eq!(after.created_at, belief.created_at);
    assert_eq!(after.last_activated_at, belief.last_activated_at);
    assert!(after.decay_accounted_at >= reserved.reserved_at);
    assert_eq!(
        serde_json::to_value(store.get_belief(retained.id).await?)?,
        retained_before
    );
    audit.batch_execute(sql).await?;
    assert_eq!(
        store
            .get_belief(belief.id)
            .await?
            .unwrap()
            .decay_accounted_at,
        after.decay_accounted_at
    );
    store.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn cancelled_or_malformed_decay_preserves_the_original_counts_and_baseline() -> Result<()> {
    let (store, service) = setup().await?;
    let reserved = reservation(&service).await?;
    let project = format!("decay-admission-{}", reserved.operation_token);
    let belief = belief_at(
        &store,
        identity().await?,
        reserved.reserved_at - Duration::days(1),
        &project,
        MemoryType::Fact,
    )
    .await?;
    let before = serde_json::to_value(store.get_belief(belief.id).await?)?;
    let step = plan(
        &service,
        reserved.operation_token,
        "decay_all",
        json!({"decay_factor":0.5,"project":project}),
    )
    .await?;
    let CancellationDecision::Recorded(cancellation) = service
        .record_operation_cancellation(reserved.operation_token)
        .await?
    else {
        panic!("cancellation missing")
    };
    assert_eq!(
        service.decay_operation(&step).await?,
        StepDecision::Cancelled(cancellation)
    );
    for args in [
        json!({"decay_factor":-0.1}),
        json!({"decay_factor":1.1}),
        json!({"decay_factor":"slow"}),
        json!({"unknown":17}),
    ] {
        let token = reservation(&service).await?.operation_token;
        let step = plan(&service, token, "decay_all", args).await?;
        assert!(service.decay_operation(&step).await.is_err());
        pending(&service, token, &step).await?;
    }
    assert_eq!(
        serde_json::to_value(store.get_belief(belief.id).await?)?,
        before
    );
    store.delete_project(&project).await?;
    Ok(())
}

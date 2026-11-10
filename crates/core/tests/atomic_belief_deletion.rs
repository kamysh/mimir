//! Registered belief deletion and its original answers share a commit.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::{
    config::Config,
    db,
    graph::{Belief, Edge, EdgeType, MemoryType},
    inference::NumericalDecision,
    learning::*,
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

async fn identity() -> Result<Uuid> {
    Ok(db::connect(&config().database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0))
}

async fn setup() -> Result<(AgeStore, MimirService)> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let store = AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)?;
    Ok((store, service))
}

async fn belief(store: &AgeStore, id: Uuid) -> Result<Belief> {
    let mut value = Belief::new_in_project(
        "owned deletion belief".into(),
        0.5,
        0.0,
        format!("belief-deletion-{id}"),
    )?
    .with_memory_type(MemoryType::Fact);
    value.id = id;
    store.insert_belief_with_provenance(&value, None).await?;
    Ok(value)
}

async fn admitted(
    service: &MimirService,
    operation: &str,
    arguments: Value,
) -> Result<(Uuid, RegisteredStep)> {
    let token = service
        .reserve_operation(&identity().await?.to_string())
        .await?
        .operation_token;
    let request = OperationBindingRequest::new(operation.into(), arguments, json!({}))?;
    service.bind_operation_request(token, &request).await?;
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &request, |_, _| Box::pin(async { Ok(vec![]) }))
        .await?
    else {
        panic!("registered plan missing")
    };
    let steps = plan.steps();
    assert_eq!(steps.len(), 1);
    Ok((token, steps[0].clone()))
}

async fn completed_reply(service: &MimirService, token: Uuid) -> Result<Value> {
    let OperationOutcome::Completed { outcome, .. } =
        service.read_operation_outcome(token, None).await?
    else {
        panic!("completed outcome missing")
    };
    Ok(outcome.reply().clone())
}

#[tokio::test]
async fn retry_after_reconnect_keeps_original_true_and_unrelated_records() -> Result<()> {
    let (store, service) = setup().await?;
    let removed = belief(&store, identity().await?).await?;
    let retained = belief(&store, identity().await?).await?;
    store
        .insert_belief_embedding(removed.id, &[0.3, 0.4])
        .await?;
    store
        .insert_belief_embedding(retained.id, &[0.6, 0.8])
        .await?;
    let child = belief(&store, identity().await?).await?;
    store
        .insert_edge(&Edge::new(removed.id, child.id, EdgeType::Supports, 1.0)?)
        .await?;
    service.propagate_from(removed.id).await?;
    assert!(store.get_belief(child.id).await?.unwrap().alpha > child.alpha0);
    let retained_before = mimir_json::to_value(store.get_belief(retained.id).await?)?;
    let (other_token, other_step) =
        admitted(&service, "delete_belief", json!({"id": identity().await?})).await?;
    let StepDecision::Done(other_reply) = service.delete_belief_operation(&other_step).await?
    else {
        panic!("unrelated original answer missing")
    };
    let (token, step) = admitted(&service, "delete_belief", json!({"id": removed.id})).await?;
    let not_before: chrono::DateTime<chrono::Utc> = db::connect(&config().database)
        .await?
        .query_one("SELECT clock_timestamp()", &[])
        .await?
        .get(0);
    let StepDecision::Done(first) = service.delete_belief_operation(&step).await? else {
        panic!("deletion missing")
    };
    assert_eq!(first.reply, json!({"deleted": true}));
    assert!(store.get_belief(removed.id).await?.is_none());
    let child_after = store.get_belief(child.id).await?.unwrap();
    assert!(child_after.decay_accounted_at >= not_before);
    assert_eq!(child_after.created_at, child.created_at);
    assert_eq!(child_after.last_activated_at, child.last_activated_at);
    assert_eq!(child_after.alpha.to_bits(), child.alpha0.to_bits());
    assert_eq!(child_after.beta.to_bits(), child.beta0.to_bits());
    let audit = db::connect(&config().database).await?;
    assert!(audit
        .query_opt(
            "SELECT 1 FROM belief_embeddings WHERE belief_id=$1",
            &[&removed.id]
        )
        .await?
        .is_none());
    assert!(audit
        .query_opt(
            "SELECT 1 FROM belief_embeddings WHERE belief_id=$1",
            &[&retained.id]
        )
        .await?
        .is_some());
    drop(service);
    let reopened = MimirService::connect(&config()).await?;
    let StepDecision::Done(retried) = reopened.delete_belief_operation(&step).await? else {
        panic!("saved answer missing")
    };
    assert_eq!(retried, first);
    assert_eq!(completed_reply(&reopened, token).await?, first.reply);
    assert_eq!(
        mimir_json::to_value(store.get_belief(retained.id).await?)?,
        retained_before
    );
    assert_eq!(
        reopened
            .read_operation_step(other_token, other_step.id())
            .await?,
        Some(other_reply)
    );
    assert_eq!(
        completed_reply(&reopened, other_token).await?,
        json!({"deleted":false})
    );
    store.delete_belief(retained.id).await?;
    store.delete_belief(child.id).await?;
    Ok(())
}

#[tokio::test]
async fn saved_false_does_not_delete_a_belief_created_after_completion() -> Result<()> {
    let (store, service) = setup().await?;
    let id = identity().await?;
    let (token, step) = admitted(&service, "delete_belief", json!({"id":id})).await?;
    let StepDecision::Done(first) = service.delete_belief_operation(&step).await? else {
        panic!("missing-belief result absent")
    };
    assert_eq!(first.reply, json!({"deleted":false}));
    belief(&store, id).await?;
    let before = mimir_json::to_value(store.get_belief(id).await?)?;
    let StepDecision::Done(retried) = service.delete_belief_operation(&step).await? else {
        panic!("saved missing-belief result absent")
    };
    assert_eq!(retried, first);
    assert_eq!(completed_reply(&service, token).await?, first.reply);
    assert_eq!(mimir_json::to_value(store.get_belief(id).await?)?, before);
    store.delete_belief(id).await?;
    Ok(())
}

#[tokio::test]
async fn rejected_final_result_rolls_back_deletion_retirement_and_step_answer() -> Result<()> {
    let (store, service) = setup().await?;
    let value = belief(&store, identity().await?).await?;
    store.insert_belief_embedding(value.id, &[0.3, 0.4]).await?;
    let source_id = identity().await?;
    service
        .record_experience(
            &Experience {
                id: source_id,
                project: value.project.clone().unwrap(),
                context: "owned belief deletion fixture".into(),
                action: "verify deletion and retirement commit together".into(),
                outcome: Outcome::Success,
                source: ObservationSource::ToolResult,
                evidence: vec!["private fixture".into()],
                belief_ids: vec![value.id],
                pattern_id: None,
                learning_items: vec![],
                source_records: vec![],
            },
            0,
        )
        .await?;
    let audit = db::connect(&config().database).await?;
    audit.execute(
        "INSERT INTO mimir_review_candidates(experience_id,candidate_key,kind,node_id,declaration) VALUES($1,'owned-belief','belief',$2,'{}'::jsonb)",
        &[&source_id, &value.id],
    ).await?;
    let (token, step) = admitted(&service, "delete_belief", json!({"id":value.id})).await?;
    let constraint = format!("reject_belief_result_{}", token.simple());
    audit.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies ADD CONSTRAINT {constraint} CHECK (operation_token <> '{token}'::uuid OR step <> '@operation-result') NOT VALID")).await?;
    let attempted = service.delete_belief_operation(&step).await;
    audit
        .batch_execute(&format!(
            "ALTER TABLE mimir_operation_step_replies DROP CONSTRAINT {constraint}"
        ))
        .await?;
    assert!(attempted.is_err());
    assert!(store.get_belief(value.id).await?.is_some());
    assert!(audit
        .query_opt(
            "SELECT 1 FROM belief_embeddings WHERE belief_id=$1",
            &[&value.id]
        )
        .await?
        .is_some());
    assert!(!audit
        .query_one(
            "SELECT retired FROM mimir_review_candidates WHERE node_id=$1",
            &[&value.id]
        )
        .await?
        .get::<_, bool>(0));
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    assert!(service
        .read_operation_step(token, "@operation-result")
        .await?
        .is_none());
    assert!(matches!(
        service.read_operation_outcome(token, None).await?,
        OperationOutcome::Pending { .. }
    ));
    let source_before: String = audit
        .query_one(
            "SELECT to_jsonb(e)::text FROM mimir_experiences e WHERE id=$1",
            &[&source_id],
        )
        .await?
        .get(0);
    let StepDecision::Done(saved) = service.delete_belief_operation(&step).await? else {
        panic!("retry did not finish")
    };
    assert_eq!(saved.reply, json!({"deleted":true}));
    assert_eq!(completed_reply(&service, token).await?, saved.reply);
    assert!(store.get_belief(value.id).await?.is_none());
    assert!(audit
        .query_one(
            "SELECT retired FROM mimir_review_candidates WHERE node_id=$1",
            &[&value.id]
        )
        .await?
        .get::<_, bool>(0));
    assert_eq!(
        audit
            .query_one(
                "SELECT to_jsonb(e)::text FROM mimir_experiences e WHERE id=$1",
                &[&source_id]
            )
            .await?
            .get::<_, String>(0),
        source_before
    );
    Ok(())
}

#[tokio::test]
async fn another_registered_operation_cannot_enter_belief_deletion() -> Result<()> {
    let (store, service) = setup().await?;
    let value = belief(&store, identity().await?).await?;
    let before = mimir_json::to_value(store.get_belief(value.id).await?)?;
    let (token, wrong_step) =
        admitted(&service, "delete_project", json!({"project":value.project})).await?;
    let error = service
        .delete_belief_operation(&wrong_step)
        .await
        .unwrap_err();
    assert!(error.to_string().contains("registered delete_belief step"));
    assert_eq!(
        mimir_json::to_value(store.get_belief(value.id).await?)?,
        before
    );
    assert!(service
        .read_operation_step(token, wrong_step.id())
        .await?
        .is_none());
    assert!(matches!(
        service.read_operation_outcome(token, None).await?,
        OperationOutcome::Pending { .. }
    ));
    store.delete_belief(value.id).await?;
    Ok(())
}

#[tokio::test]
async fn explicit_cancellation_preserves_belief_and_saves_no_completion() -> Result<()> {
    let (store, service) = setup().await?;
    let value = belief(&store, identity().await?).await?;
    let before = mimir_json::to_value(store.get_belief(value.id).await?)?;
    let (token, step) = admitted(&service, "delete_belief", json!({"id":value.id})).await?;
    let CancellationDecision::Recorded(receipt) =
        service.record_operation_cancellation(token).await?
    else {
        panic!("cancellation missing")
    };
    assert_eq!(
        service.delete_belief_operation(&step).await?,
        StepDecision::Cancelled(receipt)
    );
    assert_eq!(
        mimir_json::to_value(store.get_belief(value.id).await?)?,
        before
    );
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    assert!(service
        .read_operation_step(token, "@operation-result")
        .await?
        .is_none());
    store.delete_belief(value.id).await?;
    Ok(())
}

#[tokio::test]
async fn malformed_original_arguments_receive_correction_before_any_deletion() -> Result<()> {
    let (store, service) = setup().await?;
    let value = belief(&store, identity().await?).await?;
    for arguments in [
        json!({}),
        json!({"id":17}),
        json!({"id":"not-a-uuid"}),
        json!({"id":value.id,"unexpected":true}),
    ] {
        let (token, step) = admitted(&service, "delete_belief", arguments).await?;
        let error = service.delete_belief_operation(&step).await.unwrap_err();
        assert!(error
            .to_string()
            .contains("requires exactly one id field containing a UUID"));
        assert!(store.get_belief(value.id).await?.is_some());
        assert!(service
            .read_operation_step(token, step.id())
            .await?
            .is_none());
        assert!(matches!(
            service.read_operation_outcome(token, None).await?,
            OperationOutcome::Pending { .. }
        ));
    }
    store.delete_belief(value.id).await?;
    Ok(())
}

#[tokio::test]
async fn repeated_numerical_states_restore_deletion_edges_vector_and_pending_token() -> Result<()> {
    let (store, service) = setup().await?;
    let root = belief(&store, identity().await?).await?;
    let mut a = isolation::seed_belief("cyclic deletion A", 0.1, 0.0, MemoryType::Fact).await?;
    let mut b = isolation::seed_belief("cyclic deletion B", 0.1, 0.0, MemoryType::Fact).await?;
    if a.id > b.id {
        std::mem::swap(&mut a, &mut b);
    }
    store
        .insert_edge(&Edge::new(b.id, a.id, EdgeType::Defeats, 0.7)?)
        .await?;
    store
        .insert_edge(&Edge::new(a.id, b.id, EdgeType::Supports, 1.0)?)
        .await?;
    store
        .insert_edge(&Edge::new(root.id, a.id, EdgeType::Supports, 0.0)?)
        .await?;
    store.insert_belief_embedding(root.id, &[0.3, 0.4]).await?;
    let mut original_edges = store.get_edges_among(&[root.id, a.id, b.id]).await?;
    original_edges.sort_by_key(|edge| (edge.0, edge.1));
    let before = mimir_json::to_value([
        store.get_belief(root.id).await?,
        store.get_belief(a.id).await?,
        store.get_belief(b.id).await?,
    ])?;
    let (token, step) = admitted(&service, "delete_belief", json!({"id":root.id})).await?;
    let error = service.delete_belief_operation(&step).await.unwrap_err();
    let decision = error
        .downcast_ref::<NumericalDecision>()
        .expect("actual numerical user decision");
    assert!(decision
        .issue()
        .suggested_correction()
        .contains("Open a dialog"));
    assert_eq!(
        mimir_json::to_value([
            store.get_belief(root.id).await?,
            store.get_belief(a.id).await?,
            store.get_belief(b.id).await?
        ])?,
        before
    );
    let audit = db::connect(&config().database).await?;
    let mut retained_edges = store.get_edges_among(&[root.id, a.id, b.id]).await?;
    retained_edges.sort_by_key(|edge| (edge.0, edge.1));
    assert_eq!(retained_edges, original_edges);
    assert!(audit
        .query_opt(
            "SELECT 1 FROM belief_embeddings WHERE belief_id=$1",
            &[&root.id]
        )
        .await?
        .is_some());
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    assert!(service
        .read_operation_step(token, "@operation-result")
        .await?
        .is_none());
    assert!(
        matches!(service.read_operation_outcome(token,None).await?, OperationOutcome::Pending{saved_replies,..} if saved_replies.is_empty())
    );
    // Dispose only this fixture's three PostgreSQL-issued identities.
    audit.query(&format!("SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (n:Belief) WHERE n.id IN ['{}','{}','{}'] DETACH DELETE n RETURN 1 $$) AS (ok ag_catalog.agtype)", config().database.dbname,root.id,a.id,b.id),&[]).await?;
    store.delete_belief_embeddings(&[root.id]).await?;
    Ok(())
}

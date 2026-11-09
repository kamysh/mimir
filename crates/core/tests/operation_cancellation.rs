//! Explicit cancellation and registered writes in the disposable database.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::Result;
use mimir_core::{
    config::Config,
    db,
    graph::{MemoryType, Pattern},
    store::*,
    MimirService,
};
use serde_json::{json, Value};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};
use tokio::sync::oneshot;
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
    Ok((
        AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)?,
        service,
    ))
}
async fn reserve(service: &MimirService) -> Result<Uuid> {
    Ok(service
        .reserve_operation(&identity().await?.to_string())
        .await?
        .operation_token)
}
async fn planned(
    service: &MimirService,
    operation: &str,
    arguments: Value,
) -> Result<(Uuid, OperationBindingRequest, OperationPlan)> {
    let token = reserve(service).await?;
    let request = OperationBindingRequest::new(operation.into(), arguments, json!({}))?;
    assert!(matches!(
        service.bind_operation_request(token, &request).await?,
        OperationBindingDecision::Bound(_)
    ));
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &request, |_, _| Box::pin(async { Ok(vec![]) }))
        .await?
    else {
        panic!("plan missing")
    };
    Ok((token, request, plan))
}
async fn pattern(store: &AgeStore) -> Result<Pattern> {
    let id = identity().await?;
    let mut pattern = Pattern::new_in_project(
        "cancellation fixture".into(),
        "preserve committed work".into(),
        0.5,
        format!("cancellation-{id}"),
    )?;
    pattern.id = id;
    store.insert_pattern(&pattern).await?;
    Ok(pattern)
}
async fn owner(token: Option<Uuid>, project: &str) -> Result<Uuid> {
    Ok(db::connect(&config().database).await?.query_one(
        "INSERT INTO mimir_embedding_owners(operation_token,project) VALUES($1,$2) RETURNING owner_token", &[&token,&project],
    ).await?.get(0))
}

#[tokio::test]
async fn cancellation_retries_keep_the_original_time_and_reservation() -> Result<()> {
    let (store, service) = setup().await?;
    let unknown = identity().await?;
    assert!(matches!(
        service.record_operation_cancellation(unknown).await?,
        CancellationDecision::UnknownToken
    ));
    assert!(service
        .read_operation_cancellation(unknown)
        .await?
        .is_none());
    let retained = pattern(&store).await?;
    let before = serde_json::to_value(store.get_pattern(retained.id).await?)?;
    let token = reserve(&service).await?;
    let reservation = service.read_operation_reservation(token).await?;
    let CancellationDecision::Recorded(first) =
        service.record_operation_cancellation(token).await?
    else {
        panic!("cancellation missing")
    };
    drop(service);
    let reopened = MimirService::connect(&config()).await?;
    assert_eq!(
        reopened.record_operation_cancellation(token).await?,
        CancellationDecision::Recorded(first.clone())
    );
    assert_eq!(
        reopened.read_operation_cancellation(token).await?,
        Some(first.clone())
    );
    assert_eq!(
        reopened.read_operation_reservation(token).await?,
        reservation
    );
    let request = OperationBindingRequest::new(
        "delete_pattern".into(),
        json!({"id":retained.id}),
        json!({}),
    )?;
    assert!(matches!(
        reopened.bind_operation_request(token, &request).await?,
        OperationBindingDecision::Cancelled(_)
    ));
    assert!(reopened.read_operation_binding(token).await?.is_none());
    assert!(matches!(
        reopened.read_operation_outcome(token, None).await?,
        OperationOutcome::Cancelled { binding: None, .. }
    ));
    assert_eq!(
        serde_json::to_value(store.get_pattern(retained.id).await?)?,
        before
    );
    store.delete_pattern(retained.id).await?;
    Ok(())
}

#[tokio::test]
async fn an_existing_saved_result_wins_without_cancellation_or_changed_answers() -> Result<()> {
    let (store, service) = setup().await?;
    let value = pattern(&store).await?;
    let (token, _, plan) = planned(&service, "delete_pattern", json!({"id":value.id})).await?;
    let step = plan.steps().remove(0);
    let StepDecision::Done(first) = service.delete_pattern_operation(&step).await? else {
        panic!("deletion missing")
    };
    let CancellationDecision::SavedResult(saved) =
        service.record_operation_cancellation(token).await?
    else {
        panic!("saved result missing")
    };
    assert_eq!(saved.reply, first.reply);
    assert_eq!(saved.step, "@operation-result");
    assert!(service.read_operation_cancellation(token).await?.is_none());
    assert_eq!(
        service.read_operation_step(token, step.id()).await?,
        Some(first.clone())
    );
    let OperationOutcome::Completed { outcome, .. } =
        service.read_operation_outcome(token, None).await?
    else {
        panic!("completion changed")
    };
    assert_eq!(outcome.reply(), &first.reply);
    let audit = db::connect(&config().database).await?;
    let refused = audit
        .execute(
            "INSERT INTO mimir_operation_cancellations(operation_token) VALUES($1)",
            &[&token],
        )
        .await
        .unwrap_err();
    assert!(refused.to_string().contains("db error"));
    assert!(service.read_operation_cancellation(token).await?.is_none());
    Ok(())
}

#[tokio::test]
async fn cancellation_prevents_callbacks_and_keeps_the_frozen_plan() -> Result<()> {
    let (store, service) = setup().await?;
    let retained = pattern(&store).await?;
    let (token, request, plan) =
        planned(&service, "delete_pattern", json!({"id":retained.id})).await?;
    let step = plan.steps().remove(0);
    let CancellationDecision::Recorded(receipt) =
        service.record_operation_cancellation(token).await?
    else {
        panic!("cancellation missing")
    };
    let calls = Arc::new(AtomicUsize::new(0));
    let changed = calls.clone();
    let answer = service
        .commit_final_operation_step(&step, move |_, _| {
            Box::pin(async move {
                changed.fetch_add(1, Ordering::SeqCst);
                Ok((json!({"deleted":true}), json!({"deleted":true})))
            })
        })
        .await?;
    assert_eq!(answer, StepDecision::Cancelled(receipt.clone()));
    let selected = calls.clone();
    assert!(matches!(
        service
            .prepare_operation(token, &request, move |_, _| Box::pin(async move {
                selected.fetch_add(1, Ordering::SeqCst);
                Ok(vec![])
            }))
            .await?,
        PlanDecision::Cancelled(_)
    ));
    assert!(matches!(
        service.complete_operation(&plan, json!({})).await?,
        CompletionDecision::Cancelled(_)
    ));
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert!(store.get_pattern(retained.id).await?.is_some());
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    assert!(
        matches!(service.read_operation_outcome(token,Some(&request)).await?,OperationOutcome::Cancelled{binding:Some(_),saved_replies,..} if saved_replies.is_empty())
    );
    store.delete_pattern(retained.id).await?;
    Ok(())
}

#[tokio::test]
async fn revocation_keeps_other_owners_and_rejects_late_metadata_and_answers() -> Result<()> {
    let (_, service) = setup().await?;
    let (token, request, plan) =
        planned(&service, "delete_pattern", json!({"id":identity().await?})).await?;
    let other_token = reserve(&service).await?;
    let removed = owner(Some(token), "owned cancellation").await?;
    let other = owner(Some(other_token), "other cancellation").await?;
    let independent = owner(None, "independent cancellation").await?;
    let CancellationDecision::Recorded(receipt) =
        service.record_operation_cancellation(token).await?
    else {
        panic!("cancellation missing")
    };
    let audit = db::connect(&config().database).await?;
    for (id, present) in [(removed, false), (other, true), (independent, true)] {
        assert_eq!(
            audit
                .query_opt(
                    "SELECT 1 FROM mimir_embedding_owners WHERE owner_token=$1",
                    &[&id]
                )
                .await?
                .is_some(),
            present
        );
    }
    for sql in [
        "INSERT INTO mimir_operation_bindings(operation_token,operation,arguments,settings) VALUES($1,'delete_pattern','{}','{}') ON CONFLICT DO NOTHING",
        "INSERT INTO mimir_operation_plans(operation_token,plan) VALUES($1,'{}') ON CONFLICT DO NOTHING",
        "INSERT INTO mimir_operation_step_replies(operation_token,step,reply) VALUES($1,'late','{}')",
        "INSERT INTO mimir_embedding_owners(operation_token) VALUES($1)",
    ] {
        let refused=audit.execute(sql,&[&token]).await.unwrap_err();
        assert!(refused.as_db_error().unwrap().message().contains("explicitly cancelled"));
    }
    for sql in [
        "UPDATE mimir_operation_cancellations SET cancelled_at=now() WHERE operation_token=$1",
        "DELETE FROM mimir_operation_cancellations WHERE operation_token=$1",
    ] {
        assert!(audit.execute(sql, &[&token]).await.is_err());
    }
    assert!(audit
        .execute(
            "UPDATE mimir_embedding_owners SET operation_token=$2 WHERE owner_token=$1",
            &[&other, &token]
        )
        .await
        .is_err());
    assert_eq!(
        service.read_operation_cancellation(token).await?,
        Some(receipt)
    );
    assert!(service
        .read_operation_step(token, plan.steps()[0].id())
        .await?
        .is_none());
    assert!(matches!(
        service
            .read_operation_outcome(token, Some(&request))
            .await?,
        OperationOutcome::Cancelled { .. }
    ));
    audit
        .execute(
            "DELETE FROM mimir_embedding_owners WHERE owner_token=ANY($1)",
            &[&vec![other, independent]],
        )
        .await?;
    Ok(())
}

#[tokio::test]
async fn cancellation_waits_for_an_entered_step_and_keeps_its_committed_edge() -> Result<()> {
    let (store, service) = setup().await?;
    let project = format!("cancel-partial-{}", identity().await?);
    let a =
        isolation::seed_belief_in_project("source", 0.7, 0.4, &project, MemoryType::Fact).await?;
    let b =
        isolation::seed_belief_in_project("target", 0.6, 0.4, &project, MemoryType::Fact).await?;
    let (token, request, plan) = planned(
        &service,
        "record_defeat",
        json!({"from_id":a.id,"to_id":b.id,"weight":0.5}),
    )
    .await?;
    let steps = plan.steps();
    assert_eq!(steps.len(), 2);
    let first = steps[0].clone();
    let worker = MimirService::connect(&config()).await?;
    let graph = config().database.dbname;
    let sql=format!("SELECT * FROM ag_catalog.cypher('{graph}', $$ MATCH (a:Belief {{id:'{}'}}), (b:Belief {{id:'{}'}}) CREATE (a)-[:DEFEATS {{weight:0.5}}]->(b) RETURN 1 $$) AS (ok ag_catalog.agtype)",a.id,b.id);
    let (entered_tx, entered_rx) = oneshot::channel();
    let (release_tx, release_rx) = oneshot::channel();
    let writing = tokio::spawn(async move {
        worker
            .commit_operation_step(&first, move |tx, _| {
                Box::pin(async move {
                    tx.query(&sql, &[]).await?;
                    entered_tx
                        .send(())
                        .map_err(|_| anyhow::anyhow!("observer closed"))?;
                    release_rx.await?;
                    Ok(json!({"created":true}))
                })
            })
            .await
    });
    entered_rx.await?;
    let canceller = MimirService::connect(&config()).await?;
    let (requested_tx, requested_rx) = oneshot::channel();
    let cancelling = tokio::spawn(async move {
        requested_tx
            .send(())
            .map_err(|_| anyhow::anyhow!("observer closed"))?;
        canceller.record_operation_cancellation(token).await
    });
    requested_rx.await?;
    release_tx
        .send(())
        .map_err(|_| anyhow::anyhow!("writer closed"))?;
    let StepDecision::Done(committed) = writing.await?? else {
        panic!("entered step did not commit")
    };
    assert!(matches!(
        cancelling.await??,
        CancellationDecision::Recorded(_)
    ));
    assert_eq!(store.get_edges_among(&[a.id, b.id]).await?.len(), 1);
    let OperationOutcome::Cancelled {
        saved_replies,
        binding: Some(original),
        ..
    } = service
        .read_operation_outcome(token, Some(&request))
        .await?
    else {
        panic!("cancelled partial outcome missing")
    };
    assert_eq!(saved_replies, vec![committed.clone()]);
    assert_eq!(original.request, request);
    assert_eq!(
        service.read_operation_step(token, steps[0].id()).await?,
        Some(committed)
    );
    let calls = Arc::new(AtomicUsize::new(0));
    let attempted = calls.clone();
    assert!(matches!(
        service
            .commit_final_operation_step(&steps[1], move |_, _| Box::pin(async move {
                attempted.fetch_add(1, Ordering::SeqCst);
                Ok((json!({}), json!({})))
            }))
            .await?,
        StepDecision::Cancelled(_)
    ));
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    store.delete_belief(a.id).await?;
    store.delete_belief(b.id).await?;
    Ok(())
}

#[tokio::test]
async fn cancellation_during_selection_prevents_publishing_the_plan() -> Result<()> {
    let (_, service) = setup().await?;
    let token = reserve(&service).await?;
    let request = OperationBindingRequest::new(
        "delete_pattern".into(),
        json!({"id":identity().await?}),
        json!({}),
    )?;
    service.bind_operation_request(token, &request).await?;
    let capturing_service = MimirService::connect(&config()).await?;
    let captured_request = request.clone();
    let (entered_tx, entered_rx) = oneshot::channel();
    let (release_tx, release_rx) = oneshot::channel();
    let capturing = tokio::spawn(async move {
        capturing_service
            .prepare_operation(token, &captured_request, move |_, _| {
                Box::pin(async move {
                    entered_tx
                        .send(())
                        .map_err(|_| anyhow::anyhow!("observer closed"))?;
                    release_rx.await?;
                    Ok(vec![])
                })
            })
            .await
    });
    entered_rx.await?;
    assert!(matches!(
        service.record_operation_cancellation(token).await?,
        CancellationDecision::Recorded(_)
    ));
    release_tx
        .send(())
        .map_err(|_| anyhow::anyhow!("capture closed"))?;
    assert!(matches!(capturing.await??, PlanDecision::Cancelled(_)));
    let audit = db::connect(&config().database).await?;
    assert!(audit
        .query_opt(
            "SELECT 1 FROM mimir_operation_plans WHERE operation_token=$1",
            &[&token]
        )
        .await?
        .is_none());
    assert!(
        matches!(service.read_operation_outcome(token, Some(&request)).await?, OperationOutcome::Cancelled{saved_replies,..} if saved_replies.is_empty())
    );
    Ok(())
}

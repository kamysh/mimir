//! Real business changes and saved answers in the maintained disposable fixture.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{Context, Result};
use mimir_core::{config::Config, db, learning::*, store::*, MimirService};
use serde_json::{json, Value};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};
use tokio_postgres::Transaction;
use uuid::Uuid;

fn config() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
    }
}

async fn prepared() -> Result<(MimirService, Config, Uuid, Uuid, OperationBindingRequest)> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let client = db::connect(&cfg.database).await?;
    let id: Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("atomic-step-{id}");
    service
        .record_experience(
            &Experience {
                id,
                project: project.clone(),
                context: "private saved-step fixture".into(),
                action: "verify atomic publication".into(),
                outcome: Outcome::Success,
                source: ObservationSource::ToolResult,
                evidence: vec!["owned PostgreSQL fixture receipt".into()],
                belief_ids: vec![],
                pattern_id: None,
                learning_items: vec![],
                source_records: vec![],
            },
            0,
        )
        .await?;
    let token = service.reserve_operation().await?.operation_token;
    let request = OperationBindingRequest::new(
        "delete_project".into(),
        json!({"project":project}),
        json!({}),
    )?;
    assert!(matches!(
        service.bind_operation_request(token, &request).await?,
        OperationBindingDecision::Bound(_)
    ));
    Ok((service, cfg, token, id, request))
}

fn erase<'a, 'client>(
    tx: &'a Transaction<'client>,
    original: &'a OperationBindingRequest,
) -> StepWork<'a> {
    Box::pin(async move {
        let project = original
            .arguments()
            .get("project")
            .and_then(Value::as_str)
            .context("missing admitted project")?;
        let rows = tx
            .query(
                "DELETE FROM mimir_experiences WHERE project=$1 RETURNING id",
                &[&project],
            )
            .await?;
        let removed = rows
            .iter()
            .map(|row| row.get::<_, Uuid>(0).to_string())
            .collect::<Vec<_>>();
        Ok(json!({"removed":removed}))
    })
}

#[tokio::test]
async fn competing_callers_publish_once_and_keep_the_original_answer() -> Result<()> {
    let (first, cfg, token, id, request) = prepared().await?;
    let second = MimirService::connect(&cfg).await?;
    let unbound = first.reserve_operation().await?.operation_token;
    assert_eq!(
        first
            .commit_operation_step(unbound, &request, "delete_experiences", |_, _| Box::pin(
                async { panic!("unbound request executed") }
            ))
            .await?,
        StepDecision::UnknownBinding
    );
    let calls = Arc::new(AtomicUsize::new(0));
    let a = calls.clone();
    let b = calls.clone();
    let (one, two) = tokio::join!(
        first.commit_operation_step(
            token,
            &request,
            "delete_experiences",
            move |tx, original| {
                a.fetch_add(1, Ordering::SeqCst);
                erase(tx, original)
            }
        ),
        second.commit_operation_step(
            token,
            &request,
            "delete_experiences",
            move |tx, original| {
                b.fetch_add(1, Ordering::SeqCst);
                erase(tx, original)
            }
        ),
    );
    assert_eq!(one.as_ref().unwrap(), two.as_ref().unwrap());
    let StepDecision::Done(saved) = one? else {
        panic!("expected a saved answer");
    };
    assert_eq!(saved.reply, json!({"removed":[id.to_string()]}));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(
        second
            .read_operation_step(token, "delete_experiences")
            .await?,
        Some(saved.clone())
    );
    drop(first);
    let reopened = MimirService::connect(&cfg).await?;
    assert_eq!(
        reopened
            .commit_operation_step(token, &request, "delete_experiences", |_, _| Box::pin(
                async { panic!("saved step ran again") }
            ))
            .await?,
        StepDecision::Done(saved)
    );
    // Even a saved answer cannot make a changed request look successful.
    let changed = OperationBindingRequest::new(
        "delete_project".into(),
        json!({"project":"different"}),
        json!({}),
    )?;
    assert!(matches!(
        reopened
            .commit_operation_step(token, &changed, "delete_experiences", |_, _| Box::pin(
                async { panic!("changed request executed") }
            ))
            .await?,
        StepDecision::ChangedRequest(_)
    ));
    Ok(())
}

#[tokio::test]
async fn failing_to_save_an_answer_rolls_back_the_real_business_change() -> Result<()> {
    let (service, cfg, token, id, request) = prepared().await?;
    let result = service.commit_operation_step(token, &request, "delete_experiences", move |tx, original| Box::pin(async move {
        let reply = erase(tx, original).await?;
        // The injected constraint and deletion belong to the SAME transaction.
        // A failed reply insert rolls both back, leaving no fixture-wide guard.
        tx.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies ADD CONSTRAINT mimir_test_reject_reply CHECK (operation_token <> '{token}'::uuid) NOT VALID")).await?;
        Ok(reply)
    })).await;
    assert!(result.is_err());
    assert!(service
        .read_operation_step(token, "delete_experiences")
        .await?
        .is_none());
    let audit = db::connect(&cfg.database).await?;
    assert!(audit
        .query_opt("SELECT id FROM mimir_experiences WHERE id=$1", &[&id])
        .await?
        .is_some());
    assert!(audit
        .query_opt(
            "SELECT 1 FROM pg_constraint WHERE conname='mimir_test_reject_reply'",
            &[]
        )
        .await?
        .is_none());
    let retried = service
        .commit_operation_step(token, &request, "delete_experiences", erase)
        .await?;
    let StepDecision::Done(saved) = retried else {
        panic!("corrected step did not complete");
    };
    assert_eq!(saved.reply, json!({"removed":[id.to_string()]}));
    assert!(audit
        .query_opt("SELECT id FROM mimir_experiences WHERE id=$1", &[&id])
        .await?
        .is_none());
    Ok(())
}

#[tokio::test]
async fn interrupted_connection_before_publication_leaves_no_partial_step() -> Result<()> {
    let (service, cfg, token, id, request) = prepared().await?;
    let service = Arc::new(service);
    let owner = service.clone();
    let expected = request.clone();
    let (reached, at_boundary) = tokio::sync::oneshot::channel();
    let (resume, released) = tokio::sync::oneshot::channel();
    let work = tokio::spawn(async move {
        owner
            .commit_operation_step(
                token,
                &expected,
                "delete_experiences",
                move |tx, original| {
                    Box::pin(async move {
                        let reply = erase(tx, original).await?;
                        let pid: i32 = tx.query_one("SELECT pg_backend_pid()", &[]).await?.get(0);
                        reached
                            .send(pid)
                            .map_err(|_| anyhow::anyhow!("boundary receiver closed"))?;
                        released.await?;
                        Ok(reply)
                    })
                },
            )
            .await
    });
    let pid = at_boundary.await?;
    let audit = db::connect(&cfg.database).await?;
    let stopped: bool = audit
        .query_one("SELECT pg_terminate_backend($1)", &[&pid])
        .await?
        .get(0);
    assert!(stopped);
    resume
        .send(())
        .map_err(|_| anyhow::anyhow!("step task already stopped"))?;
    assert!(work.await?.is_err());
    let reopened = MimirService::connect(&cfg).await?;
    assert!(reopened
        .read_operation_step(token, "delete_experiences")
        .await?
        .is_none());
    assert!(audit
        .query_opt("SELECT id FROM mimir_experiences WHERE id=$1", &[&id])
        .await?
        .is_some());
    let StepDecision::Done(saved) = reopened
        .commit_operation_step(token, &request, "delete_experiences", erase)
        .await?
    else {
        panic!("retry failed");
    };
    assert_eq!(saved.reply, json!({"removed":[id.to_string()]}));
    Ok(())
}

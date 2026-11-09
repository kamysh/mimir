#[allow(dead_code)]
#[path = "../../../../tests/support/isolation.rs"]
mod isolation;
use super::*;

#[test]
fn deeply_nested_invalid_capture_is_rejected_without_recursive_copy_or_cleanup() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let source = format!(
                r#"{{"beliefs":{}null{}}}"#,
                "[".repeat(10000),
                "]".repeat(10000)
            );
            let source = mimir_json::parse(&source).unwrap();
            assert!(pending_keys(&source).is_err());
        })
        .unwrap()
        .join()
        .unwrap();
}
use crate::{config::Config, db, graph::MemoryType, store::CancellationDecision, MimirService};
use serde_json::json;

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

#[test]
fn capture_requires_exact_complete_unique_source_rows() {
    let valid = json!({"beliefs":[{"id":"00000000-0000-0000-0000-000000000001",
        "content":"complete source", "project":null,"already_embedded":false}]});
    assert_eq!(
        pending_keys(&valid).unwrap(),
        vec!["00000000-0000-0000-0000-000000000001"]
    );
    for field in ["id", "content", "project", "already_embedded"] {
        let mut absent = valid.clone();
        absent["beliefs"][0].as_object_mut().unwrap().remove(field);
        assert!(pending_keys(&absent).is_err(), "missing {field}");
    }
    let mut duplicate = valid.clone();
    duplicate["beliefs"]
        .as_array_mut()
        .unwrap()
        .push(valid["beliefs"][0].clone());
    assert!(pending_keys(&duplicate).is_err());
    let mut unknown = valid.clone();
    unknown["beliefs"][0]["limit"] = json!(0);
    assert!(pending_keys(&unknown).is_err());
    let mut skipped = valid;
    skipped["beliefs"][0]["already_embedded"] = json!(true);
    assert!(pending_keys(&skipped).unwrap().is_empty());
}

#[tokio::test]
async fn original_capture_survives_new_records_vectors_and_reconnect() -> Result<()> {
    let cfg = config();
    let client = db::connect(&cfg.database).await?;
    let key: String = client
        .query_one("SELECT gen_random_uuid()::text", &[])
        .await?
        .get(0);
    let project = format!("backfill-capture-{key}");
    let first = isolation::seed_belief_in_project(
        "complete original source",
        0.7,
        0.5,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let service = MimirService::connect(&cfg).await?;
    let token = service.reserve_operation(&key).await?.operation_token;
    let PlanDecision::Ready(plan) = service.prepare_reembed_operation(token).await? else {
        panic!("capture not ready")
    };
    assert!(plan
        .steps()
        .iter()
        .any(|step| step.description().key.as_deref() == Some(first.id.to_string().as_str())));
    let original: String = client
        .query_one(
            "SELECT plan::text FROM mimir_operation_plans WHERE operation_token=$1",
            &[&token],
        )
        .await?
        .get(0);
    let original: Value = mimir_json::from_str(&original)?;
    let captured = original["capture"]["beliefs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == first.id.to_string())
        .unwrap();
    assert_eq!(captured["content"], first.content);
    assert_eq!(captured["project"], project);
    assert_eq!(captured["already_embedded"], false);
    service
        .store
        .insert_belief_embedding(first.id, &{
            let mut values = vec![0.0; 768];
            values[0] = 1.0;
            values
        })
        .await?;
    let later = isolation::seed_belief_in_project(
        "later source excluded from original selection",
        0.7,
        0.5,
        &project,
        MemoryType::Fact,
    )
    .await?;
    drop(service);
    let reopened = MimirService::connect(&cfg).await?;
    let PlanDecision::Ready(retry) = reopened.prepare_reembed_operation(token).await? else {
        panic!("saved capture not ready")
    };
    assert_eq!(
        plan.steps()
            .iter()
            .map(|s| s.description().clone())
            .collect::<Vec<_>>(),
        retry
            .steps()
            .iter()
            .map(|s| s.description().clone())
            .collect::<Vec<_>>()
    );
    assert!(!retry
        .steps()
        .iter()
        .any(|step| step.description().key.as_deref() == Some(later.id.to_string().as_str())));
    let saved: String = client
        .query_one(
            "SELECT plan::text FROM mimir_operation_plans WHERE operation_token=$1",
            &[&token],
        )
        .await?
        .get(0);
    assert_eq!(mimir_json::from_str::<Value>(&saved)?, original);
    assert!(reopened
        .read_operation_step(token, super::super::operation_plans::RESULT_KEY)
        .await?
        .is_none());
    reopened.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn cancellation_notifies_without_a_preparation_owner_row() -> Result<()> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let client = db::connect(&cfg.database).await?;
    let key: String = client
        .query_one("SELECT gen_random_uuid()::text", &[])
        .await?
        .get(0);
    let token = service.reserve_operation(&key).await?.operation_token;
    let mut events = db::EmbeddingOwnerSubscription::connect(&cfg.database).await?;
    let count: i64 = client
        .query_one(
            "SELECT count(*) FROM mimir_embedding_owners WHERE operation_token=$1",
            &[&token],
        )
        .await?
        .get(0);
    assert_eq!(count, 0);
    assert!(matches!(
        service.record_operation_cancellation(token).await?,
        CancellationDecision::Recorded(_)
    ));
    events.changed().await?;
    assert!(service.read_operation_cancellation(token).await?.is_some());
    Ok(())
}

#[tokio::test]
async fn invalid_original_settings_request_recovery_before_capturing_sources() -> Result<()> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let client = db::connect(&cfg.database).await?;
    let key: String = client
        .query_one("SELECT gen_random_uuid()::text", &[])
        .await?
        .get(0);
    let token = service.reserve_operation(&key).await?.operation_token;
    let request = OperationBindingRequest::new("reembed".into(), json!({}), json!({}))?;
    service.bind_operation_request(token, &request).await?;
    let PlanDecision::NeedsRecovery(explanation) = service.prepare_reembed_operation(token).await?
    else {
        panic!("invalid stored settings must request recovery")
    };
    for required in [
        "embeddings",
        "original binding",
        "dialog",
        "Do not select new work",
    ] {
        assert!(
            explanation.contains(required),
            "missing {required}: {explanation}"
        );
    }
    assert_eq!(
        service
            .read_operation_binding(token)
            .await?
            .unwrap()
            .request,
        request
    );
    let plans: i64 = client
        .query_one(
            "SELECT count(*) FROM mimir_operation_plans WHERE operation_token=$1",
            &[&token],
        )
        .await?
        .get(0);
    let replies: i64 = client
        .query_one(
            "SELECT count(*) FROM mimir_operation_step_replies WHERE operation_token=$1",
            &[&token],
        )
        .await?
        .get(0);
    assert_eq!((plans, replies), (0, 0));
    Ok(())
}

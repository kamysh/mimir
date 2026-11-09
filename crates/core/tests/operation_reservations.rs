//! Every connection is constrained to the maintained disposable fixture.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::store::{OperationBindingDecision, OperationBindingRequest};
use mimir_core::{config::Config, db, MimirService};
use serde_json::json;
use serde_json::Value;
use std::collections::BTreeMap;
use tokio_postgres::Client;
use uuid::Uuid;

async fn request_key() -> Result<String> {
    let client = db::connect(&config().database).await?;
    Ok(client
        .query_one("SELECT gen_random_uuid()::text", &[])
        .await?
        .get(0))
}

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

async fn business_snapshot(client: &Client, graph: &str) -> Result<BTreeMap<String, Value>> {
    // Snapshot every column and row, including graph edges and vector tables.
    // Reservation/binding/step receipts are control metadata, not business data.
    let tables = client.query(
        "SELECT quote_ident(n.nspname)||'.'||quote_ident(c.relname) FROM pg_class c JOIN pg_namespace n ON n.oid=c.relnamespace WHERE n.nspname IN ('public',$1) AND c.relkind IN ('r','p') AND c.relname NOT IN ('mimir_operation_reservations','mimir_operation_bindings','mimir_operation_step_replies','mimir_operation_plans','mimir_operation_request_keys') ORDER BY 1",
        &[&graph],
    ).await?;
    let mut snapshot = BTreeMap::new();
    for row in tables {
        let table: String = row.get(0);
        let sql = format!("SELECT COALESCE(jsonb_agg(to_jsonb(t) ORDER BY to_jsonb(t)::text),'[]'::jsonb)::text FROM {table} t");
        let encoded: String = client.query_one(&sql, &[]).await?.get(0);
        snapshot.insert(table, mimir_json::from_str(&encoded)?);
    }
    Ok(snapshot)
}

#[tokio::test]
async fn reservations_survive_lost_reply_and_reconnection_without_business_changes() -> Result<()> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let audit = db::connect(&cfg.database).await?;
    let before = business_snapshot(&audit, &cfg.database.dbname).await?;
    let key = request_key().await?;
    let first = service.reserve_operation(&key).await?;
    assert_eq!(
        service
            .read_operation_reservation(first.operation_token)
            .await?,
        Some(first.clone())
    );
    let second = service.reserve_operation(&request_key().await?).await?;
    assert_eq!(
        service
            .read_operation_reservation(first.operation_token)
            .await?,
        Some(first.clone())
    );
    assert_eq!(
        service
            .read_operation_reservation(second.operation_token)
            .await?,
        Some(second)
    );
    drop(service);
    let reconnected = MimirService::connect(&cfg).await?;
    let old = reconnected
        .read_operation_reservation(first.operation_token)
        .await?
        .unwrap();
    assert_eq!(old, first);
    assert_eq!(reconnected.reserve_operation(&key).await?, first);
    for sql in [
        "UPDATE mimir_operation_reservations SET reserved_at=now() WHERE operation_token=$1",
        "UPDATE mimir_operation_request_keys SET request_key=request_key || '-changed' WHERE operation_token=$1",
        "DELETE FROM mimir_operation_request_keys WHERE operation_token=$1",
    ] {
        let error = audit.execute(sql, &[&first.operation_token]).await.unwrap_err();
        assert_eq!(error.code(), Some(&tokio_postgres::error::SqlState::CHECK_VIOLATION));
        assert_eq!(reconnected.reserve_operation(&key).await?, first);
    }
    assert_eq!(
        business_snapshot(&audit, &cfg.database.dbname).await?,
        before
    );
    Ok(())
}

#[tokio::test]
async fn simultaneous_same_key_keeps_one_reservation_and_original_time() -> Result<()> {
    let cfg = config();
    let first = MimirService::connect(&cfg).await?;
    let second = MimirService::connect(&cfg).await?;
    let audit = db::connect(&cfg.database).await?;
    let key = request_key().await?;
    let before: i64 = audit
        .query_one("SELECT count(*) FROM mimir_operation_reservations", &[])
        .await?
        .get(0);
    let (a, b) = tokio::join!(
        first.reserve_operation(&key),
        second.reserve_operation(&key)
    );
    let original = a?;
    assert_eq!(b?, original);
    let after: i64 = audit
        .query_one("SELECT count(*) FROM mimir_operation_reservations", &[])
        .await?
        .get(0);
    assert_eq!(after, before + 1, "the losing allocation must roll back");
    assert_eq!(first.reserve_operation(&key).await?, original);
    let distinct = format!("{key}-another-action");
    assert_ne!(
        first.reserve_operation(&distinct).await?.operation_token,
        original.operation_token
    );
    Ok(())
}

#[tokio::test]
async fn invalid_or_rejected_key_publication_leaves_no_reservation() -> Result<()> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let audit = db::connect(&cfg.database).await?;
    let before: i64 = audit
        .query_one("SELECT count(*) FROM mimir_operation_reservations", &[])
        .await?
        .get(0);
    for key in ["", " \n\t"] {
        let error = service
            .reserve_operation(key)
            .await
            .unwrap_err()
            .to_string();
        assert!(error.contains("request_key") && error.contains("reuse"));
    }
    // The fixture owns this trigger and no live database is reachable.
    audit.batch_execute("CREATE FUNCTION mimir_fixture_reject_key() RETURNS trigger LANGUAGE plpgsql AS $$ BEGIN IF NEW.request_key LIKE 'fixture-rejected-%' THEN RAISE EXCEPTION 'fixture refuses key publication'; END IF; RETURN NEW; END; $$; CREATE TRIGGER mimir_fixture_reject_key BEFORE INSERT ON mimir_operation_request_keys FOR EACH ROW EXECUTE FUNCTION mimir_fixture_reject_key();").await?;
    let key = format!("fixture-rejected-{}", request_key().await?);
    let rejected = service.reserve_operation(&key).await;
    audit.batch_execute("DROP TRIGGER mimir_fixture_reject_key ON mimir_operation_request_keys; DROP FUNCTION mimir_fixture_reject_key();").await?;
    assert!(rejected.is_err());
    let after: i64 = audit
        .query_one("SELECT count(*) FROM mimir_operation_reservations", &[])
        .await?
        .get(0);
    assert_eq!(after, before);
    // The caller can repair the cause and repeat the same key.
    let original = service.reserve_operation(&key).await?;
    assert_eq!(service.reserve_operation(&key).await?, original);
    Ok(())
}

#[tokio::test]
async fn rolled_back_reservation_is_not_a_usable_token() -> Result<()> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let mut client = db::connect(&cfg.database).await?;
    let tx = client.transaction().await?;
    let token: Uuid = tx
        .query_one(
            "INSERT INTO mimir_operation_reservations DEFAULT VALUES RETURNING operation_token",
            &[],
        )
        .await?
        .get(0);
    tx.rollback().await?;
    assert!(service.read_operation_reservation(token).await?.is_none());
    Ok(())
}

#[tokio::test]
async fn original_request_survives_changed_input_reconnection_and_direct_mutation() -> Result<()> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let audit = db::connect(&cfg.database).await?;
    let before = business_snapshot(&audit, &cfg.database.dbname).await?;
    let token = service
        .reserve_operation(&request_key().await?)
        .await?
        .operation_token;
    let request = OperationBindingRequest::new(
        "delete_project".into(),
        json!({"project":"fixture-project", "selected":[1,2]}),
        json!({"policy":"user-selected"}),
    )?;
    let OperationBindingDecision::Bound(original) =
        service.bind_operation_request(token, &request).await?
    else {
        panic!("first binding was not admitted");
    };
    // JSON object order and equivalent JSONB numbers do not change a request.
    let equivalent = OperationBindingRequest::new(
        "delete_project".into(),
        mimir_json::from_str("{\"selected\":[1.0,2],\"project\":\"fixture-project\"}")?,
        json!({"policy":"user-selected"}),
    )?;
    assert_eq!(
        service.bind_operation_request(token, &equivalent).await?,
        OperationBindingDecision::Bound(original.clone())
    );
    for changed in [
        OperationBindingRequest::new(
            "delete_project".into(),
            json!({"project":"other-project", "selected":[1,2]}),
            request.settings().clone(),
        )?,
        OperationBindingRequest::new(
            "delete_project".into(),
            json!({"project":"fixture-project", "selected":[2,1]}),
            request.settings().clone(),
        )?,
        OperationBindingRequest::new(
            "delete_project".into(),
            request.arguments().clone(),
            json!({"policy":"different"}),
        )?,
        OperationBindingRequest::new(
            "different_operation".into(),
            request.arguments().clone(),
            request.settings().clone(),
        )?,
    ] {
        assert_eq!(
            service.bind_operation_request(token, &changed).await?,
            OperationBindingDecision::ChangedRequest(original.clone())
        );
    }
    drop(service);
    let reconnected = MimirService::connect(&cfg).await?;
    assert_eq!(
        reconnected.read_operation_binding(token).await?,
        Some(original.clone())
    );
    assert_eq!(
        reconnected.bind_operation_request(token, &request).await?,
        OperationBindingDecision::Bound(original.clone())
    );
    for sql in [
        "UPDATE mimir_operation_bindings SET arguments='{}'::jsonb WHERE operation_token=$1",
        "DELETE FROM mimir_operation_bindings WHERE operation_token=$1",
    ] {
        let error = audit.execute(sql, &[&token]).await.unwrap_err();
        assert_eq!(
            error.code(),
            Some(&tokio_postgres::error::SqlState::CHECK_VIOLATION)
        );
        assert_eq!(
            reconnected.read_operation_binding(token).await?,
            Some(original.clone())
        );
    }
    assert_eq!(
        business_snapshot(&audit, &cfg.database.dbname).await?,
        before
    );
    Ok(())
}

#[tokio::test]
async fn concurrent_different_requests_have_one_immutable_winner() -> Result<()> {
    let cfg = config();
    let first = MimirService::connect(&cfg).await?;
    let second = MimirService::connect(&cfg).await?;
    let token = first
        .reserve_operation(&request_key().await?)
        .await?
        .operation_token;
    let one =
        OperationBindingRequest::new("delete_project".into(), json!({"project":"one"}), json!({}))?;
    let two =
        OperationBindingRequest::new("delete_project".into(), json!({"project":"two"}), json!({}))?;
    let (a, b) = tokio::join!(
        first.bind_operation_request(token, &one),
        second.bind_operation_request(token, &two)
    );
    let (winner, rejected) = match (a?, b?) {
        (
            OperationBindingDecision::Bound(winner),
            OperationBindingDecision::ChangedRequest(rejected),
        )
        | (
            OperationBindingDecision::ChangedRequest(rejected),
            OperationBindingDecision::Bound(winner),
        ) => (winner, rejected),
        other => panic!("expected one binding and one correction: {other:?}"),
    };
    assert_eq!(winner, rejected);
    assert_eq!(first.read_operation_binding(token).await?, Some(winner));
    Ok(())
}

#[tokio::test]
async fn invalid_storage_input_and_uncommitted_tokens_cannot_create_a_binding() -> Result<()> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let mut client = db::connect(&cfg.database).await?;
    let tx = client.transaction().await?;
    let token: Uuid = tx
        .query_one(
            "INSERT INTO mimir_operation_reservations DEFAULT VALUES RETURNING operation_token",
            &[],
        )
        .await?
        .get(0);
    tx.rollback().await?;
    let request = OperationBindingRequest::new(
        "delete_project".into(),
        json!({"project":"fixture"}),
        json!({}),
    )?;
    assert_eq!(
        service.bind_operation_request(token, &request).await?,
        OperationBindingDecision::UnknownToken
    );
    assert!(service.read_operation_binding(token).await?.is_none());
    assert!(OperationBindingRequest::new("delete_project".into(), json!(null), json!({})).is_err());
    assert!(OperationBindingRequest::new("delete_project".into(), json!({}), json!([])).is_err());
    assert!(OperationBindingRequest::new(" delete_project".into(), json!({}), json!({})).is_err());
    Ok(())
}

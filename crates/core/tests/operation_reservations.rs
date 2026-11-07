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

fn config() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
    }
}

async fn business_snapshot(client: &Client, graph: &str) -> Result<BTreeMap<String, Value>> {
    // Snapshot every column and row, including graph edges and vector tables.
    // Reservation/binding/step receipts are control metadata, not business data.
    let tables = client.query(
        "SELECT quote_ident(n.nspname)||'.'||quote_ident(c.relname) FROM pg_class c JOIN pg_namespace n ON n.oid=c.relnamespace WHERE n.nspname IN ('public',$1) AND c.relkind IN ('r','p') AND c.relname NOT IN ('mimir_operation_reservations','mimir_operation_bindings','mimir_operation_step_replies') ORDER BY 1",
        &[&graph],
    ).await?;
    let mut snapshot = BTreeMap::new();
    for row in tables {
        let table: String = row.get(0);
        let sql = format!("SELECT COALESCE(jsonb_agg(to_jsonb(t) ORDER BY to_jsonb(t)::text),'[]'::jsonb)::text FROM {table} t");
        let encoded: String = client.query_one(&sql, &[]).await?.get(0);
        snapshot.insert(table, serde_json::from_str(&encoded)?);
    }
    Ok(snapshot)
}

#[tokio::test]
async fn reservations_survive_reconnection_and_age_without_business_changes() -> Result<()> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let audit = db::connect(&cfg.database).await?;
    let before = business_snapshot(&audit, &cfg.database.dbname).await?;
    let first = service.reserve_operation().await?;
    assert_eq!(
        service
            .read_operation_reservation(first.operation_token)
            .await?,
        Some(first.clone())
    );
    let second = service.reserve_operation().await?;
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
    audit.execute("UPDATE mimir_operation_reservations SET reserved_at=TIMESTAMPTZ '1900-01-01 00:00:00+00' WHERE operation_token=$1", &[&first.operation_token]).await?;
    drop(service);
    let reconnected = MimirService::connect(&cfg).await?;
    let old = reconnected
        .read_operation_reservation(first.operation_token)
        .await?
        .unwrap();
    assert_eq!(old.operation_token, first.operation_token);
    assert!(old.reserved_at < first.reserved_at);
    assert_eq!(
        business_snapshot(&audit, &cfg.database.dbname).await?,
        before
    );
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
    let token = service.reserve_operation().await?.operation_token;
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
        serde_json::from_str("{\"selected\":[1.0,2],\"project\":\"fixture-project\"}")?,
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
    let token = first.reserve_operation().await?.operation_token;
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

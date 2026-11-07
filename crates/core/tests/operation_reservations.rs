//! Every connection is constrained to the maintained disposable fixture.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::{config::Config, db, MimirService};
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
    // Only the explicitly authorized reservation metadata is excluded.
    let tables = client.query(
        "SELECT quote_ident(n.nspname)||'.'||quote_ident(c.relname) FROM pg_class c JOIN pg_namespace n ON n.oid=c.relnamespace WHERE n.nspname IN ('public',$1) AND c.relkind IN ('r','p') AND c.relname <> 'mimir_operation_reservations' ORDER BY 1",
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

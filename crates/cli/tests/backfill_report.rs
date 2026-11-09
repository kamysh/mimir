//! Actual CLI backfill decisions use the guarded disposable database fixture.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{config::Config, db, graph::MemoryType, MimirService};
use serde_json::Value;
use std::process::Stdio;

#[tokio::test]
async fn reembed_without_backend_requests_a_decision_and_preserves_existing_data() -> Result<()> {
    let fixture = isolation::fixture();
    let config = Config::load()?;
    fixture.assert_database(&config.database);
    ensure!(
        config.embeddings.is_none(),
        "this fixture must not configure a model"
    );
    let service = MimirService::connect(&config).await?;
    let client = db::connect(&config.database).await?;
    let identity: uuid::Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("cli-backfill-missing-backend-{identity}");
    let belief = isolation::seed_belief_in_project(
        "stored belief still waiting for an embedding",
        0.7,
        0.5,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let before = serde_json::to_value(service.get_belief(belief.id).await?)?;
    let log = fixture
        .root
        .join(format!("backfill-missing-backend-{identity}"));
    let mut child = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir"))
        .arg("reembed")
        .stdin(Stdio::null())
        .stdout(std::fs::File::create(log.with_extension("stdout"))?)
        .stderr(std::fs::File::create(log.with_extension("stderr"))?)
        .kill_on_drop(true)
        .spawn()?;
    let status = child.wait().await?;
    std::fs::write(log.with_extension("exit"), format!("{:?}\n", status.code()))?;
    let output = std::fs::read(log.with_extension("stdout"))?;
    let after = serde_json::to_value(service.get_belief(belief.id).await?)?;
    let vector_count: i64 = client
        .query_one(
            "SELECT count(*) FROM public.belief_embeddings WHERE belief_id=$1",
            &[&belief.id],
        )
        .await?
        .get(0);
    service.delete_project(&project).await?;

    ensure!(
        status.success(),
        "CLI must offer a decision; output retained at {}",
        log.display()
    );
    // Parse all stdout: a trailing success summary would make this fail too.
    let report: Value = serde_json::from_slice(&output)?;
    ensure!(report["status"] == "needs_input");
    ensure!(report["operation_status"] == "incomplete");
    ensure!(report["next_action"] == "open_user_dialog");
    ensure!(report["current_vector_publication"] == "not_attempted");
    ensure!(report["current_belief_id"].is_null());
    ensure!(report["confirmed_counts"]["embedded"] == 0);
    ensure!(report["business_changes"]["embedded_belief_ids"]
        .as_array()
        .is_some_and(Vec::is_empty));
    let problem = report["problem"].as_str().unwrap_or_default();
    ensure!(problem.contains("user") && problem.contains("embedding"));
    ensure!(
        after == before && vector_count == 0,
        "a prerequisite decision must preserve stored data"
    );
    eprintln!("Backfill CLI output retained at {}", log.display());
    Ok(())
}

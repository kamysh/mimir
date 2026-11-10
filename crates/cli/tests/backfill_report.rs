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
    let before = mimir_json::to_value(service.get_belief(belief.id).await?)?;
    let token = service
        .reserve_operation(&format!("cli-backfill-{identity}"))
        .await?
        .operation_token;
    let log = fixture
        .root
        .join(format!("backfill-missing-backend-{identity}"));
    let mut child = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir"))
        .arg("reembed")
        .args(["--operation-token", &token.to_string()])
        .stdin(Stdio::null())
        .stdout(std::fs::File::create(log.with_extension("stdout"))?)
        .stderr(std::fs::File::create(log.with_extension("stderr"))?)
        .kill_on_drop(true)
        .spawn()?;
    let status = child.wait().await?;
    std::fs::write(log.with_extension("exit"), format!("{:?}\n", status.code()))?;
    let output = std::fs::read(log.with_extension("stdout"))?;
    let after = mimir_json::to_value(service.get_belief(belief.id).await?)?;
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
    let report: Value = mimir_json::from_slice(&output)?;
    ensure!(report["status"] == "needs_input");
    ensure!(report["next_action"] == "correct_request_or_ask_user");
    let correction: mimir_core::interaction::NeedsInput = mimir_json::decode_ref(&report)?;
    let problem = &correction.issues()[0].fault().message;
    ensure!(problem.contains("user") && problem.contains("embedding"));
    ensure!(
        matches!(
            service.read_operation_outcome(token, None).await?,
            mimir_core::store::OperationOutcome::Pending { .. }
        ),
        "a missing provider must preserve the original unfinished plan"
    );
    ensure!(
        after == before && vector_count == 0,
        "a prerequisite decision must preserve stored data"
    );
    eprintln!("Backfill CLI output retained at {}", log.display());
    Ok(())
}

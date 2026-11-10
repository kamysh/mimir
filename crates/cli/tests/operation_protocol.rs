//! Actual CLI processes must retain the action identity and original answer.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Context, Result};
use mimir_core::{config::Config, db, graph::MemoryType, interaction::NeedsInput, MimirService};
use std::{path::Path, process::Command};
use uuid::Uuid;

fn command(
    root: &Path,
    name: &str,
    arguments: &[&str],
    without_config: bool,
) -> Result<mimir_json::Document> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_mimir"));
    command.args(arguments);
    if without_config {
        command
            .env_clear()
            .env("MIMIR_CONFIG", root.join("must-not-read-config.toml"));
    }
    let output = command.output()?;
    std::fs::write(root.join(format!("{name}.stdout")), &output.stdout)?;
    std::fs::write(root.join(format!("{name}.stderr")), &output.stderr)?;
    std::fs::write(
        root.join(format!("{name}.exit")),
        format!("{}\n", output.status),
    )?;
    ensure!(
        output.status.success(),
        "CLI failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    ensure!(
        output.stderr.is_empty(),
        "the reply must carry the full correction: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    Ok(mimir_json::parse(std::str::from_utf8(&output.stdout)?)?)
}

#[tokio::test]
async fn cli_reserves_replays_reads_and_cancels_the_original_action() -> Result<()> {
    let fixture = isolation::fixture();
    let audit = db::connect(&fixture.database_config()).await?;
    let id: Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let root = fixture.root.join(format!("cli-operation-{id}"));
    std::fs::create_dir(&root)?;
    let project = format!("cli-operation-{id}");
    let config = Config {
        database: fixture.database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let service = MimirService::connect(&config).await?;
    let belief = isolation::seed_belief_in_project(
        "a disposable belief",
        0.5,
        0.2,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let key = format!("delete-{id}");
    let reserved = command(&root, "reserve", &["operation", "reserve", &key], false)?;
    ensure!(
        reserved
            == command(
                &root,
                "reserve-replay",
                &["operation", "reserve", &key],
                false
            )?
    );
    let token = reserved["operation_token"]
        .as_str()
        .context("missing token")?;
    let belief_id = belief.id.to_string();
    let arguments = ["delete", "belief", &belief_id, "--operation-token", token];
    let completed = command(&root, "delete", &arguments, false)?;
    ensure!(
        completed["status"] == "completed" && completed["result"]["deleted"] == true,
        "unexpected deletion receipt: {completed}"
    );
    ensure!(service.get_belief(belief.id).await?.is_none());
    ensure!(
        completed == command(&root, "delete-replay", &arguments, false)?,
        "retry lost the original true deletion result"
    );
    let readback = command(
        &root,
        "read",
        &["operation", "outcome", "--operation-token", token],
        false,
    )?;
    for field in ["operation_token", "status", "original_request", "result"] {
        ensure!(
            readback[field] == completed[field],
            "readback changed original {field}"
        );
    }
    ensure!(readback["pending_executions"]
        .as_array()
        .context("readback execution list")?
        .is_empty());
    ensure!(readback["worker_cleanup"] == "not_confirmed_by_this_receipt");
    ensure!(
        completed
            == command(
                &root,
                "cancel-completed",
                &["operation", "cancel", "--operation-token", token],
                false
            )?
    );
    let changed = command(
        &root,
        "changed-request",
        &["forget", &project, "--operation-token", token],
        false,
    )?;
    let _: NeedsInput = mimir_json::decode_ref(&changed)?;
    let wrong_backfill = command(
        &root,
        "wrong-backfill-token",
        &["reembed", "--operation-token", token],
        false,
    )?;
    let _: NeedsInput = mimir_json::decode_ref(&wrong_backfill)?;
    ensure!(
        wrong_backfill["status"] == "needs_input",
        "backfill returned another action's success"
    );

    let cancellation_key = format!("cancel-{id}");
    let pending = command(
        &root,
        "reserve-cancel",
        &["operation", "reserve", &cancellation_key],
        false,
    )?;
    let cancel_token = pending["operation_token"]
        .as_str()
        .context("missing token")?;
    let cancelled = command(
        &root,
        "cancel",
        &["operation", "cancel", "--operation-token", cancel_token],
        false,
    )?;
    ensure!(
        cancelled["status"] == "cancelled"
            && cancelled["worker_cleanup"] == "confirmed_for_all_registered_copies"
    );
    let revoked = command(
        &root,
        "revoked-write",
        &["forget", &project, "--operation-token", cancel_token],
        false,
    )?;
    ensure!(revoked["status"] == "cancelled");

    for (index, args) in [
        vec!["forget", &project],
        vec!["operation", "outcome"],
        vec!["operation", "cancel"],
        vec!["operation", "reserve", "   "],
        vec!["stats", "--operation-token", token],
        vec!["forget", &project, "--operation-token", "not-a-uuid"],
    ]
    .into_iter()
    .enumerate()
    {
        let response = command(&root, &format!("input-{index}"), &args, true)?;
        let correction: NeedsInput = mimir_json::decode_ref(&response)?;
        ensure!(!correction.issues()[0].suggested_correction().is_empty());
    }
    let pending_key = format!("prepare-{id}");
    let pending = command(
        &root,
        "reserve-document",
        &["operation", "reserve", &pending_key],
        false,
    )?;
    let pending_token = pending["operation_token"]
        .as_str()
        .context("missing token")?;
    let document = root.join("source.md");
    std::fs::write(
        &document,
        "# Supporting source\nThe complete original passage.\n",
    )?;
    let response = command(
        &root,
        "missing-embedding",
        &[
            "doc",
            "load",
            document.to_str().unwrap(),
            "--project",
            &project,
            "--operation-token",
            pending_token,
        ],
        false,
    )?;
    let _: NeedsInput = mimir_json::decode_ref(&response)?;
    ensure!(response["status"] == "needs_input");
    ensure!(
        service
            .read_operation_binding(pending_token.parse()?)
            .await?
            .context("the admitted source must retain its binding")?
            .request
            .operation()
            == "load_document"
    );
    service.delete_project(&project).await?;
    eprintln!("Complete CLI operation transcripts: {}", root.display());
    Ok(())
}

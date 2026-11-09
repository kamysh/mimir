//! Existing hook paths preserve complete queries and results without live hooks.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{config::Config, db, graph::MemoryType, MimirService};
use std::{
    io::Write,
    os::unix::fs::PermissionsExt,
    process::{Command, Stdio},
};

#[tokio::test]
async fn hooks_keep_late_query_terms_all_results_and_full_belief_text() -> Result<()> {
    let fixture = isolation::fixture();
    let cfg = Config {
        database: fixture.database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let svc = MimirService::connect(&cfg).await?;
    let client = db::connect(&cfg.database).await?;
    let id: uuid::Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("complete-hook-{id}");
    let foreign_project = format!("{project}-other");
    let needle = format!("latequery{}", id.simple());
    let scratch = fixture.root.join(format!("hook-output-{id}"));
    std::fs::create_dir(&scratch)?;
    std::fs::set_permissions(&scratch, std::fs::Permissions::from_mode(0o700))?;
    let checked = async {
        let mut texts = Vec::new();
        for index in 0..6 {
            let content = format!("{needle} {} final retained condition {index}", "λ complete knowledge ".repeat(250));
            isolation::seed_belief_in_project(&content, 0.8, 0.4, &project, MemoryType::Fact).await?;
            texts.push(content);
        }
        let working = format!("{}final working decision", "全文 unresolved working content ".repeat(250));
        isolation::seed_belief_in_project(&working, 0.7, 0.4, &project, MemoryType::Working).await?;
        let foreign = format!("{needle} foreign project must stay hidden");
        isolation::seed_belief_in_project(&foreign, 0.9, 0.4, &foreign_project, MemoryType::Fact).await?;
        let execute = |args: &[&str], input: serde_json::Value| -> Result<std::process::Output> {
            let mut child = Command::new(env!("CARGO_BIN_EXE_mimir"))
                .args(args).env("TMPDIR", &scratch).env("CLAUDE_CODE_SESSION_ID", id.to_string())
                .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn()?;
            child.stdin.take().unwrap().write_all(serde_json::to_string(&input)?.as_bytes())?;
            Ok(child.wait_with_output()?)
        };
        let declared = execute(&["hook", "set-project", &project], serde_json::json!({}))?;
        ensure!(declared.status.success(), "set-project failed: {}", String::from_utf8_lossy(&declared.stderr));
        ensure!(String::from_utf8(declared.stdout)?.contains(&working), "project message must retain the complete working belief");
        let long_query = format!("{} {needle}", "!".repeat(700));
        for (event, input) in [
            ("prompt", serde_json::json!({"session_id":id.to_string(), "prompt":long_query})),
            ("pretooluse", serde_json::json!({"session_id":id.to_string(), "tool_input":{"command":long_query}})),
        ] {
            let output = execute(&["hook", event], input)?;
            ensure!(output.status.success(), "{event} failed: {}", String::from_utf8_lossy(&output.stderr));
            let stdout = String::from_utf8(output.stdout)?;
            let shown = if event == "pretooluse" {
                serde_json::from_str::<serde_json::Value>(&stdout)?["hookSpecificOutput"]["additionalContext"].as_str().unwrap().to_owned()
            } else { stdout };
            for text in &texts {
                ensure!(shown.contains(text), "{event} must use the late term, retain all six matches and print every complete belief");
            }
            ensure!(!shown.contains(&foreign), "{event} must retain project scope");
        }
        let stopped = execute(&["hook", "stop", "--project", &project], serde_json::json!({"stop_hook_active":false}))?;
        ensure!(stopped.status.code() == Some(2), "the separate legacy Stop policy must retain its existing outcome");
        ensure!(String::from_utf8(stopped.stderr)?.contains(&working), "Stop output must retain the whole working belief");
        Ok::<_, anyhow::Error>(())
    }.await;
    let cleanup = svc.delete_project(&project).await;
    let foreign_cleanup = svc.delete_project(&foreign_project).await;
    let scratch_cleanup = std::fs::remove_dir_all(&scratch);
    checked?;
    cleanup?;
    foreign_cleanup?;
    scratch_cleanup?;
    Ok(())
}

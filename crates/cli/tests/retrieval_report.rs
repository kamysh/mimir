//! Real CLI and hook output against the maintained private PostgreSQL fixture.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Result};
use mimir_core::{config::Config, db, graph::Belief, store::AgeStore};
use serde_json::json;
use std::{
    io::Write,
    path::Path,
    process::{Command, Stdio},
};
use uuid::Uuid;

#[path = "../../../tests/support/retrieval_preference.rs"]
mod preference;

#[tokio::test]
async fn cli_evidence_preserves_memory_preference_and_selection() -> Result<()> {
    let fixture = isolation::fixture();
    let config = Config::load_from_path(&fixture.root.join("config.toml"))?;
    fixture.assert_database(&config.database);
    let state = preference::PreferenceFixture::create(&config).await?;
    let output_root = fixture
        .root
        .join(format!("preference-output-{}", state.ordinary_first));
    std::fs::create_dir(&output_root)?;
    let checked = async {
        let base = [
            "query",
            state.query.as_str(),
            "--project",
            state.project.as_str(),
            "--limit",
            "1",
        ];
        let ordinary = run(&output_root, "ordinary", &base, None)?;
        ensure!(ordinary.contains(&state.ordinary_first.to_string()));
        let mut preferred = base.to_vec();
        preferred.extend(["--prefer-type", "experiential"]);
        let plain = run(&output_root, "preferred", &preferred, None)?;
        preferred.push("--evidence");
        let enriched = run(&output_root, "preferred-evidence", &preferred, None)?;
        for output in [&plain, &enriched] {
            ensure!(
                output.contains(&state.preferred_first.to_string()),
                "preference ignored; complete output at {}",
                output_root.display()
            );
            ensure!(
                !output.contains(&state.ordinary_first.to_string()),
                "selection changed"
            );
            ensure!(
                output.contains("semantic similarity was not evaluated"),
                "coverage missing"
            );
        }
        ensure!(
            enriched.contains("Complete supporting passage"),
            "support missing"
        );
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = state.cleanup().await;
    checked?;
    cleanup
}

fn run(root: &Path, name: &str, args: &[&str], input: Option<serde_json::Value>) -> Result<String> {
    let mut child = Command::new(env!("CARGO_BIN_EXE_mimir"))
        .args(args)
        .stdin(if input.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    if let Some(input) = input {
        child
            .stdin
            .take()
            .unwrap()
            .write_all(serde_json::to_string(&input)?.as_bytes())?;
    }
    let output = child.wait_with_output()?;
    std::fs::write(root.join(format!("{name}.stdout")), &output.stdout)?;
    std::fs::write(root.join(format!("{name}.stderr")), &output.stderr)?;
    std::fs::write(
        root.join(format!("{name}.exit")),
        format!("{:?}\n", output.status.code()),
    )?;
    ensure!(
        output.status.success(),
        "{name} failed; complete output at {}",
        root.display()
    );
    Ok(String::from_utf8(output.stdout)?)
}

#[tokio::test]
async fn cli_and_hooks_keep_informative_coverage_and_pretool_stdout_valid_json() -> Result<()> {
    let fixture = isolation::fixture();
    let cfg = Config::load_from_path(&fixture.root.join("config.toml"))?;
    fixture.assert_database(&cfg.database);
    ensure!(
        cfg.embeddings.is_none(),
        "this test requires the fixture's intentionally unconfigured embeddings"
    );
    let audit = db::connect(&cfg.database).await?;
    let id: Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("cli-retrieval-{id}");
    let query = format!("E0412_literal_{id}");
    let root = fixture.root.join(format!("retrieval-output-{id}"));
    std::fs::create_dir(&root)?;
    let store = AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)?;
    let mut belief = Belief::new_in_project(query.clone(), 0.7, 0.5, project.clone())?;
    belief.id = id;
    store.insert_belief(&belief).await?;
    let checked = async {
        for (name, args, input) in [
            ("query", vec!["query", &query, "--project", &project], None),
            (
                "grounded",
                vec!["query", &query, "--project", &project, "--evidence"],
                None,
            ),
            (
                "prompt",
                vec!["hook", "prompt"],
                Some(json!({"session_id":id,"prompt":query})),
            ),
            (
                "pretool",
                vec!["hook", "pretooluse"],
                Some(json!({"session_id":id,"tool_input":{"command":query}})),
            ),
        ] {
            let output = run(&root, name, &args, input)?;
            let shown = if name == "pretool" {
                let value: serde_json::Value = serde_json::from_str(&output)?;
                ensure!(value["hookSpecificOutput"]["hookEventName"] == "PreToolUse");
                value["hookSpecificOutput"]["additionalContext"]
                    .as_str()
                    .unwrap()
                    .to_string()
            } else {
                output
            };
            ensure!(
                shown.contains(&query)
                    && shown.contains("no embedding backend is configured")
                    && shown.contains("semantic similarity was not evaluated")
                    && shown.contains("Next step:"),
                "{name} hid retrieval coverage; complete output at {}",
                root.display()
            );
        }
        Ok::<_, anyhow::Error>(())
    }
    .await;
    store.delete_project(&project).await?;
    eprintln!("Complete CLI output retained at {}", root.display());
    checked
}

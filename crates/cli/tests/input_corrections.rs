//! Actual CLI/MCP correction outcomes; invalid CLI input must not load config.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{
    interaction::NeedsInput,
    validation::{Code, Segment},
};
use serde_json::{json, Value};
use std::process::{Command, Stdio};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

fn invalid(arguments: &[&str]) -> Result<NeedsInput> {
    let fixture = isolation::fixture();
    let output = Command::new(env!("CARGO_BIN_EXE_mimir"))
        .args(arguments)
        .env_clear()
        .env(
            "MIMIR_CONFIG",
            fixture.root.join("must-not-read-this-config.toml"),
        )
        .output()?;
    ensure!(
        output.status.success(),
        "invalid input became execution failure: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    ensure!(
        output.stderr.is_empty(),
        "correction must carry its own complete diagnostic"
    );
    let value: Value = serde_json::from_slice(&output.stdout)?;
    ensure!(
        value["status"] == "needs_input" && value["business_changes"] == "none",
        "input was reported as completed"
    );
    Ok(serde_json::from_value(value)?)
}

#[test]
fn parser_and_semantic_misuse_return_repair_guidance_before_configuration() -> Result<()> {
    for (arguments, code) in [
        (vec!["list", "--limit", "0"], Code::InvalidNumber),
        (vec!["list", "--limt", "2"], Code::UnknownField),
        (vec!["forget"], Code::MissingField),
        (
            vec!["judge", "run", "--invented-option"],
            Code::UnknownField,
        ),
        (
            vec!["sweep-defeated", "--threshold", "2"],
            Code::InvalidNumber,
        ),
        (vec!["decay", "--factor", "NaN"], Code::InvalidNumber),
        (
            vec!["decay", "--factor", "not-a-number"],
            Code::InvalidNumber,
        ),
        (vec!["delete", "belief", "bad-id"], Code::MalformedInput),
    ] {
        let correction = invalid(&arguments)?;
        ensure!(
            correction.issues()[0].fault().code == code,
            "wrong diagnosis for {arguments:?}: {correction:?}"
        );
        ensure!(!correction.issues()[0].expected().is_empty());
        ensure!(!correction.issues()[0].suggested_correction().is_empty());
    }
    ensure!(
        invalid(&["list", "--limt", "2"])?.issues()[0].fault().path
            == vec![Segment::Key("--limt".into())]
    );
    let correction = invalid(&[
        "evidence",
        "add",
        "bad-chunk",
        "bad-belief",
        "--weight",
        "2",
    ])?;
    ensure!(
        correction.issues().len() == 3,
        "every supplied invalid field must be identified"
    );
    for field in ["chunk_id", "belief_id", "weight"] {
        ensure!(correction
            .issues()
            .iter()
            .any(|issue| issue.fault().path == vec![Segment::Key(field.into())]));
    }
    for flag in ["--help", "--version"] {
        let output = Command::new(env!("CARGO_BIN_EXE_mimir"))
            .arg(flag)
            .env_clear()
            .output()?;
        ensure!(
            output.status.success() && !output.stdout.is_empty(),
            "help or version changed"
        );
    }
    let fixture = isolation::fixture();
    let operational = Command::new(env!("CARGO_BIN_EXE_mimir"))
        .arg("stats")
        .env_clear()
        .env(
            "MIMIR_CONFIG",
            fixture.root.join("must-not-read-this-config.toml"),
        )
        .output()?;
    ensure!(
        !operational.status.success(),
        "configuration failure became successful execution"
    );
    ensure!(
        !String::from_utf8_lossy(&operational.stdout).contains("business_changes"),
        "unclassified failure claimed nothing changed"
    );
    Ok(())
}

#[tokio::test]
async fn cli_and_mcp_keep_the_same_uuid_diagnosis_and_mcp_remains_usable() -> Result<()> {
    let fixture = isolation::fixture();
    let cli = invalid(&["delete", "belief", "bad-id"])?;
    let stderr = std::fs::File::create(fixture.root.join(format!(
        "cli-correction-mcp-{}.stderr",
        uuid::Uuid::new_v4()
    )))?;
    let mut child = tokio::process::Command::new(&fixture.mcp)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(stderr)
        .kill_on_drop(true)
        .spawn()?;
    let mut input = child.stdin.take().unwrap();
    let mut output = BufReader::new(child.stdout.take().unwrap());
    for (id, name, arguments) in [
        (1, "delete_belief", json!({"id":"bad-id"})),
        (2, "learning_capabilities", json!({})),
    ] {
        let request = json!({"jsonrpc":"2.0","id":id,"method":"tools/call","params":{"name":name,"arguments":arguments}});
        input.write_all(format!("{request}\n").as_bytes()).await?;
        input.flush().await?;
        let mut line = String::new();
        ensure!(
            output.read_line(&mut line).await? != 0,
            "MCP stopped on correction"
        );
        let response: Value = serde_json::from_str(&line)?;
        ensure!(response.get("error").is_none());
        let value: Value =
            serde_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
        if id == 1 {
            let mcp: NeedsInput = serde_json::from_value(value)?;
            ensure!(
                mcp.issues() == cli.issues(),
                "MCP and CLI disagree about the same identifier"
            );
        } else {
            ensure!(
                value["contract_version"] == 3,
                "corrected conversation cannot continue: {value}"
            );
        }
    }
    drop(input);
    ensure!(child.wait().await?.success());
    Ok(())
}

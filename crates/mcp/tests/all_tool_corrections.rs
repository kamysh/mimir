//! Exercise every advertised tool with an unexpected argument on one session.
#[allow(dead_code)]
#[path = "../../../tests/support/database_observation.rs"]
mod database_observation;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Context, Result};
use mimir_core::{
    db,
    interaction::NeedsInput,
    validation::{Code, Segment},
};
use serde_json::{json, Value};
use std::process::Stdio;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

async fn snapshot() -> Result<database_observation::DatabaseObservation> {
    let mut connection = db::connect(&isolation::fixture().database_config()).await?;
    let tx = connection
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .read_only(true)
        .start()
        .await?;
    let result = database_observation::observe(&tx).await?;
    tx.commit().await?;
    Ok(result)
}

async fn send(
    input: &mut tokio::process::ChildStdin,
    output: &mut BufReader<tokio::process::ChildStdout>,
    request: Value,
) -> Result<Value> {
    input.write_all(format!("{request}\n").as_bytes()).await?;
    input.flush().await?;
    let mut line = String::new();
    ensure!(
        output.read_line(&mut line).await? != 0,
        "MCP server stopped while checking a request"
    );
    Ok(mimir_json::from_str(&line)?)
}

#[tokio::test]
async fn every_advertised_tool_explains_an_unknown_field_without_changes() -> Result<()> {
    let fixture = isolation::fixture();
    let database = fixture.database_config();
    let identity: Uuid = db::connect(&database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let stderr = std::fs::File::create(
        fixture
            .root
            .join(format!("all-tools-corrections-{identity}.stderr")),
    )?;
    let mut child = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir-mcp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(stderr)
        .kill_on_drop(true)
        .spawn()?;
    let mut input = child.stdin.take().context("missing MCP input")?;
    let mut output = BufReader::new(child.stdout.take().context("missing MCP output")?);
    let catalogue = send(
        &mut input,
        &mut output,
        json!({"jsonrpc":"2.0","id":"catalogue","method":"tools/list"}),
    )
    .await?;
    let tools = catalogue["result"]["tools"]
        .as_array()
        .context("missing advertised tools")?;
    ensure!(!tools.is_empty(), "MCP server advertised no tools");
    let before = snapshot().await?;
    for descriptor in tools {
        let name = descriptor["name"].as_str().context("tool without a name")?;
        let request = json!({"jsonrpc":"2.0","id":name,"method":"tools/call","params":{"name":name,"arguments":{"unexpected_agent_field":true}}});
        let response = send(&mut input, &mut output, request).await?;
        ensure!(
            response["id"] == name && response.get("error").is_none(),
            "{name}: correction became a protocol error: {response}"
        );
        let text = response["result"]["content"][0]["text"]
            .as_str()
            .context("missing correction text")?;
        let correction: NeedsInput = mimir_json::from_str(text)?;
        let issue = correction
            .issues()
            .iter()
            .find(|item| {
                item.fault().code == Code::UnknownField
                    && item.fault().path == vec![Segment::Key("unexpected_agent_field".into())]
            })
            .with_context(|| format!("{name}: unknown field was not explained"))?;
        ensure!(
            !issue.fault().message.is_empty()
                && !issue.expected().is_empty()
                && !issue.suggested_correction().is_empty(),
            "{name}: incomplete correction"
        );
    }
    let corrected = send(&mut input, &mut output, json!({"jsonrpc":"2.0","id":"corrected","method":"tools/call","params":{"name":"list_patterns","arguments":{}}})).await?;
    ensure!(
        corrected["id"] == "corrected" && corrected.get("error").is_none(),
        "corrected request failed: {corrected}"
    );
    let value: Value = mimir_json::from_str(
        corrected["result"]["content"][0]["text"]
            .as_str()
            .context("missing corrected result")?,
    )?;
    ensure!(
        value.get("status") != Some(&json!("needs_input")),
        "corrected request still needs input: {value}"
    );
    let after = snapshot().await?;
    ensure!(
        before == after,
        "invalid requests changed stored database records"
    );
    drop(input);
    ensure!(
        child.wait().await?.success(),
        "MCP server did not stop cleanly"
    );
    Ok(())
}

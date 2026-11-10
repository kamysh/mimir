//! Exercise advertised tools with unexpected, missing, mistyped and invalid arguments.
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

async fn check_field(
    input: &mut tokio::process::ChildStdin,
    output: &mut BufReader<tokio::process::ChildStdout>,
    name: &str,
    arguments: Value,
    field: &str,
    code: Code,
) -> Result<()> {
    let response = send(input, output, json!({"jsonrpc":"2.0","id":name,"method":"tools/call","params":{"name":name,"arguments":arguments}})).await?;
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
            item.fault().code == code && item.fault().path == vec![Segment::Key(field.into())]
        })
        .with_context(|| format!("{name}: {field} did not receive {code:?} guidance"))?;
    ensure!(
        !issue.fault().message.is_empty()
            && !issue.expected().is_empty()
            && !issue.suggested_correction().is_empty(),
        "{name}: incomplete correction for {field}"
    );
    if code == Code::InvalidNumber && matches!(field, "limit" | "evidence_per_belief") {
        let guidance =
            format!("{} {}", issue.expected(), issue.suggested_correction()).to_lowercase();
        ensure!(
            guidance.contains("omit")
                && (guidance.contains("positive") || guidance.contains("at least 1")),
            "{name}: zero selection did not explain the available corrections: {guidance}"
        );
    }
    Ok(())
}

#[tokio::test]
async fn advertised_tools_explain_invalid_fields_without_changes() -> Result<()> {
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
    let mut missing_cases = 0;
    let mut wrong_type_cases = 0;
    let mut invalid_uuid_cases = 0;
    let mut invalid_choice_cases = 0;
    let mut zero_selection_cases = 0;
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
        if let Some(required) = descriptor["inputSchema"]["required"].as_array() {
            for field in required {
                let field = field.as_str().context("non-string required field")?;
                check_field(
                    &mut input,
                    &mut output,
                    name,
                    json!({}),
                    field,
                    Code::MissingField,
                )
                .await?;
                missing_cases += 1;
            }
        }
        if let Some(properties) = descriptor["inputSchema"]["properties"].as_object() {
            for (field, schema) in properties {
                let wrong = match schema["type"].as_str() {
                    Some("string" | "object" | "array" | "null") => Some(json!(false)),
                    Some("integer" | "number" | "boolean") => Some(json!("wrong type")),
                    _ => None,
                };
                if let Some(wrong) = wrong {
                    let mut arguments = serde_json::Map::new();
                    arguments.insert(field.clone(), wrong);
                    check_field(
                        &mut input,
                        &mut output,
                        name,
                        Value::Object(arguments),
                        field,
                        Code::WrongType,
                    )
                    .await?;
                    wrong_type_cases += 1;
                }
                if schema["format"] == "uuid" {
                    let mut arguments = serde_json::Map::new();
                    arguments.insert(field.clone(), json!("not-a-uuid"));
                    check_field(
                        &mut input,
                        &mut output,
                        name,
                        Value::Object(arguments),
                        field,
                        Code::MalformedInput,
                    )
                    .await?;
                    invalid_uuid_cases += 1;
                }
                if schema["type"] == "string"
                    && schema["enum"].as_array().is_some_and(|choices| {
                        !choices.contains(&json!("not-an-advertised-choice"))
                    })
                {
                    let mut arguments = serde_json::Map::new();
                    arguments.insert(field.clone(), json!("not-an-advertised-choice"));
                    check_field(
                        &mut input,
                        &mut output,
                        name,
                        Value::Object(arguments),
                        field,
                        Code::MalformedInput,
                    )
                    .await?;
                    invalid_choice_cases += 1;
                }
                if matches!(field.as_str(), "limit" | "evidence_per_belief")
                    && schema["minimum"]
                        .as_i64()
                        .is_some_and(|minimum| minimum >= 1)
                {
                    let mut arguments = serde_json::Map::new();
                    arguments.insert(field.clone(), json!(0));
                    check_field(
                        &mut input,
                        &mut output,
                        name,
                        Value::Object(arguments),
                        field,
                        Code::InvalidNumber,
                    )
                    .await?;
                    zero_selection_cases += 1;
                }
            }
        }
    }
    ensure!(
        missing_cases != 0 && wrong_type_cases != 0,
        "tool catalogue produced no missing-field or wrong-type cases"
    );
    ensure!(
        zero_selection_cases != 0,
        "tool catalogue produced no zero-selection cases"
    );
    println!("Checked {missing_cases} missing-field, {wrong_type_cases} wrong-type, {invalid_uuid_cases} invalid UUID, {invalid_choice_cases} invalid choice and {zero_selection_cases} zero-selection cases across {} advertised tools", tools.len());
    for name in [
        "list_beliefs",
        "list_patterns",
        "get_contradictions",
        "pending_experiences",
        "learning_capabilities",
    ] {
        ensure!(
            tools.iter().any(|tool| tool["name"] == name),
            "{name} is not advertised"
        );
        check_field(
            &mut input,
            &mut output,
            name,
            json!({"unexpected_agent_field": true}),
            "unexpected_agent_field",
            Code::UnknownField,
        )
        .await?;
        let corrected = send(&mut input, &mut output, json!({"jsonrpc":"2.0","id":"corrected","method":"tools/call","params":{"name":name,"arguments":{}}})).await?;
        ensure!(
            corrected["id"] == "corrected"
                && corrected.get("error").is_none()
                && corrected["result"]["isError"] != true,
            "{name}: corrected request failed: {corrected}"
        );
        let value: Value = mimir_json::from_str(
            corrected["result"]["content"][0]["text"]
                .as_str()
                .context("missing corrected result")?,
        )?;
        ensure!(
            value.get("status") != Some(&json!("needs_input")),
            "{name}: corrected request still needs input: {value}"
        );
    }
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

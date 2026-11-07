//! Exercise correction and continued use through the actual stdio server.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{config::Config, interaction::NeedsInput, MimirService};
use serde_json::{json, Value};
use std::process::Stdio;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use uuid::Uuid;

#[tokio::test]
async fn malformed_messages_do_not_execute_and_the_same_connection_recovers() -> Result<()> {
    let fixture = isolation::fixture();
    let service = MimirService::connect(&Config {
        database: fixture.database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
    })
    .await?;
    let project = format!("envelope-session-{}", Uuid::new_v4());
    let experience_id = Uuid::new_v4();
    service
        .record_experience(
            &serde_json::from_value(json!({
                "id":experience_id, "project":project, "context":"preserve this project",
                "action":"exercise envelope admission", "outcome":"unknown", "source":"agent_report"
            }))?,
            0,
        )
        .await?;

    let stderr = std::fs::File::create(
        fixture
            .root
            .join(format!("envelope-session-{}.stderr", Uuid::new_v4())),
    )?;
    let mut child = tokio::process::Command::new(&fixture.mcp)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(stderr)
        .kill_on_drop(true)
        .spawn()?;
    let mut input = child.stdin.take().unwrap();
    let mut output = BufReader::new(child.stdout.take().unwrap());
    let delete = json!({"name":"delete_project", "arguments":{"project":project}});
    let invalid = vec![
        (vec![0xff, b'\n'], -32700, Value::Null),
        (b"{\n".to_vec(), -32700, Value::Null),
        (b"[]\n".to_vec(), -32600, Value::Null),
        (
            format!(
                "{}\n",
                json!({"jsonrpc":"1.0","id":0,"method":"tools/call","params":delete})
            )
            .into_bytes(),
            -32600,
            json!(0),
        ),
        (
            format!(
                "{}\n",
                json!({"jsonrpc":"2.0","id":false,"method":"tools/call","params":delete})
            )
            .into_bytes(),
            -32600,
            Value::Null,
        ),
        (
            format!(
                "{}\n",
                json!({"jsonrpc":"2.0","id":"params","method":"tools/call","params":null})
            )
            .into_bytes(),
            -32602,
            json!("params"),
        ),
    ];
    for (bytes, code, id) in invalid {
        input.write_all(&bytes).await?;
        input.flush().await?;
        let mut line = String::new();
        ensure!(
            output.read_line(&mut line).await? != 0,
            "server exited on malformed input"
        );
        let response: Value = serde_json::from_str(&line)?;
        ensure!(
            response["id"] == id && response["error"]["code"] == code,
            "wrong protocol response: {response}"
        );
        let correction: NeedsInput = serde_json::from_value(response["error"]["data"].clone())?;
        ensure!(!correction.issues().is_empty(), "missing repair details");
    }
    // Notifications receive no response. The next response must belong to the
    // identified request, and the original project data must still exist.
    for message in [
        json!({"jsonrpc":"2.0","method":"tools/call","params":delete}),
        json!({"jsonrpc":"2.0","method":"tools/call","params":null}),
        json!({"jsonrpc":"2.0","method":"notifications/initialized"}),
        json!({"jsonrpc":"2.0","id":"still-usable","method":"tools/call", "params":{"name":"get_experience","arguments":{"id":experience_id}}}),
    ] {
        input.write_all(format!("{message}\n").as_bytes()).await?;
    }
    input.flush().await?;
    let mut line = String::new();
    ensure!(
        output.read_line(&mut line).await? != 0,
        "server failed before corrected request"
    );
    let response: Value = serde_json::from_str(&line)?;
    ensure!(
        response["id"] == "still-usable" && response.get("error").is_none(),
        "connection did not recover: {response}"
    );
    let body: Value =
        serde_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
    ensure!(
        body.to_string().contains(&experience_id.to_string()),
        "invalid message deleted project data: {body}"
    );
    drop(input);
    line.clear();
    ensure!(
        output.read_line(&mut line).await? == 0,
        "notification unexpectedly received a response"
    );
    ensure!(child.wait().await?.success(), "server failed on normal EOF");
    service.delete_project(&project).await?;
    Ok(())
}

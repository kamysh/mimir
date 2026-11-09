//! Real branch-built stdio server: deep invalid input is a correction, and the
//! same connection still accepts a later request. No business rows are written.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Result};
use serde_json::Value;
use std::process::Stdio;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

#[tokio::test]
async fn deep_json_is_diagnosed_without_losing_the_mcp_session() -> Result<()> {
    let fixture = isolation::fixture();
    let stderr = std::fs::File::create(
        fixture
            .root
            .join(format!("deep-json-{}.stderr", uuid::Uuid::new_v4())),
    )?;
    let mut child = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir-mcp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(stderr)
        .kill_on_drop(true)
        .spawn()?;
    let mut input = child.stdin.take().unwrap();
    let mut output = BufReader::new(child.stdout.take().unwrap());
    let depth = 10000;
    let nested = format!("{}null{}", "[".repeat(depth), "]".repeat(depth));
    for (id, message, expected) in [
        (
            1,
            format!(
                r#"{{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{{"name":"list_beliefs","arguments":{{"unexpected":{nested}}}}}}}"#
            ),
            "correction",
        ),
        (
            2,
            format!(
                r#"{{"jsonrpc":"2.0","id":2,"method":"tools/call","params":{{"name":"list_beliefs","arguments":{{"limit":{nested}}}}}}}"#
            ),
            "correction",
        ),
        (
            3,
            format!(
                r#"{{"jsonrpc":"2.0","id":3,"method":"tools/list","params":{{"_meta":{nested}}}}}"#
            ),
            "tools",
        ),
        (
            4,
            format!(
                r#"{{"jsonrpc":"2.0","id":4,"method":"tools/list","params":{{"extra":{nested},"extra":null}}}}"#
            ),
            "duplicate",
        ),
        (0, format!("[{nested},"), "syntax"),
    ] {
        input.write_all(format!("{message}\n").as_bytes()).await?;
        input.flush().await?;
        let mut line = String::new();
        ensure!(
            output.read_line(&mut line).await? != 0,
            "server exited on deep {expected} input"
        );
        let response: Value = mimir_json::from_str(&line)?;
        match expected {
            "correction" => {
                ensure!(response["id"] == id);
                let text = response["result"]["content"][0]["text"].as_str().unwrap();
                let correction: Value = mimir_json::from_str(text)?;
                ensure!(
                    correction["status"] == "needs_input"
                        && correction["business_changes"] == "none"
                );
                ensure!(!correction["issues"].as_array().unwrap().is_empty());
            }
            "tools" => ensure!(response["id"] == id && response["result"]["tools"].is_array()),
            "duplicate" => ensure!(response["id"] == id && response["error"]["code"] == -32600),
            "syntax" => ensure!(response["id"].is_null() && response["error"]["code"] == -32700),
            _ => unreachable!(),
        }
    }
    // A deep notification has no response. The next message must receive its
    // own response, demonstrating that cleanup did not kill or desync stdin.
    input.write_all(format!(r#"{{"jsonrpc":"2.0","method":"notifications/initialized","params":{{"_meta":{nested}}}}}
{{"jsonrpc":"2.0","id":6,"method":"tools/list"}}
"#).as_bytes()).await?;
    input.flush().await?;
    let mut line = String::new();
    ensure!(output.read_line(&mut line).await? != 0);
    let response: Value = mimir_json::from_str(&line)?;
    ensure!(response["id"] == 6 && response["result"]["tools"].is_array());
    drop(input);
    ensure!(child.wait().await?.success());
    Ok(())
}

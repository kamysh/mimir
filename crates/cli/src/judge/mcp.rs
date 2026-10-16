use anyhow::{anyhow, bail, ensure, Result};
use serde_json::{json, Value};
use std::path::Path;
use std::process::Stdio;
use std::time::{Duration, Instant};
use tokio::io::{AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStdin, ChildStdout, Command};

const MAX_MESSAGE: usize = 1024 * 1024;

pub struct Client {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    next_id: u64,
    deadline: Instant,
    allowed_tools: Vec<Value>,
}

impl Client {
    pub async fn start(
        command: &str,
        args: &[String],
        config: &Path,
        seconds: u64,
    ) -> Result<Self> {
        let mut process = Command::new(command);
        process
            .args(args)
            .env("MIMIR_CONFIG", config)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .kill_on_drop(true);
        // A separate process group lets timeout cleanup include grandchildren.
        unsafe {
            process.pre_exec(|| {
                if libc::setpgid(0, 0) == -1 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let mut child = process
            .spawn()
            .map_err(|_| anyhow!("unable to start MCP child"))?;
        let input = child
            .stdin
            .take()
            .ok_or_else(|| anyhow!("MCP stdin unavailable"))?;
        let output = BufReader::new(
            child
                .stdout
                .take()
                .ok_or_else(|| anyhow!("MCP stdout unavailable"))?,
        );
        let mut client = Self {
            child,
            input,
            output,
            next_id: 1,
            deadline: Instant::now() + Duration::from_secs(seconds),
            allowed_tools: Vec::new(),
        };
        let response = client
            .request(
                "initialize",
                json!({"protocolVersion":"2024-11-05",
            "capabilities":{},"clientInfo":{"name":"mimir-judge","version":"1"}}),
            )
            .await?;
        ensure!(
            response.get("protocolVersion").and_then(Value::as_str) == Some("2024-11-05"),
            "unsupported MCP protocol"
        );
        client
            .notify("notifications/initialized", json!({}))
            .await?;
        client.allowed_tools = client.validate_tools().await?;
        Ok(client)
    }

    pub fn allowed_tools(&self) -> &[Value] {
        &self.allowed_tools
    }

    fn remaining(&self) -> Result<Duration> {
        self.deadline
            .checked_duration_since(Instant::now())
            .filter(|time| !time.is_zero())
            .ok_or_else(|| anyhow!("MCP deadline exceeded"))
    }

    async fn send(&mut self, message: Value) -> Result<()> {
        let mut bytes = serde_json::to_vec(&message)?;
        ensure!(bytes.len() < MAX_MESSAGE, "MCP request exceeds limit");
        bytes.push(b'\n');
        tokio::time::timeout(self.remaining()?, async {
            self.input.write_all(&bytes).await?;
            self.input.flush().await
        })
        .await
        .map_err(|_| anyhow!("MCP write timeout"))??;
        Ok(())
    }

    async fn notify(&mut self, method: &str, params: Value) -> Result<()> {
        self.send(json!({"jsonrpc":"2.0","method":method,"params":params}))
            .await
    }

    async fn line(&mut self) -> Result<Value> {
        let mut bytes = Vec::new();
        loop {
            let byte = tokio::time::timeout(self.remaining()?, self.output.read_u8())
                .await
                .map_err(|_| anyhow!("MCP read timeout"))?
                .map_err(|_| anyhow!("MCP stream ended"))?;
            if byte == b'\n' {
                break;
            }
            ensure!(bytes.len() < MAX_MESSAGE, "MCP response exceeds limit");
            bytes.push(byte);
        }
        serde_json::from_slice(&bytes).map_err(|_| anyhow!("malformed MCP response"))
    }

    pub async fn request(&mut self, method: &str, params: Value) -> Result<Value> {
        let id = self.next_id;
        self.next_id = self
            .next_id
            .checked_add(1)
            .ok_or_else(|| anyhow!("MCP request ID overflow"))?;
        self.send(json!({"jsonrpc":"2.0","id":id,"method":method,"params":params}))
            .await?;
        let mut notifications = 0;
        loop {
            let response = self.line().await?;
            ensure!(
                response.get("jsonrpc").and_then(Value::as_str) == Some("2.0"),
                "invalid MCP envelope"
            );
            if response.get("id").is_none() {
                ensure!(
                    response.get("method").and_then(Value::as_str).is_some(),
                    "invalid MCP notification"
                );
                notifications += 1;
                ensure!(notifications <= 64, "too many MCP notifications");
                continue;
            }
            ensure!(
                response["id"].as_u64() == Some(id),
                "unexpected MCP response ID"
            );
            if response.get("error").is_some() {
                bail!("MCP request failed");
            }
            return response
                .get("result")
                .cloned()
                .ok_or_else(|| anyhow!("missing MCP result"));
        }
    }

    async fn validate_tools(&mut self) -> Result<Vec<Value>> {
        let result = self.request("tools/list", json!({})).await?;
        let tools = result["tools"]
            .as_array()
            .ok_or_else(|| anyhow!("invalid MCP tool list"))?;
        let mut allowed = Vec::new();
        for (name, required) in [
            (
                "pending_experiences",
                &[("project", "string"), ("limit", "integer")][..],
            ),
            ("get_experience", &[("id", "string")][..]),
            (
                "review_experience",
                &[
                    ("review", "object"),
                    ("expected_review_revision", "integer"),
                ][..],
            ),
            ("experience_history", &[("id", "string")][..]),
            (
                "query_relevant",
                &[
                    ("context", "string"),
                    ("project", "string"),
                    ("limit", "integer"),
                ][..],
            ),
            (
                "query_learning_context",
                &[
                    ("context", "string"),
                    ("project", "string"),
                    ("limit", "integer"),
                ][..],
            ),
            (
                "explain_belief",
                &[
                    ("id", "string"),
                    ("limit", "integer"),
                    ("offset", "integer"),
                ][..],
            ),
            ("get_belief", &[("id", "string")][..]),
            (
                "query_intervention",
                &[("id", "string"), ("value", "number")][..],
            ),
            ("get_contradictions", &[("project", "string")][..]),
        ] {
            let schema = tools
                .iter()
                .find(|tool| tool["name"] == name)
                .and_then(|tool| tool.get("inputSchema"))
                .ok_or_else(|| anyhow!("required MCP tool unavailable: {name}"))?;
            for (key, kind) in required {
                ensure!(
                    schema["properties"][key]["type"] == *kind,
                    "unsupported MCP schema: {name}"
                );
            }
            if name == "review_experience" {
                for (key, kind) in [
                    ("experience_id", "string"),
                    ("experience_revision", "integer"),
                    ("reviewer", "string"),
                ] {
                    ensure!(
                        schema["properties"]["review"]["properties"][key]["type"] == kind,
                        "unsupported MCP review schema"
                    );
                }
            }
            if name != "pending_experiences" {
                allowed.push(
                    tools
                        .iter()
                        .find(|tool| tool["name"] == name)
                        .unwrap()
                        .clone(),
                );
            }
        }
        Ok(allowed)
    }

    pub async fn tool(&mut self, name: &str, args: Value) -> Result<Value> {
        let result = self
            .request("tools/call", json!({"name":name,"arguments":args}))
            .await?;
        ensure!(
            result.get("isError").and_then(Value::as_bool) != Some(true),
            "MCP tool failed"
        );
        let content = result["content"]
            .as_array()
            .ok_or_else(|| anyhow!("invalid MCP tool result"))?;
        ensure!(
            content.len() == 1 && content[0]["type"] == "text",
            "invalid MCP tool content"
        );
        let text = content[0]["text"]
            .as_str()
            .ok_or_else(|| anyhow!("invalid MCP tool text"))?;
        serde_json::from_str(text).map_err(|_| anyhow!("invalid MCP tool JSON"))
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        if let Some(pid) = self.child.id() {
            // The child was placed in its own process group before exec.
            let _ = unsafe { libc::kill(-(pid as i32), libc::SIGKILL) };
        }
        let _ = self.child.start_kill();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn rejects_malformed_transport_and_kills_descendants_on_timeout() {
        let crashed = Client::start(
            "bash",
            &["-c".into(), "exit 7".into()],
            Path::new("/var/tmp/mimir/step5/unused-config"),
            2,
        )
        .await;
        assert!(crashed.is_err());
        let malformed = Client::start(
            "bash",
            &["-c".into(), "read -r request; printf 'not-json\\n'".into()],
            Path::new("/var/tmp/mimir/step5/unused-config"),
            2,
        )
        .await;
        assert!(malformed.is_err());

        let pid_file = format!("/var/tmp/mimir/step5/descendant-{}.pid", std::process::id());
        let script = format!(
            "sleep 30 & child=$!; printf '%s' \"$child\" > '{}'; wait",
            pid_file
        );
        let timed_out = Client::start(
            "bash",
            &["-c".into(), script],
            Path::new("/var/tmp/mimir/step5/unused-config"),
            1,
        )
        .await;
        assert!(timed_out.is_err());
        let pid: u32 = std::fs::read_to_string(&pid_file).unwrap().parse().unwrap();
        let mut alive = true;
        for _ in 0..20 {
            let proc_state = std::fs::read_to_string(format!("/proc/{pid}/stat"));
            alive = proc_state.is_ok_and(|state| state.split_whitespace().nth(2) != Some("Z"));
            if !alive {
                break;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
        assert!(!alive, "timeout left a live descendant");
        std::fs::remove_file(pid_file).unwrap();
    }
}

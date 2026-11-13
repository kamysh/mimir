use anyhow::{anyhow, bail, ensure, Result};
use mimir_core::validation::{Fault, Refusal, RefusalKind};
use serde_json::{json, Value};
use std::path::Path;
use std::process::Stdio;
use std::sync::Arc;
#[cfg(test)]
use std::time::Duration;
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStdin, ChildStdout, Command};
use tokio::sync::Mutex;

#[derive(Debug)]
pub struct CandidateConflict(pub Fault);

#[derive(Debug)]
pub struct UndeclaredBeliefCandidate(pub Fault);

#[derive(Debug)]
pub struct McpApplicationError(pub Fault);

impl std::fmt::Display for McpApplicationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0.message)
    }
}

impl std::error::Error for McpApplicationError {}

impl std::fmt::Display for CandidateConflict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0.message)
    }
}

impl std::error::Error for CandidateConflict {}

impl std::fmt::Display for UndeclaredBeliefCandidate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0.message)
    }
}

impl std::error::Error for UndeclaredBeliefCandidate {}

#[cfg(test)]
fn candidate_conflict(error: &Value) -> bool {
    Refusal::from_mcp(error).is_some_and(|r| r.kind == RefusalKind::CandidateConflict)
}

#[cfg(test)]
fn undeclared_belief_candidate(error: &Value) -> bool {
    Refusal::from_mcp(error).is_some_and(|r| r.kind == RefusalKind::UndeclaredCandidate)
}

pub struct Client {
    child: Child,
    process_group: Option<i32>,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    stderr: Arc<Mutex<Vec<u8>>>,
    stderr_task: Option<tokio::task::JoinHandle<()>>,
    allowed_tools: Vec<Value>,
}

impl Client {
    pub async fn start(command: &str, args: &[String], config: &Path) -> Result<Self> {
        let mut process = Command::new(command);
        process
            .args(args)
            .env("MIMIR_CONFIG", config)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .kill_on_drop(true);
        // A separate process group lets cancellation cleanup include grandchildren.
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
            .map_err(|error| anyhow!("unable to start MCP child: {error}"))?;
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
        let mut error_pipe = child
            .stderr
            .take()
            .ok_or_else(|| anyhow!("MCP stderr unavailable"))?;
        let stderr = Arc::new(Mutex::new(Vec::new()));
        let captured = Arc::clone(&stderr);
        let stderr_task = tokio::spawn(async move {
            let mut chunk = [0u8; 1024];
            while let Ok(size) = error_pipe.read(&mut chunk).await {
                if size == 0 {
                    break;
                }
                let mut bytes = captured.lock().await;
                bytes.extend_from_slice(&chunk[..size]);
            }
        });
        let mut client = Self {
            process_group: child.id().map(|pid| pid as i32),
            child,
            input,
            output,
            stderr,
            stderr_task: Some(stderr_task),
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
        let capabilities = client.tool("learning_capabilities", json!({})).await?;
        validate_learning_capabilities(&capabilities)?;
        Ok(client)
    }

    pub fn allowed_tools(&self) -> &[Value] {
        &self.allowed_tools
    }

    async fn send(&mut self, message: Value) -> Result<()> {
        let mut bytes = serde_json::to_vec(&message)?;
        bytes.push(b'\n');
        self.input.write_all(&bytes).await?;
        self.input.flush().await?;
        Ok(())
    }

    async fn notify(&mut self, method: &str, params: Value) -> Result<()> {
        self.send(json!({"jsonrpc":"2.0","method":method,"params":params}))
            .await
    }

    async fn line(&mut self) -> Result<Value> {
        let mut bytes = Vec::new();
        let read = tokio::select! {
            biased;
            read = self.output.read_until(b'\n', &mut bytes) => read,
            status = self.child.wait() => {
                status?;
                Ok(0)
            }
        };
        if read? == 0 || bytes.last() != Some(&b'\n') {
            self.stop().await;
            let stderr = self.stderr.lock().await;
            let detail = String::from_utf8_lossy(&stderr);
            if detail.is_empty() {
                bail!("MCP stream ended");
            }
            bail!("MCP stream ended: {detail}");
        }
        serde_json::from_slice(&bytes).map_err(|error| {
            super::state::SourceFailure::json("malformed MCP response", &bytes, error).into()
        })
    }

    pub async fn request(&mut self, method: &str, params: Value) -> Result<Value> {
        let review_call = method == "tools/call" && params["name"] == "review_experience";
        let id = uuid::Uuid::new_v4().simple().to_string();
        self.send(json!({"jsonrpc":"2.0","id":id,"method":method,"params":params}))
            .await?;
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
                continue;
            }
            ensure!(
                response["id"].as_str() == Some(id.as_str()),
                "unexpected MCP response ID"
            );
            if response.get("error").is_some() {
                if method == "tools/call" {
                    if let Some(refusal) = Refusal::from_mcp(&response["error"]) {
                        return Err(match refusal.kind {
                            RefusalKind::CandidateConflict if review_call => {
                                CandidateConflict(refusal.fault).into()
                            }
                            RefusalKind::UndeclaredCandidate => {
                                UndeclaredBeliefCandidate(refusal.fault).into()
                            }
                            _ => McpApplicationError(refusal.fault).into(),
                        });
                    }
                }
                let code = response["error"]["code"].as_i64().unwrap_or(-1);
                let message = response["error"]["message"]
                    .as_str()
                    .unwrap_or("unspecified MCP failure");
                // An unclassified error is not a validation refusal and cannot
                // justify telling the model that no mutation occurred.
                bail!("MCP error {code}: {message}");
            }
            return response
                .get("result")
                .cloned()
                .ok_or_else(|| anyhow!("missing MCP result"));
        }
    }

    async fn validate_tools(&mut self) -> Result<Vec<Value>> {
        let result = self.request("tools/list", json!({})).await?;
        checked_tools(&result)
    }

    pub async fn tool(&mut self, name: &str, args: Value) -> Result<Value> {
        let result = self
            .request("tools/call", json!({"name":name,"arguments":args}))
            .await?;
        if result.get("isError").and_then(Value::as_bool) == Some(true) {
            bail!("MCP tool returned an unclassified isError result");
        }
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
        serde_json::from_str(text).map_err(|error| {
            super::state::SourceFailure::json("invalid MCP tool JSON", text.as_bytes(), error)
                .into()
        })
    }

    pub async fn stop(&mut self) {
        if let Some(group) = self.process_group.take() {
            let _ = unsafe { libc::kill(-group, libc::SIGKILL) };
        }
        let _ = self.child.start_kill();
        let _ = self.child.wait().await;
        if let Some(reader) = self.stderr_task.take() {
            let _ = reader.await;
        }
    }
}

// Mimir.JudgeToolCatalogue.check: first matching definitions, exact property
// types, and host-only demands excluded from the model tool catalogue.
fn checked_tools(result: &Value) -> Result<Vec<Value>> {
    let tools = result["tools"]
        .as_array()
        .ok_or_else(|| anyhow!("invalid MCP tool list"))?;
    let mut allowed = Vec::new();
    for (name, required) in [
        (
            "pending_experiences",
            &[
                ("project", "string"),
                ("limit", "integer"),
                ("exclude_ids", "array"),
            ][..],
        ),
        ("learning_capabilities", &[][..]),
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
            "query_document",
            &[
                ("context", "string"),
                ("project", "string"),
                ("limit", "integer"),
            ][..],
        ),
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
        if name == "learning_capabilities" {
            ensure!(
                schema["type"] == "object",
                "unsupported MCP capability schema"
            );
        }
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
                ("rationale", "string"),
                ("assessments", "array"),
                ("extracted_items", "array"),
                ("source_coverage", "array"),
                ("feedback", "array"),
                ("links", "array"),
                ("superseded_beliefs", "array"),
                ("candidates", "array"),
                ("candidate_feedback", "array"),
                ("candidate_links", "array"),
            ] {
                ensure!(
                    schema["properties"]["review"]["properties"][key]["type"] == kind,
                    "unsupported MCP review schema"
                );
            }
        }
        if !matches!(name, "pending_experiences" | "learning_capabilities") {
            allowed.push(
                tools
                    .iter()
                    .find(|tool| tool["name"] == name)
                    .unwrap()
                    .clone(),
            );
        }
    }
    for name in ["get_lesson_assessment", "lesson_assessment_history"] {
        if let Some(tool) = tools.iter().find(|tool| tool["name"] == name) {
            for key in ["project", "belief_id", "scope", "rubric"] {
                ensure!(
                    tool["inputSchema"]["properties"][key]["type"] == "string",
                    "unsupported assessment schema"
                );
            }
            allowed.push(tool.clone());
        }
    }
    if let Some(tool) = tools.iter().find(|t| t["name"] == "get_learning_review") {
        ensure!(
            tool["inputSchema"]["properties"]["id"]["type"] == "string",
            "unsupported review receipt schema"
        );
        allowed.push(tool.clone());
    }
    Ok(allowed)
}

// Mimir.LearningCapabilities.admit 3 1. Compatibility is independent of the
// user-controlled package version, and only gates the optional judge client.
fn validate_learning_capabilities(capabilities: &Value) -> Result<()> {
    ensure!(capabilities.is_object(), "expected an object");
    let integer = |key: &str| -> Result<u64> {
        capabilities
            .get(key)
            .ok_or_else(|| anyhow!("missing required field: {key}"))?
            .as_u64()
            .ok_or_else(|| anyhow!("expected an unsigned integer: {key}"))
    };
    let contract = integer("contract_version")?;
    let model = integer("assessment_model_version")?;
    let requirements = [
        ("source_coverage", "source coverage is unavailable"),
        (
            "typed_learning_items",
            "typed learning items are unavailable",
        ),
        (
            "revision_owned_assessments",
            "revision-owned assessments are unavailable",
        ),
        (
            "legacy_graph_probability_unchanged",
            "legacy graph probability compatibility is unavailable",
        ),
    ];
    let mut flags = [false; 4];
    // Decode the complete record before semantic validation, matching fields
    // followed by validate in LearningCapabilities.admit.
    for (index, (key, _)) in requirements.iter().enumerate() {
        flags[index] = capabilities
            .get(key)
            .ok_or_else(|| anyhow!("missing required field: {key}"))?
            .as_bool()
            .ok_or_else(|| anyhow!("expected a boolean: {key}"))?;
    }
    ensure!(contract == 3, "unsupported learning contract version");
    ensure!(model == 1, "unsupported assessment model version");
    for (supported, (_, message)) in flags.into_iter().zip(requirements) {
        ensure!(supported, "{message}");
    }
    Ok(())
}

impl Drop for Client {
    fn drop(&mut self) {
        if let Some(group) = self.process_group.take() {
            // The child was placed in its own process group before exec.
            let _ = unsafe { libc::kill(-group, libc::SIGKILL) };
        }
        let _ = self.child.start_kill();
        if let Some(reader) = self.stderr_task.take() {
            reader.abort();
        }
    }
}

#[cfg(test)]
#[path = "mcp_startup_tests.rs"]
mod startup_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_known_candidate_conflicts_are_deferred() {
        assert!(candidate_conflict(
            &json!({"code":-32000,"message":"candidate key has a different declaration", "data":Refusal::candidate_conflict()})
        ));
        assert!(!candidate_conflict(
            &json!({"code":-32000,"message":"database unavailable"})
        ));
        assert!(!candidate_conflict(
            &json!({"code":-32001,"message":"candidate key has a different declaration"})
        ));
        assert!(undeclared_belief_candidate(&json!({
            "code":-32000,
            "message":"candidate belief reference must be declared in this review",
            "data":Refusal::undeclared_candidate()
        })));
        assert!(!undeclared_belief_candidate(&json!({
            "code":-32001,
            "message":"candidate belief reference must be declared in this review"
        })));
        assert!(!undeclared_belief_candidate(&json!({
            "code":-32000,
            "message":"database unavailable"
        })));
        assert!(!candidate_conflict(
            &json!({"code":-32000,"message":"candidate key has a different declaration"})
        ));
    }

    #[tokio::test]
    async fn rejects_malformed_transport_and_kills_descendants_on_cancellation() {
        let crashed = Client::start(
            "bash",
            &[
                "-c".into(),
                "read -r request; echo startup-failure >&2; exit 7".into(),
            ],
            Path::new("/var/tmp/mimir/step5/unused-config"),
        )
        .await;
        assert!(crashed
            .err()
            .unwrap()
            .to_string()
            .contains("startup-failure"));
        let malformed = Client::start(
            "bash",
            &["-c".into(), "read -r request; printf 'not-json\\n'".into()],
            Path::new("/var/tmp/mimir/step5/unused-config"),
        )
        .await;
        assert!(malformed.is_err());

        let pid_file =
            std::env::temp_dir().join(format!("mimir-descendant-{}.pid", uuid::Uuid::new_v4()));
        let script = format!(
            "sleep 30 & child=$!; printf '%s' \"$child\" > '{}'; wait",
            pid_file.display()
        );
        let cancelled = tokio::time::timeout(
            Duration::from_secs(1),
            Client::start(
                "bash",
                &["-c".into(), script],
                Path::new("/var/tmp/mimir/step5/unused-config"),
            ),
        )
        .await;
        assert!(cancelled.is_err());
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
        assert!(!alive, "cancellation left a live descendant");
        std::fs::remove_file(pid_file).unwrap();
    }
}

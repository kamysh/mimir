use anyhow::{anyhow, bail, ensure, Result};
use mimir_core::validation::{Fault, Refusal, RefusalKind};
use serde_json::{json, Value};
use std::path::Path;
use std::process::Stdio;
use tokio::io::{AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStdin, ChildStdout, Command};
use tokio::task::JoinHandle;

struct StderrCapture {
    bytes: Vec<u8>,
    error: Option<std::io::Error>,
}

#[derive(Debug)]
pub struct McpStreamEnded {
    pub stderr: Vec<u8>,
    pub issues: Vec<String>,
}

impl std::fmt::Display for McpStreamEnded {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "MCP stream ended")?;
        if !self.stderr.is_empty() {
            write!(output, ": {}", String::from_utf8_lossy(&self.stderr))?;
        }
        for issue in &self.issues {
            write!(output, "; {issue}")?;
        }
        Ok(())
    }
}
impl std::error::Error for McpStreamEnded {}

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

/// Own the exact effective configuration handed to one MCP child. The source
/// file can change after admission without changing this child's database.
pub struct PreparedConfig {
    _directory: super::harness::RunDir,
    path: std::path::PathBuf,
}

#[cfg(test)]
mod prepared_config_tests {
    use super::PreparedConfig;
    use crate::judge::{config, harness::RunDir};
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    #[test]
    fn prepared_mcp_config_keeps_selected_settings_and_cleans_up() {
        let work = RunDir::new_in(&std::env::temp_dir()).unwrap();
        let source_text = format!(
            "config_version=1\n[logging]\ndirectory={}\n[database]\nhost='127.0.0.1'\nport=15432\ndbname='snapshot-selected'\nuser='snapshot-user'\npassword='fixture-only-secret'\nssl_mode='verify-full'\nssl_root_cert='/fixture/root.pem'\n[judge]\n[llm]\nbackend='command'\nmodel='fixture-model'\ncommand='/bin/true'\n",
            toml::Value::String(work.path().join("logs").display().to_string())
        );
        let original = work.write("original.toml", source_text.as_bytes()).unwrap();
        let selected = config::load(Some(&original)).unwrap();
        assert_eq!(selected.core.database.dbname, "snapshot-selected");
        let prepared = PreparedConfig::new(&selected, work.path()).unwrap();
        let child_path = prepared.path().to_owned();
        assert_ne!(child_path, original);
        assert_ne!(
            std::fs::metadata(&child_path).unwrap().ino(),
            std::fs::metadata(&original).unwrap().ino()
        );
        std::fs::write(
            &original,
            source_text.replace("snapshot-selected", "snapshot-replaced"),
        )
        .unwrap();
        let (child, operations) =
            mimir_core::config::Config::load_with_operations(&child_path).unwrap();
        assert_eq!(
            toml::to_string(&child).unwrap(),
            toml::to_string(&selected.core).unwrap()
        );
        assert_eq!(
            operations.header().unwrap(),
            selected.operations.header().unwrap()
        );
        assert_eq!(
            config::load(Some(&original)).unwrap().core.database.dbname,
            "snapshot-replaced"
        );
        assert_eq!(
            std::fs::metadata(&child_path).unwrap().permissions().mode() & 0o077,
            0
        );
        assert_eq!(
            std::fs::metadata(child_path.parent().unwrap())
                .unwrap()
                .permissions()
                .mode()
                & 0o077,
            0
        );
        drop(prepared);
        assert!(!child_path.exists());
        assert!(original.exists());
    }
}

impl PreparedConfig {
    pub fn new(settings: &super::config::RuntimeConfig, directory: &Path) -> Result<Self> {
        let work = super::harness::RunDir::new_in(directory)?;
        let text = format!(
            "{}\n{}",
            settings.operations.header()?,
            toml::to_string(&settings.core)?
        );
        let path = work.write("mcp-config.toml", text.as_bytes())?;
        ensure!(
            path != settings.path,
            "private MCP configuration must differ from its source"
        );
        let observed = super::config::load(Some(&path))?;
        ensure!(
            toml::to_string(&observed.core)? == toml::to_string(&settings.core)?
                && observed.operations.header()? == settings.operations.header()?,
            "private MCP configuration differs from the selected settings; retry after correcting the configuration"
        );
        Ok(Self {
            _directory: work,
            path,
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }
}

pub struct Client {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    stderr: Option<JoinHandle<StderrCapture>>,
    next_id: u64,
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
        let stderr = tokio::spawn(async move {
            let mut bytes = Vec::new();
            let error = error_pipe.read_to_end(&mut bytes).await.err();
            StderrCapture { bytes, error }
        });
        let mut client = Self {
            child,
            input,
            output,
            stderr: Some(stderr),
            next_id: 1,
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
        let message = mimir_json::Document::new(message);
        let mut bytes = mimir_json::to_vec(&message)?;
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
        loop {
            let byte = self.output.read_u8().await;
            let byte = match byte {
                Ok(byte) => byte,
                Err(error) => return Err(self.ended(error).await.into()),
            };
            if byte == b'\n' {
                break;
            }
            bytes.push(byte);
        }
        mimir_json::from_slice(&bytes).map_err(|error| {
            super::state::SourceFailure::json("malformed MCP response", &bytes, error).into()
        })
    }

    async fn ended(&mut self, cause: std::io::Error) -> McpStreamEnded {
        let mut issues = vec![format!("response read: {cause}")];
        // EOF means no further protocol reply can arrive. Stop the exact owned
        // group before reaping its leader, so descendants cannot retain pipes
        // or embedding work and the group ID cannot have been reused.
        if let Some(pid) = self.child.id() {
            if unsafe { libc::kill(-(pid as i32), libc::SIGKILL) } == -1 {
                let error = std::io::Error::last_os_error();
                if error.raw_os_error() != Some(libc::ESRCH) {
                    issues.push(format!("child-group cleanup: {error}"));
                }
            }
        }
        if let Err(error) = self.child.start_kill() {
            issues.push(format!("child cleanup: {error}"));
        }
        if let Err(error) = self.child.wait().await {
            issues.push(format!("child wait: {error}"));
        }
        // Keep the handle in self while awaiting it: cancelling this future
        // must still let Drop abort the reader rather than detach it.
        let joined = match self.stderr.as_mut() {
            Some(reader) => Some(reader.await),
            None => None,
        };
        self.stderr.take();
        let mut stderr = Vec::new();
        match joined {
            Some(Ok(capture)) => {
                stderr = capture.bytes;
                if let Some(error) = capture.error {
                    issues.push(format!("stderr read: {error}"));
                }
            }
            Some(Err(error)) => issues.push(format!("stderr task: {error}")),
            None => issues.push("stderr was already collected".into()),
        }
        McpStreamEnded { stderr, issues }
    }

    pub fn request<'a>(
        &'a mut self,
        method: &'a str,
        params: Value,
    ) -> impl std::future::Future<Output = Result<mimir_json::Document>> + Send + 'a {
        let params = mimir_json::Document::new(params);
        async move {
            let review_call = method == "tools/call" && params["name"] == "review_experience";
            let id = self.next_id;
            self.next_id = self
                .next_id
                .checked_add(1)
                .ok_or_else(|| anyhow!("MCP request ID overflow"))?;
            self.send(json!({"jsonrpc":"2.0","id":id,"method":method,"params":params}))
                .await?;
            loop {
                let response = mimir_json::Document::new(self.line().await?);
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
                    response["id"].as_u64() == Some(id),
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
                    .map(|v| mimir_json::Document::new(mimir_json::clone_value(v)))
                    .ok_or_else(|| anyhow!("missing MCP result"));
            }
        }
    }

    async fn validate_tools(&mut self) -> Result<Vec<Value>> {
        let result = self.request("tools/list", json!({})).await?;
        checked_tools(&result)
    }

    pub fn tool<'a>(
        &'a mut self,
        name: &'a str,
        args: Value,
    ) -> impl std::future::Future<Output = Result<mimir_json::Document>> + Send + 'a {
        let args = mimir_json::Document::new(args);
        async move {
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
            mimir_json::from_str(text).map_err(|error| {
                super::state::SourceFailure::json("invalid MCP tool JSON", text.as_bytes(), error)
                    .into()
            })
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
                    .map(|tool| mimir_json::Document::new(mimir_json::clone_value(tool)))
                    .unwrap(),
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
            allowed.push(mimir_json::Document::new(mimir_json::clone_value(tool)));
        }
    }
    if let Some(tool) = tools.iter().find(|t| t["name"] == "get_learning_review") {
        ensure!(
            tool["inputSchema"]["properties"]["id"]["type"] == "string",
            "unsupported review receipt schema"
        );
        allowed.push(mimir_json::Document::new(mimir_json::clone_value(tool)));
    }
    Ok(allowed
        .into_iter()
        .map(mimir_json::Document::into_value)
        .collect())
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
        for tool in self.allowed_tools.drain(..) {
            mimir_json::drop_value(tool);
        }
        if let Some(pid) = self.child.id() {
            // The child was placed in its own process group before exec.
            let _ = unsafe { libc::kill(-(pid as i32), libc::SIGKILL) };
        }
        let _ = self.child.start_kill();
        if let Some(reader) = self.stderr.take() {
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

    #[tokio::test]
    async fn ended_stream_keeps_complete_stderr_before_returning() {
        let work = crate::judge::harness::RunDir::new_in(&std::env::temp_dir()).unwrap();
        let mut bytes = format!(
            "first diagnostic\n{}\nactual final explanation\n",
            "λ".repeat(64 * 1024 + 1)
        )
        .into_bytes();
        bytes.push(0xff);
        let path = work.write("stderr.bin", &bytes).unwrap();
        let error = Client::start(
            "bash",
            &[
                "-c".into(),
                "read -r request; cat -- \"$1\" >&2; exit 7".into(),
                "fixture".into(),
                path.display().to_string(),
            ],
            &work.path().join("unused-config"),
        )
        .await
        .err()
        .expect("the fixture exits without a protocol reply");
        let ended = error
            .downcast_ref::<McpStreamEnded>()
            .expect("terminal evidence must remain available");
        assert_eq!(
            ended.stderr, bytes,
            "neither a prefix nor a tail may replace the evidence"
        );
        assert!(error.to_string().contains("actual final explanation"));
        assert!(
            !ended
                .issues
                .iter()
                .any(|issue| issue.starts_with("stderr ")),
            "stderr collection did not complete: {:?}",
            ended.issues
        );
    }

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

        use tokio::io::AsyncBufReadExt;
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let script = format!(
            "exec 3<>/dev/tcp/127.0.0.1/{port}; bash -c 'exec 4<>/dev/tcp/127.0.0.1/{port}; printf \"%s %s\\n\" \"$PPID\" \"$$\" >&4; read -r -u 4 stop' & descendant=$!; printf '%s %s\\n' \"$$\" \"$descendant\" >&3; wait",
            port = listener.local_addr().unwrap().port()
        );
        // Each process retains a connection until it stops. The descendant
        // announces its own identity after opening its lifetime connection.
        let startup = tokio::spawn(async move {
            Client::start(
                "bash",
                &["-c".into(), script],
                Path::new("/var/tmp/mimir/step5/unused-config"),
            )
            .await
        });
        let (transport, _) = listener.accept().await.unwrap();
        let mut transport = BufReader::new(transport);
        let mut ready = String::new();
        assert!(transport.read_line(&mut ready).await.unwrap() > 0);
        let pids: Vec<u32> = ready
            .split_whitespace()
            .map(|pid| pid.parse().unwrap())
            .collect();
        assert_eq!(pids.len(), 2);
        assert_ne!(
            pids[0], pids[1],
            "the fixture must include a real descendant"
        );
        let (descendant, _) = listener.accept().await.unwrap();
        let mut descendant = BufReader::new(descendant);
        let mut descendant_ready = String::new();
        assert!(descendant.read_line(&mut descendant_ready).await.unwrap() > 0);
        assert_eq!(descendant_ready, ready);
        assert!(
            !startup.is_finished(),
            "startup unexpectedly completed without an MCP reply"
        );
        startup.abort();
        assert!(matches!(startup.await, Err(error) if error.is_cancelled()));
        let mut remaining = Vec::new();
        transport.read_to_end(&mut remaining).await.unwrap();
        assert!(remaining.is_empty());
        descendant.read_to_end(&mut remaining).await.unwrap();
        assert!(remaining.is_empty());
    }
}

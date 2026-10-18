//! Text-only harness adapters. Model output is a request to the host, never
//! direct access to the database or MCP process.
use super::{
    config::{Backend as Kind, LlmConfig},
    process,
    runner::{Action, Backend},
    state::SourceFailure,
};
use anyhow::{anyhow, bail, ensure, Context, Result};
use mimir_core::learning::ExperienceState;
use serde::Deserialize;
use serde_json::{json, Value};
use std::fs::{self, OpenOptions};
use std::future::Future;
use std::io::{Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::pin::Pin;
use std::time::Duration;
use uuid::Uuid;

const MAX_PAYLOAD: usize = 2 * 1024 * 1024;
const MAX_ANSWER: u64 = 8 * 1024 * 1024;

const SCHEMA: &str = r#"{"type":"object","additionalProperties":false,"properties":{"calls":{"type":"array","maxItems":1,"items":{"type":"object","additionalProperties":false,"properties":{"name":{"type":"string"},"arguments_json":{"type":"string"}},"required":["name","arguments_json"]}}},"required":["calls"]}"#;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Reply {
    calls: Vec<Call>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Call {
    name: String,
    arguments_json: String,
}

struct RunDir(PathBuf);
impl RunDir {
    fn new() -> Result<Self> {
        let base = Path::new("/var/tmp/mimir");
        if !base.exists() {
            fs::DirBuilder::new().mode(0o700).create(base)?;
        }
        ensure!(
            base.is_dir() && !fs::symlink_metadata(base)?.file_type().is_symlink(),
            "unsafe harness temp root"
        );
        let path = base.join(format!("judge-{}", Uuid::new_v4()));
        fs::DirBuilder::new().mode(0o700).create(&path)?;
        Ok(Self(path))
    }
    fn path(&self) -> &Path {
        &self.0
    }
    fn write(&self, name: &str, bytes: &[u8]) -> Result<PathBuf> {
        ensure!(bytes.len() <= MAX_PAYLOAD, "harness fixture exceeded limit");
        let path = self.0.join(name);
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(&path)?;
        file.write_all(bytes)?;
        Ok(path)
    }
}
impl Drop for RunDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn read_answer(path: &Path) -> Result<Vec<u8>> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
        .map_err(|error| anyhow!("harness answer is missing: {error}"))?;
    ensure!(
        file.metadata()?.is_file() && file.metadata()?.len() <= MAX_ANSWER,
        "invalid harness answer"
    );
    let mut bytes = Vec::new();
    file.take(MAX_ANSWER + 1).read_to_end(&mut bytes)?;
    ensure!(
        bytes.len() <= MAX_ANSWER as usize,
        "harness answer exceeded limit"
    );
    Ok(bytes)
}

fn parse_reply(value: Value) -> Result<(Value, Action)> {
    let reply: Reply = serde_json::from_value(value.clone()).map_err(|error| {
        SourceFailure::json("invalid harness reply", value.to_string().as_bytes(), error)
    })?;
    ensure!(reply.calls.len() <= 1, "harness returned too many calls");
    let action = if let Some(call) = reply.calls.into_iter().next() {
        ensure!(call.name.len() <= 128, "harness tool name is too long");
        match serde_json::from_str(&call.arguments_json) {
            Ok(arguments) => Action::Tool {
                name: call.name,
                arguments,
            },
            Err(error) => Action::RejectedTool {
                name: call.name,
                source: SourceFailure::json(
                    "invalid harness tool arguments",
                    call.arguments_json.as_bytes(),
                    error,
                ),
            },
        }
    } else {
        Action::Done
    };
    Ok((value, action))
}

pub struct Harness<'a> {
    config: &'a LlmConfig,
    program: String,
    history: Vec<Value>,
    selected_id: Option<Uuid>,
    checked: bool,
}

impl<'a> Harness<'a> {
    pub fn new(config: &'a LlmConfig) -> Result<Self> {
        let program = match config.backend {
            Kind::ClaudeCode => "claude",
            Kind::Codex => "codex",
            Kind::Command => config
                .command
                .as_deref()
                .ok_or_else(|| anyhow!("missing command"))?,
            Kind::Api => bail!("API backend is not a harness"),
        };
        Ok(Self::with_program(config, program))
    }

    fn with_program(config: &'a LlmConfig, program: &str) -> Self {
        Self {
            config,
            program: program.into(),
            history: Vec::new(),
            selected_id: None,
            checked: false,
        }
    }

    async fn check_capabilities(&mut self, work: &RunDir) -> Result<()> {
        if self.checked || self.config.backend == Kind::Command {
            return Ok(());
        }
        let args: Vec<String> = if self.config.backend == Kind::Codex {
            vec!["exec".into(), "--help".into()]
        } else {
            vec!["--help".into()]
        };
        let output = process::run(
            &self.program,
            &args,
            work.path(),
            b"",
            Duration::from_secs(5),
        )
        .await
        .context("harness capability check failed")?;
        let help = String::from_utf8(output.stdout).map_err(|_| anyhow!("invalid harness help"))?;
        let required: &[&str] = if self.config.backend == Kind::Codex {
            &[
                "--ignore-user-config",
                "--ignore-rules",
                "--ephemeral",
                "--sandbox",
                "--output-schema",
                "--output-last-message",
                "--json",
                "--skip-git-repo-check",
                "--model",
                "--config",
            ]
        } else {
            &[
                "--print",
                "--restricted",
                "--tools",
                "--strict-mcp-config",
                "--mcp-config",
                "--disable-slash-commands",
                "--no-session-persistence",
                "--output-format",
                "--json-schema",
                "--permission-mode",
                "--permission-prompts",
                "--settings",
                "--model",
            ]
        };
        ensure!(
            required.iter().all(|flag| help.contains(flag)),
            "installed harness lacks required isolation or output flags"
        );
        self.checked = true;
        Ok(())
    }

    fn arguments(&self, work: &RunDir) -> Result<Vec<String>> {
        let model = self.config.model.clone();
        Ok(match self.config.backend {
            Kind::ClaudeCode => {
                let empty_mcp = work.write("mcp.json", br#"{"mcpServers":{}}"#)?;
                let mut args = vec![
                    "--print",
                    "--model",
                    &model,
                    "--restricted",
                    "--tools",
                    "",
                    "--permission-mode",
                    "dontAsk",
                    "--permission-prompts",
                    "none",
                    "--settings",
                    r#"{"disableAllHooks":true}"#,
                    "--disable-slash-commands",
                    "--mcp-config",
                    empty_mcp
                        .to_str()
                        .ok_or_else(|| anyhow!("invalid temp path"))?,
                    "--strict-mcp-config",
                    "--no-session-persistence",
                    "--output-format",
                    "json",
                    "--json-schema",
                    SCHEMA,
                ]
                .into_iter()
                .map(str::to_owned)
                .collect::<Vec<_>>();
                if let Some(budget) = self.config.max_budget_usd {
                    args.extend(["--max-budget-usd".into(), budget.to_string()]);
                }
                args
            }
            Kind::Codex => {
                let schema = work.write("schema.json", SCHEMA.as_bytes())?;
                let mut args = vec![
                    "exec".into(),
                    // Human output echoes the full prompt to stderr, which can
                    // exceed its diagnostic budget before the model replies.
                    "--json".into(),
                    "--ignore-user-config".into(),
                    "--ignore-rules".into(),
                    "--ephemeral".into(),
                    "--skip-git-repo-check".into(),
                    "--sandbox".into(),
                    "read-only".into(),
                    "--model".into(),
                    model,
                ];
                if let Some(effort) = self.config.reasoning_effort {
                    args.extend([
                        "-c".into(),
                        format!("model_reasoning_effort=\"{}\"", effort.as_str()),
                    ]);
                }
                args.extend([
                    "-c".into(),
                    "approval_policy=\"never\"".into(),
                    "-c".into(),
                    "features.shell_tool=false".into(),
                    "-c".into(),
                    "features.hooks=false".into(),
                    "-c".into(),
                    "features.apps=false".into(),
                    "-c".into(),
                    "features.plugins=false".into(),
                    "-c".into(),
                    "features.skill_search=false".into(),
                    "-c".into(),
                    "web_search=\"disabled\"".into(),
                    "-c".into(),
                    "mcp_servers={}".into(),
                    "-c".into(),
                    "project_doc_max_bytes=0".into(),
                    "--output-schema".into(),
                    schema.to_string_lossy().into_owned(),
                    "--output-last-message".into(),
                    work.path()
                        .join("answer.json")
                        .to_string_lossy()
                        .into_owned(),
                    "-".into(),
                ]);
                args
            }
            Kind::Command => self.config.args.clone(),
            Kind::Api => bail!("API backend is not a harness"),
        })
    }

    async fn step(
        &mut self,
        selected: &ExperienceState,
        last: Option<&Value>,
        tools: &[Value],
    ) -> Result<Action> {
        if self.selected_id != Some(selected.experience.id) {
            self.selected_id = Some(selected.experience.id);
            self.history.clear();
        }
        if let Some(result) = last {
            self.history
                .push(json!({"tool_results":[{"result":result}]}));
        }
        let work = RunDir::new()?;
        self.check_capabilities(&work).await?;
        let payload = json!({
            "instructions":format!("Review only this pinned experience. Use the supplied tools through calls; do not execute tools yourself. {} The host enforces project {}, experience {}, source revision {}, and review revision {}. Return an empty calls array only when you have finished.",
                super::review_guidance(), selected.experience.project, selected.experience.id, selected.revision, selected.review_revision),
            "experience":selected,
            "tools":tools,
            "history":self.history,
            "response_schema":serde_json::from_str::<Value>(SCHEMA)?,
            "protocol":"Return one JSON object matching response_schema. Request at most one tool in calls. arguments_json is a JSON object encoded as a string. Never execute tools directly."
        });
        let bytes = serde_json::to_vec(&payload)?;
        ensure!(bytes.len() <= MAX_PAYLOAD, "harness context exceeded limit");
        let args = self.arguments(&work)?;
        let output = process::run(
            &self.program,
            &args,
            work.path(),
            &bytes,
            Duration::from_secs(self.config.timeout_seconds),
        )
        .await?;
        let reply_value = match self.config.backend {
            Kind::ClaudeCode => {
                let wrapper: Value = serde_json::from_slice(&output.stdout).map_err(|error| {
                    SourceFailure::json("invalid Claude result", &output.stdout, error)
                })?;
                ensure!(wrapper["is_error"] == false, "Claude reported failure");
                if !wrapper["structured_output"].is_null() {
                    wrapper["structured_output"].clone()
                } else {
                    let result = wrapper["result"]
                        .as_str()
                        .ok_or_else(|| anyhow!("Claude result missing"))?;
                    serde_json::from_str(result).map_err(|error| {
                        SourceFailure::json(
                            "invalid Claude structured result",
                            result.as_bytes(),
                            error,
                        )
                    })?
                }
            }
            Kind::Codex => {
                let answer = read_answer(&work.path().join("answer.json"))?;
                serde_json::from_slice(&answer).map_err(|error| {
                    SourceFailure::json("invalid Codex structured result", &answer, error)
                })?
            }
            Kind::Command => serde_json::from_slice(&output.stdout).map_err(|error| {
                SourceFailure::json("invalid command result", &output.stdout, error)
            })?,
            Kind::Api => bail!("API backend is not a harness"),
        };
        let (reply, action) = parse_reply(reply_value)?;
        self.history.push(json!({"assistant":reply}));
        Ok(action)
    }
}

impl Backend for Harness<'_> {
    fn next<'a>(
        &'a mut self,
        selected: &'a ExperienceState,
        last: Option<&'a Value>,
        tools: &'a [Value],
    ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
        Box::pin(self.step(selected, last, tools))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::judge::state::Report;
    use std::os::unix::fs::PermissionsExt;

    // An offline executable that reproduces Codex's human prompt echo and the
    // distinct Codex/Claude answer transports. It never starts an actual model.
    const FIXTURE: &str = r#"#!/usr/bin/env bash
set -eu
kind=command
json=false
answer=
model=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --help)
      printf '%s\n' '--ignore-user-config --ignore-rules --ephemeral --sandbox --output-schema --output-last-message --json --skip-git-repo-check --model --config --print --restricted --tools --strict-mcp-config --mcp-config --disable-slash-commands --no-session-persistence --output-format --json-schema --permission-mode --permission-prompts --settings'
      exit 0 ;;
    exec) kind=codex ;;
    --print) kind=claude ;;
    --json) json=true ;;
    --output-format) shift; [ "$1" = json ]; json=true ;;
    --output-last-message) shift; answer=$1 ;;
    --model) shift; model=$1 ;;
  esac
  shift
done
cat > "${0}.payload"
case "$model" in
  overflow-stdout) head -c 8388609 /dev/zero; exit 0 ;;
  overflow-stderr) head -c 65537 /dev/zero >&2; exit 0 ;;
esac
if [ "$(wc -c < "${0}.payload")" -gt 65536 ]; then
  reply='{"calls":[]}'
else
  reply='{"calls":[{"name":"experience_history","arguments_json":"{}"}]}'
fi
case "$kind" in
  codex)
    if [ "$json" = false ]; then cat "${0}.payload" >&2; fi
    printf '%s\n' '{"type":"thread.started"}' '{"type":"turn.completed"}'
    printf '%s' "$reply" > "$answer" ;;
  claude)
    [ "$json" = true ]
    printf '{"is_error":false,"structured_output":%s}\n' "$reply" ;;
  command) printf '%s\n' "$reply" ;;
esac
"#;

    fn fixture(work: &RunDir) -> PathBuf {
        let program = work.write("harness-fixture", FIXTURE.as_bytes()).unwrap();
        fs::set_permissions(&program, fs::Permissions::from_mode(0o700)).unwrap();
        program
    }

    fn config(backend: &str, model: &str) -> LlmConfig {
        toml::from_str(&format!(
            "backend = {backend:?}\nmodel = {model:?}\ntimeout_seconds = 5\n"
        ))
        .unwrap()
    }

    fn selected() -> ExperienceState {
        serde_json::from_value(json!({
            "experience": {
                "id": Uuid::new_v4(), "project": "adapter-regression",
                "context": "large history", "action": "review",
                "outcome": "unknown", "source": "agent_report", "evidence": [],
                "pattern_id": null
            },
            "revision": 1, "review_revision": 0, "reviewed_revision": 0
        }))
        .unwrap()
    }

    #[tokio::test]
    async fn adapters_deliver_large_history_without_prompt_echo_overflow() {
        for backend in ["codex", "claude-code", "command"] {
            let work = RunDir::new().unwrap();
            let program = fixture(&work);
            let config = config(backend, "offline-fixture");
            let mut harness = Harness::with_program(&config, program.to_str().unwrap());
            let selected = selected();
            let tools = vec![json!({"name": "experience_history"})];
            let action = harness.step(&selected, None, &tools).await.unwrap();
            assert!(matches!(action, Action::Tool { name, .. } if name == "experience_history"));

            let history = json!({"history": "history entry; ".repeat(5_000)});
            assert!(serde_json::to_vec(&history).unwrap().len() > 64 * 1024);
            let action = harness
                .step(&selected, Some(&history), &tools)
                .await
                .unwrap();
            assert!(matches!(action, Action::Done));
            let delivered: Value = serde_json::from_slice(
                &fs::read(work.path().join("harness-fixture.payload")).unwrap(),
            )
            .unwrap();
            assert_eq!(
                delivered["history"][1]["tool_results"][0]["result"],
                history
            );
            assert_eq!(
                delivered["experience"]["experience"]["id"],
                selected.experience.id.to_string()
            );
            assert_eq!(delivered["tools"], json!(tools));
        }
    }

    #[tokio::test]
    async fn codex_requires_machine_output_before_sending_the_prompt() {
        let work = RunDir::new().unwrap();
        let script = FIXTURE
            .replace("--output-last-message --json", "--output-last-message")
            .replace("--json-schema", "--schema");
        let program = work.write("old-codex", script.as_bytes()).unwrap();
        fs::set_permissions(&program, fs::Permissions::from_mode(0o700)).unwrap();
        let config = config("codex", "offline-fixture");
        let mut harness = Harness::with_program(&config, program.to_str().unwrap());
        let error = match harness.step(&selected(), None, &[]).await {
            Err(error) => error,
            Ok(_) => panic!("accepted Codex without machine output"),
        };
        assert!(error
            .to_string()
            .contains("lacks required isolation or output flags"));
        assert!(!work.path().join("old-codex.payload").exists());
    }

    #[tokio::test]
    async fn capability_checks_preserve_overflow_evidence() {
        for backend in ["codex", "claude-code"] {
            let work = RunDir::new().unwrap();
            let program = work
                .write(
                    "noisy-help",
                    b"#!/usr/bin/env bash\nhead -c 65537 /dev/zero >&2\n",
                )
                .unwrap();
            fs::set_permissions(&program, fs::Permissions::from_mode(0o700)).unwrap();
            let config = config(backend, "offline-fixture");
            let mut harness = Harness::with_program(&config, program.to_str().unwrap());
            let error = match harness.step(&selected(), None, &[]).await {
                Err(error) => error,
                Ok(_) => panic!("accepted excessive capability output"),
            };
            assert_eq!(error.to_string(), "harness capability check failed");
            let source = error.downcast_ref::<SourceFailure>().unwrap();
            assert_eq!(source.stage, "harness stderr output");
            assert_eq!(source.total_bytes, 65537);
        }
    }

    #[tokio::test]
    async fn adapters_preserve_stream_overflow_diagnostics() {
        for backend in ["codex", "claude-code", "command"] {
            for (stream, limit) in [("stdout", 8 * 1024 * 1024), ("stderr", 64 * 1024)] {
                let work = RunDir::new().unwrap();
                let program = fixture(&work);
                let mut config = config(backend, &format!("overflow-{stream}"));
                if backend == "command" {
                    config.args = vec!["--model".into(), config.model.clone()];
                }
                let mut harness = Harness::with_program(&config, program.to_str().unwrap());
                let error = match harness.step(&selected(), None, &[]).await {
                    Err(error) => error,
                    Ok(_) => panic!("{backend} accepted excessive {stream}"),
                };
                let mut report = Report::new("blocked", 1, 0, 0, 1, 0);
                report.capture_source(&error);
                let source = report.failure_source.unwrap();
                assert_eq!(source.stage, format!("harness {stream} output"));
                assert!(source.detail.contains(&format!("limit of {limit} bytes")));
                assert_eq!(source.total_bytes, limit + 1);
                assert_eq!(source.excerpt.len(), 32 * 1024);
                assert!(!error.to_string().contains('\0'));
            }
        }
    }

    #[test]
    fn malformed_arguments_are_a_recoverable_tool_request() {
        let (_, action) = parse_reply(json!({
            "calls": [{"name": "review_experience", "arguments_json": "{\"review\": }"}]
        }))
        .unwrap();
        let Action::RejectedTool { name, source } = action else {
            panic!("expected rejected tool call")
        };
        assert_eq!(name, "review_experience");
        assert_eq!(source.stage, "invalid harness tool arguments");
        assert!(source.detail.contains("line 1 column"));
        assert_eq!(source.excerpt, "{\"review\": }");
        let mut report = Report::new("blocked", 1, 0, 0, 1, 0);
        report.failure_source = Some(source);
        let serialized = serde_json::to_value(&report).unwrap();
        assert_eq!(serialized["failure_source"]["excerpt"], "{\"review\": }");
    }
}

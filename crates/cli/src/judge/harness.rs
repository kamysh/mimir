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
use std::collections::VecDeque;
use std::fs::{self, OpenOptions};
use std::future::Future;
use std::io::{Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::pin::Pin;
use uuid::Uuid;

const SCHEMA: &str = r#"{"type":"object","additionalProperties":false,"properties":{"calls":{"type":"array","items":{"type":"object","additionalProperties":false,"properties":{"name":{"type":"string"},"arguments_json":{"type":"string"}},"required":["name","arguments_json"]}}},"required":["calls"]}"#;

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

pub(super) struct RunDir(PathBuf);
impl RunDir {
    fn new() -> Result<Self> {
        Self::new_in(Path::new("/var/tmp/mimir"))
    }
    pub(super) fn new_in(base: &Path) -> Result<Self> {
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
    pub(super) fn path(&self) -> &Path {
        &self.0
    }
    pub(super) fn write(&self, name: &str, bytes: &[u8]) -> Result<PathBuf> {
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
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
        .map_err(|error| anyhow!("harness answer is missing: {error}"))?;
    ensure!(file.metadata()?.is_file(), "invalid harness answer");
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    Ok(bytes)
}

fn parse_reply(value: Value) -> Result<(mimir_json::Document, VecDeque<Action>)> {
    let value = mimir_json::Document::new(value);
    let reply: Reply = mimir_json::decode_ref(&value).map_err(|error| {
        SourceFailure::json("invalid harness reply", value.to_string().as_bytes(), error)
    })?;
    let actions = reply
        .calls
        .into_iter()
        .map(|call| match mimir_json::from_str(&call.arguments_json) {
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
        })
        .collect();
    Ok((value, actions))
}

pub struct Harness<'a> {
    config: &'a LlmConfig,
    program: String,
    history: Vec<mimir_json::Document>,
    selected_id: Option<Uuid>,
    checked: bool,
    pending: VecDeque<Action>,
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
            pending: VecDeque::new(),
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
        let output = process::run(&self.program, &args, work.path(), b"")
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
                let args = vec![
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
                args
            }
            Kind::Codex => {
                let schema = work.write("schema.json", SCHEMA.as_bytes())?;
                let mut args = vec![
                    "exec".into(),
                    // Machine output avoids duplicating the complete prompt in diagnostics.
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
            self.pending.clear();
        }
        if let Some(result) = last {
            self.history
                .push(mimir_json::Document::new(json!({"tool_results":[{"result":mimir_json::Document::new(mimir_json::clone_value(result))}]})));
        }
        if let Some(action) = self.pending.pop_front() {
            return Ok(action);
        }
        let work = RunDir::new()?;
        self.check_capabilities(&work).await?;
        let payload = json!({
            "instructions":format!("Review only this pinned experience. Use the supplied tools through calls; do not execute tools yourself. {} The host enforces project {}, experience {}, source revision {}, and review revision {}. Return an empty calls array only when you have finished.",
                super::review_guidance(selected), selected.experience.project, selected.experience.id, selected.revision, selected.review_revision),
            "experience":selected,
            "tools":tools,
            "history":self.history,
            "response_schema":mimir_json::from_str::<Value>(SCHEMA)?,
            "protocol":"Return one JSON object matching response_schema. Calls are executed in array order, and each receives a result. arguments_json is a JSON object encoded as a string. Never execute tools directly."
        });
        let bytes = mimir_json::to_vec(&payload)?;
        let args = self.arguments(&work)?;
        let output = process::run(&self.program, &args, work.path(), &bytes).await?;
        let reply_value = match self.config.backend {
            Kind::ClaudeCode => {
                let wrapper: mimir_json::Document = mimir_json::from_slice(&output.stdout)
                    .map_err(|error| {
                        SourceFailure::json("invalid Claude result", &output.stdout, error)
                    })?;
                ensure!(wrapper["is_error"] == false, "Claude reported failure");
                if !wrapper["structured_output"].is_null() {
                    mimir_json::clone_value(&wrapper["structured_output"])
                } else {
                    let result = wrapper["result"]
                        .as_str()
                        .ok_or_else(|| anyhow!("Claude result missing"))?;
                    mimir_json::from_str(result).map_err(|error| {
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
                mimir_json::from_slice(&answer).map_err(|error| {
                    SourceFailure::json("invalid Codex structured result", &answer, error)
                })?
            }
            Kind::Command => mimir_json::from_slice(&output.stdout).map_err(|error| {
                SourceFailure::json("invalid command result", &output.stdout, error)
            })?,
            Kind::Api => bail!("API backend is not a harness"),
        };
        let (reply, calls) = parse_reply(reply_value)?;
        self.history
            .push(mimir_json::Document::new(json!({"assistant":reply})));
        self.pending = calls;
        Ok(self.pending.pop_front().unwrap_or(Action::Done))
    }
}

impl Backend for Harness<'_> {
    fn will_call_model(&self, selected: &ExperienceState) -> bool {
        self.selected_id != Some(selected.experience.id) || self.pending.is_empty()
    }

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

    #[test]
    fn deep_json_arguments_survive_queueing_rejection_and_dropped_work() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let nested = format!("{}null{}", "[".repeat(10000), "]".repeat(10000));
                let arguments = format!(r#"{{"review":{nested}}}"#);
                let (_, actions) = parse_reply(
                    json!({"calls":[{"name":"review_experience","arguments_json":arguments}]}),
                )
                .unwrap();
                drop(actions);
                let invalid =
                    mimir_json::parse(&format!(r#"{{"calls":[],"unexpected":{nested}}}"#)).unwrap();
                assert!(parse_reply(invalid.into_value()).is_err());
            })
            .unwrap()
            .join()
            .unwrap();
    }
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
  overflow-stderr) head -c 65537 /dev/zero >&2 ;;
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
        toml::from_str(&format!("backend = {backend:?}\nmodel = {model:?}\n")).unwrap()
    }

    fn selected() -> ExperienceState {
        mimir_json::from_value(json!({
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
            assert!(mimir_json::to_vec(&history).unwrap().len() > 64 * 1024);
            let action = harness
                .step(&selected, Some(&history), &tools)
                .await
                .unwrap();
            assert!(matches!(action, Action::Done));
            let delivered: Value = mimir_json::from_slice(
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
    async fn diagnostic_volume_does_not_fail_valid_work() {
        for backend in ["codex", "claude-code", "command"] {
            let work = RunDir::new().unwrap();
            let program = fixture(&work);
            let mut config = config(backend, "overflow-stderr");
            if backend == "command" {
                config.args = vec!["--model".into(), config.model.clone()];
            }
            let mut harness = Harness::with_program(&config, program.to_str().unwrap());
            assert!(matches!(
                harness.step(&selected(), None, &[]).await.unwrap(),
                Action::Tool { .. }
            ));
        }
    }

    #[test]
    fn complete_call_array_is_queued_in_order() {
        let calls: Vec<_> = (0..65)
            .map(|n| json!({"name":"get_experience","arguments_json":json!({"n":n}).to_string()}))
            .collect();
        let (_, actions) = parse_reply(json!({"calls":calls})).unwrap();
        assert_eq!(actions.len(), 65);
        for (n, action) in actions.into_iter().enumerate() {
            let Action::Tool { arguments, .. } = action else {
                panic!("missing queued call")
            };
            assert_eq!(arguments["n"], n);
        }
    }

    #[test]
    fn malformed_arguments_are_a_recoverable_tool_request() {
        let (_, mut actions) = parse_reply(json!({
            "calls": [{"name": "review_experience", "arguments_json": "{\"review\": }"}]
        }))
        .unwrap();
        let Action::RejectedTool { name, source } = actions.pop_front().unwrap() else {
            panic!("expected rejected tool call")
        };
        assert_eq!(name, "review_experience");
        assert_eq!(source.stage, "invalid harness tool arguments");
        assert!(source.detail.contains("line 1 column"));
        assert_eq!(source.excerpt, "{\"review\": }");
        let mut report = Report::new("blocked", 1, 0, 0, 1, 0);
        report.failure_source = Some(source);
        let serialized = mimir_json::to_value(&report).unwrap();
        assert_eq!(serialized["failure_source"]["excerpt"], "{\"review\": }");
    }
}

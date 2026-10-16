//! Isolated Step-11 judge comparison. Live calls require --live and two explicit configs.
use anyhow::{anyhow, bail, ensure, Context, Result};
use clap::Parser;
use serde_json::{json, Value};
use std::fs::{self, DirBuilder, OpenOptions};
use std::io::Write;
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
use uuid::Uuid;

#[derive(Parser)]
struct Args {
    #[arg(long)]
    arm_a: PathBuf,
    #[arg(long)]
    arm_b: PathBuf,
    #[arg(long)]
    mimir: PathBuf,
    #[arg(long)]
    mcp: PathBuf,
    /// Without this flag, validate selectors and configuration without database or model calls.
    #[arg(long)]
    live: bool,
}

struct Arm {
    source: PathBuf,
    document: toml::Value,
    model: String,
    effort: Option<String>,
    timeout_seconds: u64,
}

struct RunDir(PathBuf);
impl RunDir {
    fn new() -> Result<Self> {
        let base = Path::new("/var/tmp/mimir");
        ensure!(
            base.is_dir() && !fs::symlink_metadata(base)?.file_type().is_symlink(),
            "unsafe temporary root"
        );
        let path = base.join(format!("learning-compare-{}", Uuid::new_v4()));
        DirBuilder::new().mode(0o700).create(&path)?;
        Ok(Self(path))
    }

    fn write(&self, name: &str, data: &[u8]) -> Result<PathBuf> {
        let path = self.0.join(name);
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)?;
        file.write_all(data)?;
        Ok(path)
    }
}

fn load_arm(path: &Path, mimir: &Path) -> Result<Arm> {
    let config_home = std::env::var_os("XDG_CONFIG_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".config")));
    let default_config = config_home.map(|home| home.join("mimir/config.toml"));
    ensure!(
        path.is_absolute()
            && default_config.as_deref() != Some(path)
            && std::env::var_os("MIMIR_CONFIG").as_deref() != Some(path.as_os_str()),
        "use an explicit comparison config, not the installed Mimir config"
    );
    let checked = Command::new(mimir)
        .args(["judge", "check-config", "--config"])
        .arg(path)
        .output()
        .context("run judge config validation")?;
    ensure!(
        checked.status.success(),
        "comparison config is invalid: {}",
        path.display()
    );
    let raw = fs::read_to_string(path).context("read comparison config")?;
    let document: toml::Value = raw
        .parse()
        .map_err(|_| anyhow!("invalid comparison TOML"))?;
    let llm = document
        .get("llm")
        .and_then(toml::Value::as_table)
        .ok_or_else(|| anyhow!("missing llm section"))?;
    ensure!(
        llm.get("backend").and_then(toml::Value::as_str) == Some("codex"),
        "comparison currently requires the Codex backend"
    );
    let model = llm
        .get("model")
        .and_then(toml::Value::as_str)
        .ok_or_else(|| anyhow!("missing llm.model"))?
        .to_owned();
    let effort = llm
        .get("reasoning_effort")
        .and_then(toml::Value::as_str)
        .map(str::to_owned);
    let timeout_seconds = llm
        .get("timeout_seconds")
        .and_then(toml::Value::as_integer)
        .unwrap_or(300) as u64;
    ensure!(
        llm.get("max_calls")
            .and_then(toml::Value::as_integer)
            .unwrap_or(20)
            >= 3,
        "comparison requires llm.max_calls of at least 3"
    );
    let db = document
        .get("database")
        .and_then(toml::Value::as_table)
        .ok_or_else(|| anyhow!("missing database section"))?;
    ensure!(
        db.get("dbname")
            .and_then(toml::Value::as_str)
            .is_some_and(|name| name.starts_with("mimir_learning_test")),
        "comparison requires a disposable mimir_learning_test database"
    );
    ensure!(
        db.get("host")
            .and_then(toml::Value::as_str)
            .is_some_and(|host| host == "127.0.0.1" || host == "localhost"),
        "comparison requires a loopback database"
    );
    Ok(Arm {
        source: path.to_owned(),
        document,
        model,
        effort,
        timeout_seconds,
    })
}

fn variant(
    arm: &Arm,
    run: &RunDir,
    name: &str,
    project: &str,
    mcp: &Path,
    max_calls: i64,
) -> Result<PathBuf> {
    let mut config = arm.document.clone();
    let judge = config
        .get_mut("judge")
        .and_then(toml::Value::as_table_mut)
        .ok_or_else(|| anyhow!("missing judge section"))?;
    judge.insert("project".into(), toml::Value::String(project.into()));
    judge.insert("batch_size".into(), toml::Value::Integer(1));
    judge.insert(
        "mcp_command".into(),
        toml::Value::String(mcp.to_string_lossy().into_owned()),
    );
    judge.insert("mcp_args".into(), toml::Value::Array(vec![]));
    let llm = config
        .get_mut("llm")
        .and_then(toml::Value::as_table_mut)
        .ok_or_else(|| anyhow!("missing llm section"))?;
    let configured = llm
        .get("max_calls")
        .and_then(toml::Value::as_integer)
        .unwrap_or(20);
    llm.insert(
        "max_calls".into(),
        toml::Value::Integer(configured.min(max_calls)),
    );
    let root = config
        .as_table_mut()
        .ok_or_else(|| anyhow!("invalid config root"))?;
    root.remove("email");
    root.insert(
        "email".into(),
        toml::Value::Table(
            [("enabled".into(), toml::Value::Boolean(false))]
                .into_iter()
                .collect(),
        ),
    );
    run.write(name, toml::to_string(&config)?.as_bytes())
}

fn mcp_call(mcp: &Path, config: &Path, name: &str, args: Value) -> Result<Value> {
    let mut child = Command::new(mcp)
        .env("MIMIR_CONFIG", config)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .context("start isolated MCP")?;
    let request = json!({"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":name,"arguments":args}});
    writeln!(
        child
            .stdin
            .take()
            .ok_or_else(|| anyhow!("MCP stdin missing"))?,
        "{request}"
    )?;
    let output = child.wait_with_output().context("wait for MCP")?;
    ensure!(output.status.success(), "MCP process failed");
    let reply: Value =
        serde_json::from_slice(&output.stdout).map_err(|_| anyhow!("invalid MCP reply"))?;
    ensure!(
        reply.get("error").is_none() && reply["result"]["isError"] != true,
        "MCP tool refused {name}"
    );
    let text = reply["result"]["content"][0]["text"]
        .as_str()
        .ok_or_else(|| anyhow!("MCP result missing"))?;
    serde_json::from_str(text).map_err(|_| anyhow!("invalid MCP tool result"))
}

fn judge(mimir: &Path, config: &Path, state: &Path) -> Result<Value> {
    let output = Command::new(mimir)
        .args(["judge", "run", "--config"])
        .arg(config)
        .arg("--state-dir")
        .arg(state)
        .output()
        .context("run judge")?;
    let mut report: Value =
        serde_json::from_slice(&output.stdout).map_err(|_| anyhow!("invalid judge report"))?;
    report["exit_code"] = json!(output.status.code());
    Ok(report)
}

fn actor(arm: &Arm, run: &RunDir, name: &str, context: &Value) -> Result<Value> {
    const SCHEMA: &str = r#"{"type":"object","additionalProperties":false,"properties":{"related_action":{"type":"string"},"unrelated_action":{"type":"string"},"used_belief_ids":{"type":"array","items":{"type":"string"}}},"required":["related_action","unrelated_action","used_belief_ids"]}"#;
    let schema = run.write(&format!("{name}-schema.json"), SCHEMA.as_bytes())?;
    let answer = run.0.join(format!("{name}-answer.json"));
    let mut command = Command::new("codex");
    command.current_dir(&run.0).args([
        "exec",
        "--ignore-user-config",
        "--ignore-rules",
        "--ephemeral",
        "--skip-git-repo-check",
        "--sandbox",
        "read-only",
        "--model",
        &arm.model,
    ]);
    if let Some(effort) = &arm.effort {
        command.args(["-c", &format!("model_reasoning_effort=\"{effort}\"")]);
    }
    command
        .args([
            "-c",
            "approval_policy=\"never\"",
            "-c",
            "features.shell_tool=false",
            "-c",
            "features.hooks=false",
            "-c",
            "features.apps=false",
            "-c",
            "features.plugins=false",
            "-c",
            "features.skill_search=false",
            "-c",
            "web_search=\"disabled\"",
            "-c",
            "mcp_servers={}",
            "-c",
            "project_doc_max_bytes=0",
            "--output-schema",
        ])
        .arg(schema)
        .arg("--output-last-message")
        .arg(&answer)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    let mut child = command.spawn().context("start later-action actor")?;
    let prompt = format!("You are a later agent in a fresh session. You have only the retrieved Mimir context below. For each situation, state the next concrete action you would actually choose, using the context only if it is relevant. Situation one: keyboard layout indicator stays stale after a configuration change. Situation two: a disk quota alert appears during a build. Return only schema JSON. Retrieved context: {context}");
    child
        .stdin
        .take()
        .ok_or_else(|| anyhow!("actor stdin missing"))?
        .write_all(prompt.as_bytes())?;
    let deadline = Instant::now() + Duration::from_secs(arm.timeout_seconds.min(300));
    loop {
        if let Some(status) = child.try_wait()? {
            ensure!(status.success(), "later-action actor failed");
            break;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            bail!("later-action actor timed out");
        }
        std::thread::sleep(Duration::from_millis(100));
    }
    serde_json::from_slice(&fs::read(answer)?).map_err(|_| anyhow!("invalid later-action answer"))
}

#[derive(Clone, Copy)]
enum Scenario {
    Success,
    Failure,
    Unknown,
    Corrected,
    Repeated,
    Confounded,
}
impl Scenario {
    fn all() -> [Self; 6] {
        [
            Self::Success,
            Self::Failure,
            Self::Unknown,
            Self::Corrected,
            Self::Repeated,
            Self::Confounded,
        ]
    }
    fn name(self) -> &'static str {
        match self {
            Self::Success => "success",
            Self::Failure => "failure",
            Self::Unknown => "unknown",
            Self::Corrected => "corrected",
            Self::Repeated => "repeated",
            Self::Confounded => "confounded",
        }
    }
    fn initial(self) -> (&'static str, &'static str, &'static str) {
        match self {
            Self::Success => ("success", "tool_result", "Process ID changed; indicator displayed the configured layout"),
            Self::Failure => ("failure", "tool_result", "Process restarted but keyboard layout and indicator stayed stale"),
            Self::Unknown => ("unknown", "agent_report", "Agent guessed the layout switch worked; no independent check"),
            Self::Corrected => ("success", "agent_report", "Agent initially reported that the switch worked"),
            Self::Repeated => ("success", "tool_result", "Process ID changed; indicator displayed the configured layout"),
            Self::Confounded => ("success", "tool_result", "Layout appeared after a process restart and an RDP reconnect happened at the same time; neither cause was isolated"),
        }
    }
}

fn experience(id: Uuid, project: &str, scenario: Scenario, corrected: bool) -> Value {
    let (outcome, source, evidence) = if corrected {
        (
            "failure",
            "user_feedback",
            "User corrected the report: the keyboard did not switch after reconnect",
        )
    } else {
        scenario.initial()
    };
    json!({"id":id.to_string(),"project":project,"context":format!("{}: stale keyboard layout indicator over RDP", scenario.name()),
        "action":"restart keyboard layout process after checking loaded configuration",
        "outcome":outcome,"source":source,"evidence":[evidence],"belief_ids":[]})
}

fn belief_masses(context: &Value) -> Vec<Value> {
    let mut masses: Vec<_> = context["beliefs"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|belief| json!({"kind":"belief","id":belief["id"],"alpha":belief["alpha"],"beta":belief["beta"]}))
        .collect();
    masses.extend(context["patterns"].as_array().into_iter().flatten().map(|pattern| {
        json!({"kind":"pattern","id":pattern["pattern"]["id"],"successes":pattern["successes"],"failures":pattern["failures"],"unknown":pattern["unknown"]})
    }));
    masses.sort_by(|a, b| a["id"].as_str().cmp(&b["id"].as_str()));
    masses
}

fn run_case(
    arm: &Arm,
    arm_name: &str,
    scenario: Scenario,
    id: Uuid,
    run: &RunDir,
    mimir: &Path,
    mcp: &Path,
) -> Result<Value> {
    let project = format!("step11-{}-{arm_name}-{}", Uuid::new_v4(), scenario.name());
    let base = format!("{arm_name}-{}", scenario.name());
    let config = variant(arm, run, &format!("{base}.toml"), &project, mcp, 2)?;
    let state = run.0.join(format!("{base}-state"));
    let work = (|| -> Result<Value> {
        let initial = experience(id, &project, scenario, false);
        let recorded = mcp_call(
            mcp,
            &config,
            "record_experience",
            json!({"experience":initial,"expected_revision":0}),
        )?;
        ensure!(
            recorded["revision"] == 1,
            "initial experience revision mismatch"
        );
        let first = judge(mimir, &config, &state)?;
        let first_history = mcp_call(
            mcp,
            &config,
            "experience_history",
            json!({"id":id.to_string()}),
        )?;
        let first_reviews = first_history["reviews"].as_array().map_or(0, Vec::len);
        let first_context = mcp_call(
            mcp,
            &config,
            "query_learning_context",
            json!({"context":"stale keyboard layout indicator over RDP","project":project,"limit":10}),
        )?;
        let mut second = Value::Null;
        if matches!(scenario, Scenario::Corrected) {
            let changed = experience(id, &project, scenario, true);
            let updated = mcp_call(
                mcp,
                &config,
                "record_experience",
                json!({"experience":changed,"expected_revision":1}),
            )?;
            ensure!(updated["revision"] == 2, "correction revision mismatch");
            let correction = variant(
                arm,
                run,
                &format!("{base}-correction.toml"),
                &project,
                mcp,
                2,
            )?;
            second = judge(mimir, &correction, &state)?;
        }
        if matches!(scenario, Scenario::Repeated) {
            let retried = mcp_call(
                mcp,
                &config,
                "record_experience",
                json!({"experience":initial,"expected_revision":0}),
            )?;
            ensure!(
                retried["revision"] == 1,
                "exact retry changed source revision"
            );
            // The exact source retry is checked from persisted history below.
            // A second judge run cannot add evidence for the same incident.
        }
        let history = mcp_call(
            mcp,
            &config,
            "experience_history",
            json!({"id":id.to_string()}),
        )?;
        let context = mcp_call(
            mcp,
            &config,
            "query_learning_context",
            json!({"context":"stale keyboard layout indicator over RDP","project":project,"limit":10}),
        )?;
        let later = actor(arm, run, &base, &context)?;
        let reviews = history["reviews"].as_array().map_or(0, Vec::len);
        let safety = json!({"acknowledgement_has_review": first["status"] != "complete" || first_reviews > 0,
            "second_acknowledgement_has_review": second["status"] != "complete" || reviews > first_reviews || matches!(scenario, Scenario::Repeated),
            "retry_has_one_review": !matches!(scenario, Scenario::Repeated) || reviews == 1,
            "retry_keeps_belief_mass": !matches!(scenario, Scenario::Repeated) || belief_masses(&first_context) == belief_masses(&context),
            "correction_reached_revision_two": !matches!(scenario, Scenario::Corrected) || history["experiences"].as_array().and_then(|xs| xs.last()).is_some_and(|last| last["revision"] == 2)});
        Ok(
            json!({"scenario":scenario.name(),"project":project,"initial_report":first,"second_report":second,
            "first_history":first_history,"first_retrieval":first_context,
            "history":history,"retrieval":context,"later_action":later,"safety":safety}),
        )
    })();
    let cleanup = mcp_call(mcp, &config, "delete_project", json!({"project":project}));
    match (work, cleanup) {
        (Ok(value), Ok(_)) => Ok(value),
        (Err(error), Ok(_)) => Err(error),
        (Ok(_), Err(error)) => Err(error.context(format!("cleanup failed for {project}"))),
        (Err(error), Err(clean_error)) => {
            Err(error.context(format!("cleanup also failed for {project}: {clean_error}")))
        }
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    ensure!(
        args.mimir.is_absolute() && args.mcp.is_absolute(),
        "binary paths must be absolute"
    );
    let a = load_arm(&args.arm_a, &args.mimir)?;
    let b = load_arm(&args.arm_b, &args.mimir)?;
    ensure!(a.source != b.source, "use two distinct comparison configs");
    ensure!(
        a.model != b.model || a.effort != b.effort,
        "comparison arms must select different models or efforts"
    );
    ensure!(
        a.document.get("database") == b.document.get("database")
            && a.document.get("embeddings") == b.document.get("embeddings")
            && a.timeout_seconds == b.timeout_seconds,
        "comparison arms must use the same database, embeddings, and timeout"
    );
    let selectors = json!({"arm_a":{"model":a.model,"reasoning_effort":a.effort},
        "arm_b":{"model":b.model,"reasoning_effort":b.effort}});
    if !args.live {
        println!(
            "{}",
            json!({"status":"preflight","selectors":selectors,
            "next":"pass --live only after approving the model pair and account-use bound"})
        );
        return Ok(());
    }
    let run = RunDir::new()?;
    let ids: Vec<_> = Scenario::all().iter().map(|_| Uuid::new_v4()).collect();
    let mut results = Vec::new();
    for (arm_name, arm) in [("a", &a), ("b", &b)] {
        for (scenario, id) in Scenario::all().into_iter().zip(ids.iter().copied()) {
            let result = run_case(arm, arm_name, scenario, id, &run, &args.mimir, &args.mcp)
                .with_context(|| format!("comparison artifacts: {}", run.0.display()))?;
            run.write(
                &format!("{arm_name}-{}.json", scenario.name()),
                serde_json::to_string_pretty(&result)?.as_bytes(),
            )?;
            results.push(json!({"arm":arm_name,"result":result}));
        }
    }
    let report = json!({"status":"complete","selectors":selectors,"cases":results,
        "limits":"At most two model-bearing judge subprocesses for initial review, two more for correction, and one later-action subprocess per scenario. Exact retry is checked through MCP history. Codex help checks are additional. Judge max_calls also bounds tool calls. Provider-internal requests and charges are not metered."});
    let file = run.write(
        "results.json",
        serde_json::to_string_pretty(&report)?.as_bytes(),
    )?;
    println!("{}", json!({"status":"complete","results":file,"cases":12}));
    Ok(())
}

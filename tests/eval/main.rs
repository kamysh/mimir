use anyhow::{anyhow, bail, Context, Result};
use clap::{Parser, Subcommand};
use regex::Regex;
use serde_json::{json, Map, Value};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs;
use std::io::{self, BufRead, Read, Write};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

#[derive(Parser)]
#[command(
    name = "mimir-eval",
    version,
    about = "Offline and live Mimir evaluation harness"
)]
struct Cli {
    #[command(subcommand)]
    command: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Validate local tools, config, and binary/database migration alignment.
    Preflight {
        #[arg(long)]
        skip_version_check: bool,
    },
    /// Snapshot belief IDs before or after a run.
    Snapshot { when: String },
    /// Seed task beliefs into isolated eval projects.
    Seed {
        #[arg(long)]
        with_distractors: bool,
    },
    /// Remove seeded eval projects.
    Cleanup,
    /// Check bubblewrap isolation without launching a model.
    Gate,
    /// Run the positive isolation task twice; this spends model budget.
    IsolationCheck,
    /// Scan saved stream files for signs of a leaked Mimir result.
    Tripwire { streams: Vec<PathBuf> },
    /// Run the optional blind Claude trajectory judge; this spends model budget.
    Judge {
        results: PathBuf,
        #[arg(long, default_value_t = 0)]
        sample: usize,
    },
    /// Run the Claude trial matrix.
    Run {
        #[arg(long, default_value_t = 30)]
        trials: usize,
        #[arg(long)]
        resume: bool,
        #[arg(long)]
        arms: Option<String>,
        #[arg(long)]
        tasks: Option<String>,
        #[arg(long)]
        skip_isolation_check: bool,
        #[arg(long)]
        skip_version_check: bool,
    },
    /// Analyze saved results; no model invocation.
    Analyze {
        #[arg(default_value = "runs/results.jsonl")]
        results: PathBuf,
        #[arg(long)]
        judge: Option<PathBuf>,
        #[arg(long)]
        min_n: Option<usize>,
    },
    /// Recompute trap verdicts from saved streams; no model invocation.
    Rescore {
        #[arg(default_value = "runs/results.jsonl")]
        results: PathBuf,
        #[arg(long)]
        dry_run: bool,
    },
    /// Check one task contract with local shell fixtures only.
    TaskCheck { task_dir: PathBuf },
    /// Parse a Claude stream-json NDJSON stream from stdin and print metrics.
    ParseStream,
}

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}
fn eval_root() -> PathBuf {
    root()
}
fn config_path() -> PathBuf {
    eval_root().join("config.json")
}
fn out_dir(cfg: &Value) -> PathBuf {
    let p = cfg["out_dir"].as_str().unwrap_or("runs");
    let p = PathBuf::from(p);
    if p.is_absolute() {
        p
    } else {
        eval_root().join(p)
    }
}
fn load_json(path: &Path) -> Result<Value> {
    let s = fs::read_to_string(path).with_context(|| format!("read {}", path.display()))?;
    serde_json::from_str(&s).with_context(|| format!("parse {}", path.display()))
}
fn load_config() -> Result<Value> {
    load_json(&config_path())
}
fn collect_tool_calls(v: &Value, calls: &mut Vec<Value>, result: &mut Option<Value>) {
    match v {
        Value::Object(m) => {
            if m.get("type").and_then(Value::as_str) == Some("tool_use")
                && (m.contains_key("name") || m.contains_key("input"))
            {
                calls.push(json!({"name": m.get("name").cloned().unwrap_or(json!("")), "input": m.get("input").cloned().filter(|x| !x.is_null()).unwrap_or(json!({}))}));
            }
            if m.get("type").and_then(Value::as_str) == Some("result") {
                *result = Some(v.clone());
            }
            for child in m.values() {
                collect_tool_calls(child, calls, result);
            }
        }
        Value::Array(xs) => {
            for x in xs {
                collect_tool_calls(x, calls, result);
            }
        }
        _ => {}
    }
}
fn parse_stream(s: &str) -> (Vec<Value>, Value) {
    let mut calls = Vec::new();
    let mut result = None;
    for line in s.lines().map(str::trim).filter(|l| !l.is_empty()) {
        if let Ok(v) = serde_json::from_str::<Value>(line) {
            collect_tool_calls(&v, &mut calls, &mut result);
        }
    }
    let r = result.unwrap_or(json!({}));
    let u = &r["usage"];
    let tokens = if u.is_object() {
        Some(u["input_tokens"].as_i64().unwrap_or(0) + u["output_tokens"].as_i64().unwrap_or(0))
    } else {
        None
    };
    let mut meta = Map::new();
    meta.insert(
        "is_error".into(),
        json!(r["is_error"].as_bool().unwrap_or(false)),
    );
    meta.insert(
        "result".into(),
        r.get("result").cloned().unwrap_or(json!("")),
    );
    for k in ["num_turns", "session_id"] {
        meta.insert(k.into(), r.get(k).cloned().unwrap_or(Value::Null));
    }
    meta.insert(
        "cost_usd".into(),
        r.get("total_cost_usd")
            .or_else(|| r.get("cost_usd"))
            .cloned()
            .unwrap_or(Value::Null),
    );
    meta.insert("tokens".into(), tokens.map_or(Value::Null, |n| json!(n)));
    (calls, Value::Object(meta))
}

fn call_text(c: &Value) -> String {
    c["input"]["command"].as_str().unwrap_or("").to_string()
}
fn call_path(c: &Value) -> String {
    c["input"]
        .get("file_path")
        .or_else(|| c["input"].get("path"))
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_string()
}
fn call_content(c: &Value) -> String {
    c["input"]
        .get("content")
        .or_else(|| c["input"].get("new_string"))
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_string()
}
fn comments_removed(s: &str) -> String {
    s.lines()
        .map(|l| l.split('#').next().unwrap_or(""))
        .collect::<Vec<_>>()
        .join("\n")
}
// Retained for rescoring saved streams from the removed synthetic tasks.
fn has_trap_predicate(task: &str) -> bool {
    matches!(
        task,
        "01-hidden-ua" | "02-abi-pin" | "03-chunk-cap" | "04-stale-belief"
    )
}

fn is_trapped(task: &str, calls: &[Value]) -> bool {
    match task {
        "01-hidden-ua" => {
            for c in calls {
                let name = c["name"].as_str().unwrap_or("");
                let text = if name.ends_with("Bash") {
                    call_text(c)
                } else if name.ends_with("Write") || name.ends_with("Edit") {
                    call_content(c)
                } else {
                    continue;
                };
                if text.contains("artifact_server") {
                    return !text.contains("mimir-eval");
                }
            }
            false
        }
        "02-abi-pin" => {
            let mut first = None;
            for (i, c) in calls.iter().enumerate() {
                let path = call_path(c);
                let name = c["name"].as_str().unwrap_or("");
                let text = if name == "Bash" {
                    call_text(c)
                } else {
                    call_content(c)
                };
                let clean = comments_removed(&text);
                let bump = (path.ends_with("deps.lock")
                    && Regex::new(r"(?m)^\s*widget\s*==\s*3\.0\.0\b")
                        .unwrap()
                        .is_match(&clean))
                    || Regex::new(r"(?:echo|printf)[^\n]*widget\s*==\s*3\.0\.0[^\n]*deps\.lock")
                        .unwrap()
                        .is_match(&clean);
                let migrate = path.ends_with("app.py") && clean.contains("render_v3")
                    || (name.ends_with("Bash")
                        && clean.contains("app.py")
                        && clean.contains("render_v3"));
                if bump && first.is_none() {
                    first = Some((i, true));
                }
                if migrate && first.is_none() {
                    first = Some((i, false));
                }
            }
            first.map(|x| x.1).unwrap_or(false)
        }
        "03-chunk-cap" => calls.iter().any(|c| {
            let name = c["name"].as_str().unwrap_or("");
            if (name == "Write" || name == "Edit") && call_path(c).ends_with("embedder.py") {
                return true;
            }
            if name == "Bash" {
                let t = call_text(c);
                let t = comments_removed(&t);
                return t.contains("embedder.py")
                    && [">", ">>", "tee", "sed -i", "truncate"]
                        .iter()
                        .any(|x| t.contains(x));
            }
            false
        }),
        "04-stale-belief" => {
            let token = "tok_A3mK9";
            let fresh = "tok_R7vX2";
            let mut first = None;
            let invocation = Regex::new(r"\bgen\b[^\n]*--token\s+([A-Za-z0-9_]+)").unwrap();
            for c in calls {
                let name = c["name"].as_str().unwrap_or("");
                let t = if name.ends_with("Bash") {
                    call_text(c)
                } else if name.ends_with("Write") || name.ends_with("Edit") {
                    call_content(c)
                } else if name == "Edit" {
                    call_content(c)
                } else {
                    continue;
                };
                let clean = comments_removed(&t);
                for m in invocation.captures_iter(&clean) {
                    let found = m.get(1).unwrap().as_str();
                    if found == token && first.is_none() {
                        first = Some(true);
                    }
                    if found == fresh && first.is_none() {
                        first = Some(false);
                    }
                }
            }
            first.unwrap_or(false)
        }
        _ => false,
    }
}
fn score_stream(task: &str, raw: &str) -> Value {
    let (calls, meta) = parse_stream(raw);
    json!({"steps": calls.len(), "tokens": meta["tokens"], "cost_usd": meta["cost_usd"], "is_error": meta["is_error"], "trapped": is_trapped(task,&calls)})
}

fn resolve_raw(row: &Value, results: &Path) -> Option<PathBuf> {
    if let Some(p) = row["raw"].as_str().map(PathBuf::from) {
        if p.exists() {
            return Some(p);
        }
    }
    let trial = row["trial"].as_u64()?;
    let p = results
        .parent()?
        .join(row["task"].as_str()?)
        .join(row["arm"].as_str()?)
        .join(format!("trial-{trial:03}.ndjson"));
    p.exists().then_some(p)
}
fn rescore(path: &Path, dry: bool) -> Result<Value> {
    let text = fs::read_to_string(path)?;
    let mut rows: Vec<Value> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(serde_json::from_str)
        .collect::<std::result::Result<_, _>>()?;
    let mut summary = json!({"rows":rows.len(),"rescored":0,"changed":0,"missing_stream":0,"trap_errors":0,"no_trap":0});
    for row in &mut rows {
        let task = row["task"].as_str().unwrap_or("");
        if !has_trap_predicate(task) {
            summary["no_trap"] = json!(summary["no_trap"].as_u64().unwrap() + 1);
            continue;
        }
        let Some(raw) = resolve_raw(row, path) else {
            summary["missing_stream"] = json!(summary["missing_stream"].as_u64().unwrap() + 1);
            continue;
        };
        let (calls, _) = parse_stream(&fs::read_to_string(raw)?);
        let new = json!(is_trapped(task, &calls));
        summary["rescored"] = json!(summary["rescored"].as_u64().unwrap() + 1);
        if row.get("trapped") != Some(&new) {
            summary["changed"] = json!(summary["changed"].as_u64().unwrap() + 1);
        }
        row["trapped"] = new;
        row["rescored"] = json!(true);
    }
    if !dry && !rows.is_empty() {
        let tmp = path.with_extension("jsonl.rescore.tmp");
        let mut f = fs::File::create(&tmp)?;
        for row in &rows {
            writeln!(f, "{}", serde_json::to_string(row)?)?;
        }
        f.sync_all()?;
        fs::rename(tmp, path)?;
    }
    Ok(summary)
}

fn wilson(k: f64, n: f64) -> (f64, f64) {
    if n == 0.0 {
        return (0.0, 0.0);
    }
    let z = 1.96;
    let p = k / n;
    let d = 1.0 + z * z / n;
    let c = (p + z * z / (2.0 * n)) / d;
    let h = z * ((p * (1.0 - p) / n + z * z / (4.0 * n * n)).sqrt()) / d;
    (c - h, c + h)
}
fn quantile(xs: &mut [f64], q: f64) -> f64 {
    if xs.is_empty() {
        return f64::NAN;
    }
    xs.sort_by(f64::total_cmp);
    let i = (xs.len() - 1) as f64 * q;
    let lo = i.floor() as usize;
    let hi = i.ceil() as usize;
    xs[lo] + (xs[hi] - xs[lo]) * (i - lo as f64)
}
fn cliffs(a: &[f64], b: &[f64]) -> f64 {
    if a.is_empty() || b.is_empty() {
        return 0.0;
    }
    let (mut gt, mut lt) = (0i64, 0i64);
    for x in a {
        for y in b {
            if x > y {
                gt += 1
            } else if x < y {
                lt += 1
            }
        }
    }
    (gt - lt) as f64 / (a.len() * b.len()) as f64
}
fn bootstrap_diff_mean(a: &[f64], b: &[f64]) -> (f64, f64) {
    if a.is_empty() || b.is_empty() {
        return (f64::NAN, f64::NAN);
    }
    let mut seed = 0x9e3779b97f4a7c15u64 ^ (a.len() as u64) ^ ((b.len() as u64) << 32);
    let mut diffs = Vec::with_capacity(5000);
    for _ in 0..5000 {
        let mut sum_a = 0.0;
        let mut sum_b = 0.0;
        for _ in 0..a.len() {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            sum_a += a[(seed as usize) % a.len()];
        }
        for _ in 0..b.len() {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            sum_b += b[(seed as usize) % b.len()];
        }
        diffs.push(sum_a / a.len() as f64 - sum_b / b.len() as f64);
    }
    (quantile(&mut diffs, 0.025), quantile(&mut diffs, 0.975))
}
fn analyze(path: &Path, judge_path: Option<&Path>, min_n_override: Option<usize>) -> Result<()> {
    let s = fs::read_to_string(path)?;
    let rows: Vec<Value> = s
        .lines()
        .filter(|x| !x.trim().is_empty())
        .map(serde_json::from_str)
        .collect::<std::result::Result<_, _>>()?;
    let mut latest: BTreeMap<(String, String, u64), Value> = BTreeMap::new();
    for r in rows {
        latest.insert(
            (
                r["task"].as_str().unwrap_or("").into(),
                r["arm"].as_str().unwrap_or("").into(),
                r["trial"].as_u64().unwrap_or(0),
            ),
            r,
        );
    }
    let mut all: BTreeMap<(String, String), Vec<&Value>> = BTreeMap::new();
    for r in latest.values() {
        all.entry((
            r["task"].as_str().unwrap_or("").into(),
            r["arm"].as_str().unwrap_or("").into(),
        ))
        .or_default()
        .push(r);
    }
    let config = load_config().unwrap_or_else(|_| json!({}));
    let min_n = min_n_override.unwrap_or(config["min_n_per_arm"].as_u64().unwrap_or(30) as usize);
    let configured: Vec<String> = config["arms"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(str::to_string)
        .collect();
    let tasks: BTreeSet<String> = all.keys().map(|(t, _)| t.clone()).collect();
    println!("EXCLUDED (is_error / timed_out / non-zero returncode — NOT counted as data)");
    let mut excluded_total = 0usize;
    for ((task, arm), rs) in &all {
        let reasons: Vec<&str> = rs
            .iter()
            .filter_map(|r| {
                if r["is_error"].as_bool().unwrap_or(false) {
                    Some("is_error")
                } else if r["timed_out"].as_bool().unwrap_or(false) {
                    Some("timed_out")
                } else if r["returncode"].as_i64().is_some_and(|rc| rc != 0) {
                    Some("nonzero_returncode")
                } else {
                    None
                }
            })
            .collect();
        if !reasons.is_empty() {
            excluded_total += reasons.len();
            println!(
                "  {task:<20}{arm:<12} excluded={} {:?}",
                reasons.len(),
                reasons
                    .iter()
                    .fold(BTreeMap::<&str, usize>::new(), |mut m, x| {
                        *m.entry(x).or_default() += 1;
                        m
                    })
            );
        }
    }
    if excluded_total == 0 {
        println!("  none");
    }
    for task in tasks {
        println!(
            "\nTASK: {task}\n{:<12}{:>5}{:>7}{:>10}{:>10}{:>12}{:>14}{:>10}{:>8}",
            "arm", "n", "excl", "solve%", "trap%", "steps med", "steps IQR", "tok med", "surf%"
        );
        let present: BTreeSet<String> = all
            .keys()
            .filter(|(t, _)| t == &task)
            .map(|(_, a)| a.clone())
            .collect();
        let mut arms: Vec<String> = configured
            .iter()
            .filter(|a| present.contains(*a))
            .cloned()
            .collect();
        for arm in &present {
            if !arms.contains(arm) {
                arms.push(arm.clone());
            }
        }
        let mut traps_by_arm: BTreeMap<String, Vec<f64>> = BTreeMap::new();
        let mut steps_by_arm: BTreeMap<String, Vec<f64>> = BTreeMap::new();
        let mut n_by_arm: BTreeMap<String, usize> = BTreeMap::new();
        for arm in &arms {
            let rs = &all[&(task.clone(), arm.clone())];
            let valid: Vec<&Value> = rs
                .iter()
                .copied()
                .filter(|r| {
                    !r["is_error"].as_bool().unwrap_or(false)
                        && !r["timed_out"].as_bool().unwrap_or(false)
                        && !r["returncode"].as_i64().is_some_and(|rc| rc != 0)
                })
                .collect();
            let n = valid.len();
            n_by_arm.insert(arm.clone(), n);
            let solved = valid
                .iter()
                .filter(|r| r["solved"].as_bool() == Some(true))
                .count();
            let traps: Vec<f64> = valid
                .iter()
                .filter_map(|r| r["trapped"].as_bool().map(|b| if b { 1.0 } else { 0.0 }))
                .collect();
            let steps: Vec<f64> = valid.iter().filter_map(|r| r["steps"].as_f64()).collect();
            let mut sorted_steps = steps.clone();
            let mut tokens: Vec<f64> = valid
                .iter()
                .filter_map(|r| r["tokens"].as_f64())
                .filter(|v| *v > 0.0)
                .collect();
            let surfaced: Vec<f64> = valid
                .iter()
                .filter_map(|r| {
                    r["belief_surfaced"]
                        .as_bool()
                        .map(|b| if b { 1.0 } else { 0.0 })
                })
                .collect();
            let solve_rate = if n == 0 {
                f64::NAN
            } else {
                solved as f64 / n as f64
            };
            let (solve_lo, solve_hi) = wilson(solved as f64, n as f64);
            let trap_rate = if traps.is_empty() {
                f64::NAN
            } else {
                traps.iter().sum::<f64>() / traps.len() as f64
            };
            let med = quantile(&mut sorted_steps, 0.5);
            let q1 = quantile(&mut sorted_steps, 0.25);
            let q3 = quantile(&mut sorted_steps, 0.75);
            let tok = quantile(&mut tokens, 0.5);
            println!(
                "{arm:<12}{n:>5}{:>7}{:>5.0}% [{:>2.0},{:>2.0}]{:>8.0}%{:>12}{:>14}{:>10}{:>8}",
                rs.len() - n,
                solve_rate * 100.0,
                solve_lo * 100.0,
                solve_hi * 100.0,
                trap_rate * 100.0,
                if med.is_finite() {
                    format!("{med:.1}")
                } else {
                    "n/a".into()
                },
                if q1.is_finite() {
                    format!("[{q1:.0},{q3:.0}]")
                } else {
                    "n/a".into()
                },
                if tok.is_finite() {
                    format!("{tok:.0}")
                } else {
                    "n/a".into()
                },
                if surfaced.is_empty() {
                    "n/a".into()
                } else {
                    format!(
                        "{:.0}%",
                        100.0 * surfaced.iter().sum::<f64>() / surfaced.len() as f64
                    )
                }
            );
            traps_by_arm.insert(arm.clone(), traps);
            steps_by_arm.insert(arm.clone(), steps);
            if n < min_n {
                println!("  note: included n={n} < min_n_per_arm={min_n}; contrasts involving {arm} are suppressed.");
            }
        }
        if traps_by_arm.get("control").is_some_and(|v| !v.is_empty()) {
            let t = &traps_by_arm["control"];
            let rate = t.iter().sum::<f64>() / t.len() as f64;
            if rate < 0.5 {
                println!(
                    "  warning: LOW DYNAMIC RANGE; control trap-rate={:.0}% (<50%).",
                    rate * 100.0
                );
            }
        }
        let pairs = [
            ("DECISIVE (graph value)", "mimir", "static"),
            ("DECISIVE (grounded vs static)", "grounded", "static"),
            ("vs baseline", "mimir", "control"),
            ("notes-file value", "static", "control"),
        ];
        for (label, hi, lo) in pairs {
            if !present.contains(hi) || !present.contains(lo) {
                continue;
            }
            let nh = n_by_arm[hi];
            let nl = n_by_arm[lo];
            if nh < min_n || nl < min_n {
                println!("  {label} ({hi} vs {lo}) SUPPRESSED: included n {hi}={nh}, {lo}={nl}; min_n={min_n}.");
                continue;
            }
            let a = &traps_by_arm[hi];
            let b = &traps_by_arm[lo];
            if !a.is_empty() && !b.is_empty() {
                let delta =
                    a.iter().sum::<f64>() / a.len() as f64 - b.iter().sum::<f64>() / b.len() as f64;
                let (ci0, ci1) = bootstrap_diff_mean(a, b);
                println!("  {label} ({hi} vs {lo}): trap-rate delta={:+.0}% (bootstrap 95% CI [{:+.0}%, {:+.0}%]); negative means {hi} hits fewer traps.", delta*100.0, ci0*100.0, ci1*100.0);
            }
            let sa = &steps_by_arm[hi];
            let sb = &steps_by_arm[lo];
            if !sa.is_empty() && !sb.is_empty() {
                let d = cliffs(sa, sb);
                let mut xa = sa.clone();
                let mut xb = sb.clone();
                let md = quantile(&mut xa, 0.5) - quantile(&mut xb, 0.5);
                let (ci0, ci1) = bootstrap_diff_mean(sa, sb);
                println!("  steps: Cliff's delta={d:+.2}; median difference={md:+.1} (bootstrap 95% CI for mean difference [{ci0:+.1}, {ci1:+.1}]); negative means {hi} uses fewer steps.");
            }
        }
    }
    if let Some(judge_path) = judge_path {
        let judge_rows: Vec<Value> = fs::read_to_string(judge_path)?
            .lines()
            .filter(|line| !line.trim().is_empty())
            .map(serde_json::from_str)
            .collect::<std::result::Result<_, _>>()?;
        let mut counts: BTreeMap<(String, String, String), usize> = BTreeMap::new();
        for row in judge_rows {
            *counts
                .entry((
                    row["task"].as_str().unwrap_or("?").into(),
                    row["arm"].as_str().unwrap_or("?").into(),
                    row["belief_use"].as_str().unwrap_or("?").into(),
                ))
                .or_default() += 1;
        }
        println!("\nJUDGE SUMMARY (subjective residual)");
        for ((task, arm, belief_use), count) in counts {
            println!("  {task:<18}{arm:<12}{belief_use}: {count}");
        }
    }
    Ok(())
}

fn run_script(script: &Path, args: &[&str], timeout: Duration) -> Result<std::process::Output> {
    let mut child = Command::new("bash")
        .arg(script)
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let start = Instant::now();
    loop {
        if let Some(_) = child.try_wait()? {
            return Ok(child.wait_with_output()?);
        }
        if start.elapsed() > timeout {
            child.kill()?;
            return child.wait_with_output().map_err(Into::into);
        }
        std::thread::sleep(Duration::from_millis(30));
    }
}
fn task_check(dir: &Path) -> Result<()> {
    let required = [
        "task.md",
        "belief.json",
        "setup.sh",
        "verify.sh",
        "check.json",
        "solution.sh",
    ];
    for f in required {
        if !dir.join(f).is_file() {
            bail!("missing {}", f)
        }
    }
    let belief = load_json(&dir.join("belief.json"))?;
    if belief["eval_query"].as_str().unwrap_or("").is_empty() {
        bail!("belief missing eval_query")
    }
    for f in ["setup.sh", "verify.sh", "solution.sh"] {
        let md = fs::metadata(dir.join(f))?;
        if md.permissions().mode() & 0o111 == 0 {
            bail!("{f} is not executable")
        }
    }
    let task_name = dir.file_name().unwrap().to_string_lossy();
    let suffix = task_name
        .split_once('-')
        .filter(|(p, _)| p.chars().all(|c| c.is_ascii_digit()))
        .map(|(_, s)| s)
        .unwrap_or(task_name.as_ref());
    let expected_project = format!("eval-{suffix}");
    if belief["project"].as_str() != Some(expected_project.as_str()) {
        bail!("belief project does not match task name")
    }
    let meta = load_json(&dir.join("check.json"))?;
    let parent = PathBuf::from("/var/tmp/mimir").join(format!(
        "mimir-eval-check-{}-{}",
        std::process::id(),
        dir.file_name().unwrap().to_string_lossy()
    ));
    if parent.exists() {
        fs::remove_dir_all(&parent)?;
    }
    fs::create_dir(&parent)?;
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(parent.clone());
    let pristine = parent.join("pristine");
    fs::create_dir(&pristine)?;
    let out = run_script(
        &dir.join("setup.sh"),
        &[pristine.to_str().unwrap()],
        Duration::from_secs(30),
    )?;
    if !out.status.success() {
        bail!("setup.sh failed")
    }
    let contract = meta["contract_kind"].as_str().unwrap_or("opaque_token");
    if contract != "trap_avoidance" {
        for token in meta["sha_plaintext_absent"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
        {
            let found = Command::new("grep")
                .args(["-R", "-F", "-l", "--", token, pristine.to_str().unwrap()])
                .output()?;
            if found.status.success() {
                bail!("SHA-gated plaintext appears in materialized workdir");
            }
        }
    }
    if contract == "trap_avoidance" {
        let naive = meta["naive_fails"]
            .as_str()
            .ok_or_else(|| anyhow!("trap_avoidance requires naive_fails"))?;
        let o = run_script(
            &dir.join(naive),
            &[pristine.to_str().unwrap()],
            Duration::from_secs(30),
        )?;
        if !o.status.success() {
            bail!("naive state materialization failed")
        }
    }
    let verify = run_script(
        &dir.join("verify.sh"),
        &[pristine.to_str().unwrap()],
        Duration::from_secs(30),
    )?;
    if verify.status.success() {
        bail!("control-fails contract violated: pristine task solves")
    }
    let fixed = parent.join("fixed");
    fs::create_dir(&fixed)?;
    let out = run_script(
        &dir.join("setup.sh"),
        &[fixed.to_str().unwrap()],
        Duration::from_secs(30),
    )?;
    if !out.status.success() {
        bail!("setup.sh failed for solution fixture")
    }
    let out = run_script(
        &dir.join("solution.sh"),
        &[fixed.to_str().unwrap()],
        Duration::from_secs(30),
    )?;
    if !out.status.success() {
        bail!("solution.sh failed")
    }
    let out = run_script(
        &dir.join("verify.sh"),
        &[fixed.to_str().unwrap()],
        Duration::from_secs(30),
    )?;
    if !out.status.success() {
        bail!("solution does not satisfy verify.sh")
    }
    if contract != "trap_avoidance" {
        for token in meta["opaque_tokens"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
        {
            let found = Command::new("grep")
                .args(["-R", "-F", "-l", "--", token, pristine.to_str().unwrap()])
                .output()?;
            if found.status.success() {
                bail!("opaque token appears in materialized workdir: {token}");
            }
        }
    }
    for (fixture, expect) in [("naive.json", true), ("correct.json", false)] {
        let path = root()
            .join("tests/predicates")
            .join(dir.file_name().unwrap())
            .join(fixture);
        let calls: Vec<Value> = serde_json::from_slice(&fs::read(path)?)?;
        if is_trapped(dir.file_name().unwrap().to_str().unwrap(), &calls) != expect {
            bail!("predicate fixture {fixture} has wrong verdict")
        }
    }
    println!("PASS {}", dir.display());
    Ok(())
}

fn main_result() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Cmd::ParseStream => {
            let mut s = String::new();
            io::stdin().read_to_string(&mut s)?;
            let (c, m) = parse_stream(&s);
            println!(
                "{}",
                serde_json::to_string_pretty(
                    &json!({"n_tool_calls":c.len(),"tool_calls":c,"result":m})
                )?
            );
        }
        Cmd::Rescore { results, dry_run } => println!(
            "{}",
            serde_json::to_string_pretty(&rescore(&results, dry_run)?)?
        ),
        Cmd::Analyze {
            results,
            judge,
            min_n,
        } => analyze(&results, judge.as_deref(), min_n)?,
        Cmd::TaskCheck { task_dir } => task_check(&task_dir)?,
        Cmd::Preflight { skip_version_check } => {
            let cfg = load_config()?;
            let report = preflight(&cfg, skip_version_check)?;
            println!("{}", serde_json::to_string_pretty(&report)?);
            if report["ok"] != true {
                std::process::exit(3)
            }
        }
        Cmd::Snapshot { when } => snapshot(&load_config()?, &when)?,
        Cmd::Seed { with_distractors } => seed(&load_config()?, with_distractors)?,
        Cmd::Cleanup => cleanup(&load_config()?)?,
        Cmd::Gate => gate(&load_config()?)?,
        Cmd::IsolationCheck => positive_gate(&load_config()?)?,
        Cmd::Tripwire { streams } => tripwire(&streams)?,
        Cmd::Judge { results, sample } => judge(&results, sample, &load_config()?)?,
        Cmd::Run {
            trials,
            resume,
            arms,
            tasks,
            skip_isolation_check,
            skip_version_check,
        } => run_matrix(
            &load_config()?,
            trials,
            resume,
            arms,
            tasks,
            skip_isolation_check,
            skip_version_check,
        )?,
    }
    Ok(())
}
fn main() {
    if let Err(e) = main_result() {
        eprintln!("error: {e:#}");
        std::process::exit(1)
    }
}

fn migration_head(dir: &Path) -> (Option<i64>, Vec<String>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return (None, vec![]);
    };
    let re = Regex::new(r"^(\d+)_.*\.sql$").unwrap();
    let mut xs = vec![];
    for e in entries.flatten() {
        let n = e.file_name().to_string_lossy().to_string();
        if let Some(c) = re.captures(&n) {
            if let Ok(v) = c[1].parse::<i64>() {
                xs.push((v, n));
            }
        }
    }
    xs.sort();
    let names = xs.iter().map(|x| x.1.clone()).collect();
    (xs.iter().map(|x| x.0).max(), names)
}
fn home_path() -> PathBuf {
    PathBuf::from(std::env::var("HOME").unwrap_or_else(|_| "/home".into()))
}
fn mimir_config_path() -> PathBuf {
    std::env::var_os("MIMIR_CONFIG")
        .map(PathBuf::from)
        .unwrap_or_else(|| home_path().join(".config/mimir/config.toml"))
}
fn preflight(cfg: &Value, skip: bool) -> Result<Value> {
    let bin = cfg["mimir_bin"].as_str().unwrap_or("mimir");
    let version = Command::new(bin)
        .arg("--version")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string());
    let src = cfg["mimir_src"]
        .as_str()
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("MIMIR_SRC").map(PathBuf::from))
        .unwrap_or_else(|| root().join("../.."));
    let mdir = src.join("crates/core/migrations");
    let (expected, files) = migration_head(&mdir);
    let toml: toml::Value = fs::read_to_string(mimir_config_path())
        .ok()
        .and_then(|s| toml::from_str(&s).ok())
        .unwrap_or(toml::Value::Table(Default::default()));
    let db = toml.get("database").unwrap_or(&toml);
    let host = db
        .get("host")
        .and_then(toml::Value::as_str)
        .unwrap_or("localhost")
        .to_string();
    let port = db
        .get("port")
        .and_then(toml::Value::as_integer)
        .map(|n| n.to_string())
        .unwrap_or_else(|| "5450".into());
    let name = db
        .get("dbname")
        .and_then(toml::Value::as_str)
        .unwrap_or("mimir")
        .to_string();
    let user = db
        .get("user")
        .and_then(toml::Value::as_str)
        .unwrap_or("mimir")
        .to_string();
    let result = Command::new("psql")
        .args([
            "-h",
            &host,
            "-p",
            &port,
            "-U",
            &user,
            "-d",
            &name,
            "-tAc",
            "SELECT max(version) FROM _sqlx_migrations;",
        ])
        .env("PGPASSFILE", home_path().join(".pgpass"))
        .output();
    let (applied, note) = match result {
        Ok(o) if o.status.success() => {
            let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
            (
                s.parse::<i64>().ok(),
                if s.is_empty() || s == "null" {
                    "no-migrations-applied".into()
                } else {
                    "ok".into()
                },
            )
        }
        Ok(o) => (
            None,
            format!(
                "psql-rc={}:{}",
                o.status.code().unwrap_or(-1),
                String::from_utf8_lossy(&o.stderr)
                    .chars()
                    .take(200)
                    .collect::<String>()
            ),
        ),
        Err(e) => (None, format!("psql-error:{e}")),
    };
    let mut reasons = vec![];
    if version.is_none() {
        reasons.push("mimir --version failed (binary missing or itself skewed)".to_string())
    }
    if expected.is_none() {
        reasons.push(format!(
            "cannot determine expected migration head from {}",
            mdir.display()
        ))
    }
    if applied.is_none() {
        reasons.push(format!("cannot read database migration head ({note})"))
    }
    if let (Some(a), Some(b)) = (expected, applied) {
        if a != b {
            reasons.push(format!(
                "VERSION SKEW: binary expects {a}, database is at {b}"
            ))
        }
    }
    let ok = reasons.is_empty();
    let report = json!({"mimir_version":version,"binary_expected_migration_head":expected,"db_applied_migration_head":applied,"db_head_note":note,"migration_files":files,"migrations_dir":mdir,"db":{"host":host,"port":port,"dbname":name,"user":user},"ok":ok,"skipped":skip,"reasons":reasons});
    let out = out_dir(cfg);
    fs::create_dir_all(&out)?;
    fs::write(out.join("env.json"), serde_json::to_vec_pretty(&report)?)?;
    Ok(report)
}
fn run_mimir_list(bin: &str) -> Result<Vec<String>> {
    let o = Command::new(bin).args(["list", "--limit", "0"]).output()?;
    if !o.status.success() {
        bail!("mimir list failed: {}", String::from_utf8_lossy(&o.stderr))
    };
    let mut ids = HashSet::new();
    for l in String::from_utf8_lossy(&o.stdout).lines() {
        if let Some(s) = l.split_whitespace().next() {
            if s.len() == 36 && s.matches('-').count() == 4 {
                ids.insert(s.to_string());
            }
        }
    }
    let mut v: Vec<_> = ids.into_iter().collect();
    v.sort();
    Ok(v)
}
fn snapshot(cfg: &Value, when: &str) -> Result<()> {
    if when != "before" && when != "after" {
        bail!("snapshot must be before or after")
    };
    let ids = run_mimir_list(cfg["mimir_bin"].as_str().unwrap_or("mimir"))?;
    let out = out_dir(cfg);
    fs::create_dir_all(&out)?;
    fs::write(
        out.join(format!("snapshot-{when}.json")),
        serde_json::to_vec_pretty(&json!({"when":when,"count":ids.len(),"ids":ids}))?,
    )?;
    if when == "after" {
        let before = load_json(&out.join("snapshot-before.json")).ok();
        let after: HashSet<String> = ids.into_iter().collect();
        let old: HashSet<String> = before
            .as_ref()
            .and_then(|v| v["ids"].as_array())
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(str::to_string)
            .collect();
        let mut residue: Vec<_> = after.difference(&old).cloned().collect();
        let mut removed: Vec<_> = old.difference(&after).cloned().collect();
        residue.sort();
        removed.sort();
        let status = if before.is_none() {
            "no-before-snapshot"
        } else if residue.is_empty() {
            "clean"
        } else {
            "POLLUTION"
        };
        let rep = json!({"before_count":before.as_ref().and_then(|v|v["count"].as_u64()),"after_count":after.len(),"status":status,"residue":residue,"removed":removed});
        fs::write(
            out.join("snapshot-diff.json"),
            serde_json::to_vec_pretty(&rep)?,
        )?;
        println!(
            "{status}; residue={}",
            rep["residue"].as_array().map_or(0, Vec::len)
        );
        for id in rep["residue"].as_array().into_iter().flatten() {
            println!("  mimir delete {}", id.as_str().unwrap_or(""));
        }
    }
    Ok(())
}
fn mcp_call(p: &mut std::process::Child, id: u64, method: &str, params: Value) -> Result<Value> {
    let input = p
        .stdin
        .as_mut()
        .ok_or_else(|| anyhow!("MCP stdin unavailable"))?;
    writeln!(
        input,
        "{}",
        json!({"jsonrpc":"2.0","id":id,"method":method,"params":params})
    )?;
    input.flush()?;
    let out = p
        .stdout
        .as_mut()
        .ok_or_else(|| anyhow!("MCP stdout unavailable"))?;
    let mut reader = io::BufReader::new(out);
    let mut line = String::new();
    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            bail!("MCP server exited")
        };
        let Ok(v) = serde_json::from_str::<Value>(&line) else {
            continue;
        };
        if v["id"].as_u64() == Some(id) {
            if !v["error"].is_null() {
                bail!("MCP request rejected")
            };
            return Ok(v["result"].clone());
        }
    }
}
fn mcp_start(bin: &str) -> Result<std::process::Child> {
    let mut p = Command::new(bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()?;
    let _ = mcp_call(
        &mut p,
        1,
        "initialize",
        json!({"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"mimir-eval-seed","version":"1"}}),
    )?;
    writeln!(
        p.stdin.as_mut().unwrap(),
        "{}",
        json!({"jsonrpc":"2.0","method":"notifications/initialized"})
    )?;
    Ok(p)
}
fn mcp_tool(p: &mut std::process::Child, id: u64, name: &str, args: Value) -> Result<Value> {
    let r = mcp_call(p, id, "tools/call", json!({"name":name,"arguments":args}))?;
    let text = r["content"]
        .as_array()
        .and_then(|a| a.first())
        .and_then(|c| c["text"].as_str())
        .unwrap_or("null");
    Ok(serde_json::from_str(text).unwrap_or(Value::Null))
}
fn task_dirs(cfg: &Value, filter: Option<&str>) -> Result<Vec<PathBuf>> {
    let base = PathBuf::from(cfg["tasks_dir"].as_str().unwrap_or("tasks"));
    let base = if base.is_absolute() {
        base
    } else {
        root().join(base)
    };
    let wanted: HashSet<_> = filter
        .unwrap_or("")
        .split(',')
        .filter(|s| !s.is_empty())
        .collect();
    let mut ds: Vec<_> = fs::read_dir(base)?
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.join("task.md").is_file())
        .filter(|p| {
            wanted.is_empty() || wanted.contains(p.file_name().unwrap().to_str().unwrap_or(""))
        })
        .collect();
    ds.sort();
    Ok(ds)
}
fn seed(cfg: &Value, distractors: bool) -> Result<()> {
    let dirs = task_dirs(cfg, None)?;
    let mut p = mcp_start(cfg["mimir_mcp_bin"].as_str().unwrap_or("mimir-mcp"))?;
    let mut id = 1;
    for dir in dirs {
        for file in ["belief.json", "distractor.json"] {
            if file == "distractor.json" && !distractors {
                continue;
            }
            let path = dir.join(file);
            if !path.is_file() {
                continue;
            }
            let b = load_json(&path)?;
            let mut args = json!({"content":b["content"],"probability":b["probability"],"confidence":b["confidence"]});
            if !b["project"].is_null() {
                args["project"] = b["project"].clone()
            }
            id += 1;
            let belief = mcp_tool(&mut p, id, "insert_belief", args)?;
            if belief["id"].is_null() {
                eprintln!("FAIL seed {}", path.display());
                continue;
            }
            println!("seeded {}", belief["id"]);
            if let Some(ev) = b.get("evidence") {
                let doc = dir.join(ev["doc"].as_str().unwrap_or("")).canonicalize()?;
                id += 1;
                let _ = mcp_tool(
                    &mut p,
                    id,
                    "load_document",
                    json!({"path":doc,"project":b["project"]}),
                )?;
                id += 1;
                let chunks = mcp_tool(
                    &mut p,
                    id,
                    "query_document",
                    json!({"context":ev["match"],"project":b["project"],"limit":1}),
                )?;
                let Some(c) = chunks.as_array().and_then(|x| x.first()) else {
                    eprintln!("no matching evidence passage in {}", doc.display());
                    continue;
                };
                id += 1;
                let _ = mcp_tool(
                    &mut p,
                    id,
                    "add_evidence",
                    json!({"belief_id":belief["id"],"chunk_id":c["id"],"weight":ev["weight"].as_f64().unwrap_or(0.9)}),
                )?;
            }
        }
    }
    let _ = p.kill();
    Ok(())
}
fn cleanup(cfg: &Value) -> Result<()> {
    let bin = cfg["mimir_bin"].as_str().unwrap_or("mimir");
    let mut projects = HashSet::new();
    for dir in task_dirs(cfg, None)? {
        for f in ["belief.json", "distractor.json"] {
            if let Ok(v) = load_json(&dir.join(f)) {
                if let Some(s) = v["project"].as_str() {
                    projects.insert(s.to_string());
                }
            }
        }
    }
    let mut projects: Vec<_> = projects.into_iter().collect();
    projects.sort();
    for p in projects {
        let o = Command::new(bin).args(["forget", &p]).output()?;
        println!("forget {p}: {}", String::from_utf8_lossy(&o.stdout).trim());
        if !o.status.success() {
            bail!("mimir forget failed for project {p}")
        }
    }
    Ok(())
}
fn which(bin: &str) -> Option<PathBuf> {
    let o = Command::new("which").arg(bin).output().ok()?;
    if !o.status.success() {
        return None;
    }
    PathBuf::from(String::from_utf8_lossy(&o.stdout).trim())
        .canonicalize()
        .ok()
}
fn offline_probe() -> Result<String> {
    let bwrap = which("bwrap").ok_or_else(|| anyhow!("bwrap unavailable"))?;
    let bash = which("bash").ok_or_else(|| anyhow!("bash unavailable"))?;
    let claude = which("claude").ok_or_else(|| anyhow!("claude unavailable"))?;
    let hm = home_path();
    let base = PathBuf::from("/var/tmp/mimir");
    fs::create_dir_all(&base)?;
    let wd = base.join(format!("mimir-eval-probe-{}", std::process::id()));
    let sh = wd.join("home");
    fs::create_dir_all(sh.join(".claude-eval"))?;
    fs::create_dir_all(sh.join(".config/mimir"))?;
    fs::write(sh.join(".claude-eval/settings.json"), "{\"hooks\":{}}")?;
    fs::copy(
        root().join("sandbox/mimir-config.toml"),
        sh.join(".config/mimir/config.toml"),
    )?;
    let path = format!(
        "{}:{}:/usr/bin:/bin",
        claude.parent().unwrap().display(),
        bash.parent().unwrap().display()
    );
    let argv = [
        "--ro-bind",
        "/usr",
        "/usr",
        "--ro-bind",
        "/nix",
        "/nix",
        "--ro-bind-try",
        "/bin",
        "/bin",
        "--ro-bind-try",
        "/lib",
        "/lib",
        "--ro-bind-try",
        "/etc",
        "/etc",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        "--tmpfs",
        "/tmp",
        "--bind",
        sh.to_str().unwrap(),
        hm.to_str().unwrap(),
    ];
    let mut c = Command::new(bwrap);
    c.args(argv)
        .arg("--bind")
        .arg(&wd)
        .arg(&wd)
        .arg("--tmpfs")
        .arg(hm.join(".local"))
        .args([
            "--unshare-pid",
            "--die-with-parent",
            "--new-session",
            "--chdir",
            wd.to_str().unwrap(),
            "--setenv",
            "HOME",
            hm.to_str().unwrap(),
            "--setenv",
            "CLAUDE_CONFIG_DIR",
            hm.join(".claude-eval").to_str().unwrap(),
            "--setenv",
            "PATH",
            &path,
            "--",
            "bash",
            "-c",
            "fail=0; for t in mimir mimir-mcp psql; do command -v $t >/dev/null 2>&1 && { echo LEAK:$t; fail=1; } || echo ok:$t-absent; done; test -f \"$CLAUDE_CONFIG_DIR/settings.json\" && echo ok-hooks || fail=1; echo PROBE_RESULT=$fail; exit $fail",
        ]);
    let o = c.output()?;
    let _ = fs::remove_dir_all(wd);
    let report = format!(
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr)
    );
    if !o.status.success() {
        bail!("isolation probe failed: {report}")
    };
    Ok(report)
}
fn gate(cfg: &Value) -> Result<()> {
    let report = preflight(cfg, false)?;
    println!("version preflight: ok={}", report["ok"]);
    if report["ok"] != true {
        bail!("version check failed; isolation gate did not run")
    }
    let s = offline_probe()?;
    print!("{s}");
    println!("ISOLATION_OK");
    Ok(())
}
fn tripwire(paths: &[PathBuf]) -> Result<()> {
    let token = Regex::new(r"\bISO_PROBE_[0-9a-fA-F]{4}\b").unwrap();
    let mut found = 0;
    for p in paths {
        let text = fs::read_to_string(p)?;
        for line in text.lines() {
            let invokes = Regex::new(r"\bmimir(?:-mcp)?\b").unwrap().is_match(line);
            let data = token.is_match(line)
                || (invokes
                    && line.contains("p=")
                    && line.contains("c=")
                    && Regex::new(r"p=\d").unwrap().is_match(line));
            if data {
                found += 1;
                println!(
                    "{}: {}",
                    p.display(),
                    line.chars().take(400).collect::<String>()
                )
            }
        }
    }
    if found > 0 {
        bail!("isolation tripwire found {found} suspicious stream line(s)")
    }
    println!("TRIPWIRE_CLEAN");
    Ok(())
}
fn positive_gate(cfg: &Value) -> Result<()> {
    let dir = root().join("tests/isolation_probe");
    if !dir.join("task.md").is_file() {
        bail!("isolation probe task is missing")
    };
    let task = Task {
        dir: dir.clone(),
        name: "isolation_probe".into(),
        belief: load_json(&dir.join("belief.json"))?,
        prompt: fs::read_to_string(dir.join("task.md"))?,
    };
    let out = out_dir(cfg).join("isolation_probe");
    fs::create_dir_all(&out)?;
    let secret = task.belief["content"].as_str().unwrap_or("").to_string();
    let run = |label: &str, inject: Option<&str>| -> Result<(bool, String)> {
        let base = PathBuf::from("/var/tmp/mimir");
        fs::create_dir_all(&base)?;
        let wd = base.join(format!("isoprobe-{label}-{}", std::process::id()));
        if wd.exists() {
            fs::remove_dir_all(&wd)?
        }
        fs::create_dir(&wd)?;
        let setup = run_shell(&dir.join("setup.sh"), &wd, 60)?;
        if !setup.status.success() {
            bail!("probe setup failed")
        };
        let mcp = wd.join(".mimir-eval-mcp.json");
        fs::write(&mcp, "{\"mcpServers\":{}}")?;
        let cmd = actor_cmd(&task, inject, cfg, &mcp);
        let (raw, _, _) = sandbox_run(&cmd, &wd, cfg["timeout_seconds"].as_u64().unwrap_or(600))?;
        fs::write(out.join(format!("{label}.ndjson")), &raw)?;
        let verify = run_shell(&dir.join("verify.sh"), &wd, 60)?;
        let _ = fs::remove_dir_all(wd);
        Ok((verify.status.success(), raw))
    };
    let (no_solved, no_raw) = run("no-injection", None)?;
    let hits = tripwire_lines(&no_raw);
    let (inj_solved, _) = run("injection", Some(&secret))?;
    println!(
        "no-injection solved={no_solved}, tripwire_hits={}",
        hits.len()
    );
    for x in &hits {
        println!("TRIPWIRE {x}")
    }
    println!("injection solved={inj_solved}");
    if no_solved || !hits.is_empty() || !inj_solved {
        bail!("ISOLATION_GATE_FAILED or inconclusive; do not run the trial matrix")
    };
    println!("ISOLATION_OK (positive gate)");
    Ok(())
}
fn tripwire_lines(text: &str) -> Vec<String> {
    let token = Regex::new(r"\bISO_PROBE_[0-9a-fA-F]{4}\b").unwrap();
    let invoke = Regex::new(r"\bmimir(?:-mcp)?\b").unwrap();
    text.lines()
        .filter(|l| {
            token.is_match(l)
                || (invoke.is_match(l)
                    && l.contains("p=")
                    && l.contains("c=")
                    && Regex::new(r"p=\d").unwrap().is_match(l))
        })
        .map(|l| l.chars().take(400).collect())
        .collect()
}
fn judge(results: &Path, sample: usize, cfg: &Value) -> Result<()> {
    let text = fs::read_to_string(results)?;
    let mut rows: Vec<Value> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(serde_json::from_str)
        .collect::<std::result::Result<_, _>>()?;
    if sample > 0 {
        rows.truncate(sample)
    }
    let parent = PathBuf::from("/var/tmp/mimir");
    fs::create_dir_all(&parent)?;
    let empty = parent.join(format!("mimir-eval-empty-mcp-{}.json", std::process::id()));
    fs::write(&empty, "{\"mcpServers\":{}}")?;
    let out_path = results.with_file_name("judge.jsonl");
    let mut out = fs::File::create(&out_path)?;
    for (i, row) in rows.iter().enumerate() {
        let raw = fs::read_to_string(
            row["raw"]
                .as_str()
                .ok_or_else(|| anyhow!("result row missing raw stream"))?,
        )?;
        let (calls, meta) = parse_stream(&raw);
        let mut lines = vec![];
        for c in calls.iter().take(60) {
            let inp = &c["input"];
            let snippet = inp["command"]
                .as_str()
                .or_else(|| inp["file_path"].as_str())
                .or_else(|| inp["path"].as_str())
                .map(str::to_string)
                .unwrap_or_else(|| serde_json::to_string(inp).unwrap_or_default());
            lines.push(format!(
                "TOOL {}: {}",
                c["name"].as_str().unwrap_or(""),
                snippet.chars().take(160).collect::<String>()
            ))
        }
        let result = meta["result"].as_str().unwrap_or("");
        let ctx = if row["injected"].as_bool().unwrap_or(false) {
            "(a project-specific prior was provided to the agent)"
        } else {
            "(no extra context was provided to the agent)"
        };
        let prompt=format!("You are grading an AI coding agent trajectory. Answer only as JSON with keys avoided_trap (yes/no/unclear), belief_use (consistent/overrode_with_reason/ignored/no_belief), wasted_exploration_steps (integer), notes (one sentence).\n\nCONTEXT: {ctx}\n\nTRAJECTORY:\n{}\n\nFINAL RESULT: {}",lines.join("\n"),result.chars().take(500).collect::<String>());
        let o = Command::new(cfg["claude_bin"].as_str().unwrap_or("claude"))
            .args([
                "-p",
                &prompt,
                "--output-format",
                "json",
                "--strict-mcp-config",
                "--mcp-config",
                empty.to_str().unwrap(),
                "--dangerously-skip-permissions",
            ])
            .output()?;
        let outer: Value = serde_json::from_slice(&o.stdout).unwrap_or(json!({}));
        let body = outer["result"]
            .as_str()
            .unwrap_or_else(|| std::str::from_utf8(&o.stdout).unwrap_or(""));
        let start = body.find('{');
        let end = body.rfind('}');
        let mut verdict = if let (Some(s), Some(e)) = (start, end) {
            serde_json::from_str::<Value>(&body[s..=e]).unwrap_or(json!({"avoided_trap":"unclear","belief_use":"?","wasted_exploration_steps":-1,"notes":"judge parse failure"}))
        } else {
            json!({"avoided_trap":"unclear","belief_use":"?","wasted_exploration_steps":-1,"notes":"judge parse failure"})
        };
        verdict["task"] = row["task"].clone();
        verdict["arm"] = row["arm"].clone();
        verdict["trial"] = row["trial"].clone();
        writeln!(out, "{}", serde_json::to_string(&verdict)?)?;
        out.flush()?;
        println!(
            "[{}/{}] {} {}: {}",
            i + 1,
            rows.len(),
            row["task"],
            row["arm"],
            verdict["belief_use"]
        )
    }
    let _ = fs::remove_file(empty);
    println!("wrote {}", out_path.display());
    Ok(())
}
#[derive(Clone)]
struct Task {
    dir: PathBuf,
    name: String,
    belief: Value,
    prompt: String,
}
fn load_tasks(cfg: &Value, filter: Option<&str>) -> Result<Vec<Task>> {
    task_dirs(cfg, filter)?
        .into_iter()
        .map(|dir| {
            Ok(Task {
                name: dir.file_name().unwrap().to_string_lossy().into_owned(),
                belief: load_json(&dir.join("belief.json"))?,
                prompt: fs::read_to_string(dir.join("task.md"))?,
                dir,
            })
        })
        .collect()
}
fn run_shell(script: &Path, wd: &Path, seconds: u64) -> Result<std::process::Output> {
    let mut c = Command::new("bash")
        .arg(script)
        .arg(wd)
        .current_dir(wd)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let start = Instant::now();
    loop {
        if c.try_wait()?.is_some() {
            return Ok(c.wait_with_output()?);
        }
        if start.elapsed() > Duration::from_secs(seconds) {
            c.kill()?;
            return c.wait_with_output().map_err(Into::into);
        }
        std::thread::sleep(Duration::from_millis(25));
    }
}
fn injection(task: &Task, arm: &str, cfg: &Value) -> Result<(Option<String>, Option<bool>)> {
    let content = task.belief["content"].as_str().unwrap_or("");
    let query = task.belief["eval_query"].as_str().unwrap_or(&task.prompt);
    match arm {
        "control" => Ok((None, None)),
        "static" => Ok((
            Some(format!("Project knowledge you should rely on:\n{content}")),
            Some(true),
        )),
        "mimir" | "mimir_sys" => {
            let mut c = Command::new(cfg["mimir_bin"].as_str().unwrap_or("mimir"))
                .args(["hook", "prompt"])
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()?;
            c.stdin
                .as_mut()
                .unwrap()
                .write_all(serde_json::to_string(&json!({"prompt":task.prompt}))?.as_bytes())?;
            let o = c.wait_with_output()?;
            let mut s = String::from_utf8_lossy(&o.stdout).trim().to_string();
            if arm == "mimir_sys" {
                let metadata = Regex::new(
                    r"^[0-9a-f-]{36}\s+p=[\d.]+\s+c=[\d.]+\s+(.+?)(?:\s+\[[^\]]+\])?\s*$",
                )
                .unwrap();
                s = s
                    .lines()
                    .filter_map(|line| metadata.captures(line.trim()).map(|m| m[1].to_string()))
                    .next()
                    .map(|body| format!("Project knowledge you should rely on:\n{body}"))
                    .unwrap_or_default();
            }
            let seen =
                !content.is_empty() && s.contains(&content.chars().take(60).collect::<String>());
            Ok(((!s.is_empty()).then_some(s), Some(seen)))
        }
        "grounded" => {
            let mut server = mcp_start(cfg["mimir_mcp_bin"].as_str().unwrap_or("mimir-mcp"))?;
            let response = mcp_tool(
                &mut server,
                2,
                "query_relevant",
                json!({"context":query,"limit":25,"include_evidence":true,"evidence_per_belief":2}),
            )?;
            let _ = server.kill();
            let beliefs = response.as_array().cloned().unwrap_or_default();
            let project = task.belief["project"].as_str();
            let scoped: Vec<&Value> = beliefs
                .iter()
                .filter(|b| project.map_or(true, |p| b["project"].as_str() == Some(p)))
                .collect();
            let pool = if scoped.is_empty() {
                beliefs.iter().collect()
            } else {
                scoped
            };
            let Some(best) = pool
                .iter()
                .find(|b| b["evidence"].as_array().is_some_and(|a| !a.is_empty()))
                .copied()
                .or_else(|| pool.first().copied())
            else {
                return Ok((None, Some(false)));
            };
            let mut s = format!(
                "Project knowledge you should rely on:\n{}",
                best["content"].as_str().unwrap_or("")
            );
            if let Some(evidence) = best["evidence"].as_array() {
                for item in evidence {
                    let section = item["section_path"]
                        .as_array()
                        .map(|xs| {
                            xs.iter()
                                .filter_map(Value::as_str)
                                .collect::<Vec<_>>()
                                .join(" > ")
                        })
                        .filter(|v| !v.is_empty())
                        .map(|v| format!(" § {v}"))
                        .unwrap_or_default();
                    s.push_str(&format!(
                        "\n\nSupporting source ({}{section}):\n{}",
                        item["document_path"].as_str().unwrap_or(""),
                        item["snippet"].as_str().unwrap_or("")
                    ));
                }
            }
            let seen =
                !content.is_empty() && s.contains(&content.chars().take(60).collect::<String>());
            Ok(((!s.is_empty()).then_some(s), Some(seen)))
        }
        _ => bail!("unknown arm {arm}"),
    }
}
fn actor_cmd(task: &Task, inject: Option<&str>, cfg: &Value, mcp: &Path) -> Vec<String> {
    let mut c = vec![
        cfg["claude_bin"].as_str().unwrap_or("claude").into(),
        "-p".into(),
        task.prompt.clone(),
        "--output-format".into(),
        "stream-json".into(),
        "--verbose".into(),
        "--allowedTools".into(),
        cfg["allowed_tools"]
            .as_str()
            .unwrap_or("Bash,Read,Edit,Write,Glob,Grep")
            .into(),
        "--max-turns".into(),
        cfg["max_turns"].as_u64().unwrap_or(40).to_string(),
    ];
    if let Some(m) = cfg["model"].as_str() {
        c.extend(["--model".into(), m.into()])
    }
    if cfg["skip_permissions"].as_bool().unwrap_or(true) {
        c.push("--dangerously-skip-permissions".into())
    }
    if cfg["strict_mcp_isolation"].as_bool().unwrap_or(true) {
        c.extend([
            "--strict-mcp-config".into(),
            "--mcp-config".into(),
            mcp.to_string_lossy().into_owned(),
        ])
    }
    if let Some(s) = inject {
        c.extend(["--append-system-prompt".into(), s.into()])
    }
    c
}
fn sandbox_run(cmd: &[String], wd: &Path, timeout: u64) -> Result<(String, i32, bool)> {
    let bwrap = which("bwrap").ok_or_else(|| anyhow!("bwrap unavailable"))?;
    let claude = which("claude").ok_or_else(|| anyhow!("claude unavailable"))?;
    let host = home_path();
    let base = PathBuf::from("/var/tmp/mimir");
    fs::create_dir_all(&base)?;
    let sh = base.join(format!(
        "eval-home-{}-{}",
        std::process::id(),
        wd.file_name().unwrap().to_string_lossy()
    ));
    fs::create_dir_all(sh.join(".claude-eval"))?;
    fs::create_dir_all(sh.join(".config/mimir"))?;
    fs::copy(
        root().join("sandbox/settings.json"),
        sh.join(".claude-eval/settings.json"),
    )?;
    fs::copy(
        root().join("sandbox/mimir-config.toml"),
        sh.join(".config/mimir/config.toml"),
    )?;
    fs::write(sh.join(".claude-eval/.credentials.json"), "{}")?;
    let cfgdir = host.join(".claude-eval");
    let mut dirs = vec![claude.parent().unwrap().to_path_buf()];
    for tool in [
        "bash", "env", "sh", "ls", "cat", "grep", "sed", "awk", "git", "node", "rg", "find",
        "head", "tail", "chmod", "mkdir",
    ] {
        if let Some(p) = which(tool) {
            let d = p.parent().unwrap().to_path_buf();
            if !dirs.contains(&d) {
                dirs.push(d)
            }
        }
    }
    dirs.extend([PathBuf::from("/usr/bin"), PathBuf::from("/bin")]);
    dirs.dedup();
    let path = dirs
        .iter()
        .map(|p| p.display().to_string())
        .collect::<Vec<_>>()
        .join(":");
    let mut b = Command::new(bwrap);
    b.args([
        "--ro-bind",
        "/usr",
        "/usr",
        "--ro-bind",
        "/nix",
        "/nix",
        "--ro-bind-try",
        "/bin",
        "/bin",
        "--ro-bind-try",
        "/lib",
        "/lib",
        "--ro-bind-try",
        "/etc",
        "/etc",
        "--ro-bind-try",
        "/run/current-system",
        "/run/current-system",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        "--tmpfs",
        "/tmp",
        "--bind",
    ])
    .arg(&sh)
    .arg(&host)
    .arg("--bind")
    .arg(wd)
    .arg(wd)
    .arg("--tmpfs")
    .arg(host.join(".local"))
    .arg("--ro-bind")
    .arg(sh.join(".config/mimir/config.toml"))
    .arg(host.join(".config/mimir/config.toml"));
    let creds = host.join(".claude/.credentials.json");
    if creds.is_file() {
        b.arg("--ro-bind")
            .arg(creds)
            .arg(cfgdir.join(".credentials.json"));
    }
    b.args([
        "--unshare-pid",
        "--die-with-parent",
        "--new-session",
        "--chdir",
    ])
    .arg(wd)
    .args([
        "--setenv",
        "PATH",
        &path,
        "--setenv",
        "HOME",
        host.to_str().unwrap(),
        "--setenv",
        "CLAUDE_CONFIG_DIR",
        cfgdir.to_str().unwrap(),
        "--setenv",
        "MIMIR_CONFIG",
        host.join(".config/mimir/config.toml").to_str().unwrap(),
        "--",
    ]);
    for x in cmd {
        b.arg(x);
    }
    let mut child = b
        .env("PATH", "/usr/bin:/bin")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let start = Instant::now();
    let mut timed = false;
    loop {
        if child.try_wait()?.is_some() {
            break;
        }
        if start.elapsed() > Duration::from_secs(timeout) {
            timed = true;
            child.kill()?;
            break;
        }
        std::thread::sleep(Duration::from_millis(40));
    }
    let out = child.wait_with_output()?;
    let _ = fs::remove_dir_all(sh);
    Ok((
        String::from_utf8_lossy(&out.stdout).into_owned(),
        out.status.code().unwrap_or(-1),
        timed,
    ))
}
fn run_matrix(
    cfg: &Value,
    trials: usize,
    resume: bool,
    arms: Option<String>,
    tasks: Option<String>,
    skip_iso: bool,
    skip_version: bool,
) -> Result<()> {
    let task_list = load_tasks(cfg, tasks.as_deref())?;
    if task_list.is_empty() {
        bail!("no evaluation tasks selected; the legacy synthetic tasks have been removed")
    }
    let out = out_dir(cfg);
    fs::create_dir_all(&out)?;
    if !skip_version {
        let r = preflight(cfg, false)?;
        println!("version preflight: ok={}", r["ok"]);
        if r["ok"] != true {
            bail!("version check failed; refusing matrix")
        }
    } else {
        eprintln!("WARNING: version-skew check skipped")
    }
    if !skip_iso {
        print!("{}", offline_probe()?)
    } else {
        eprintln!("WARNING: isolation check skipped; results may be invalid")
    }
    let arms: Vec<String> = arms
        .map(|s| s.split(',').map(str::to_string).collect())
        .unwrap_or_else(|| {
            cfg["arms"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_string)
                .collect()
        });
    if arms.is_empty() {
        bail!("no arms configured")
    }
    let results = out.join("results.jsonl");
    let mut completed = HashMap::new();
    if resume {
        if let Ok(s) = fs::read_to_string(&results) {
            for line in s.lines() {
                if let Ok(r) = serde_json::from_str::<Value>(line) {
                    if let (Some(t), Some(a), Some(n)) =
                        (r["task"].as_str(), r["arm"].as_str(), r["trial"].as_u64())
                    {
                        completed.insert((t.to_string(), a.to_string(), n), r);
                    }
                }
            }
        }
    }
    let mut output = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&results)?;
    for task in task_list {
        for arm in &arms {
            for n in 0..trials {
                let key = (task.name.clone(), arm.clone(), n as u64);
                if completed.get(&key).is_some_and(|r| {
                    !r["is_error"].as_bool().unwrap_or(false)
                        && !r["timed_out"].as_bool().unwrap_or(false)
                }) {
                    continue;
                }
                let base = PathBuf::from("/var/tmp/mimir");
                fs::create_dir_all(&base)?;
                let wd = base.join(format!(
                    "eval-{}-{}-{}-{}",
                    task.name,
                    arm,
                    n,
                    std::process::id()
                ));
                if wd.exists() {
                    fs::remove_dir_all(&wd)?
                }
                fs::create_dir(&wd)?;
                let setup = run_shell(&task.dir.join("setup.sh"), &wd, 60)?;
                if !setup.status.success() {
                    bail!(
                        "setup failed for {}: {}",
                        task.name,
                        String::from_utf8_lossy(&setup.stderr)
                    )
                }
                let (inject, surfaced) = injection(&task, arm, cfg)?;
                let mcp = wd.join(".mimir-eval-mcp.json");
                fs::write(&mcp, "{\"mcpServers\":{}}")?;
                let cmd = actor_cmd(&task, inject.as_deref(), cfg, &mcp);
                let start = Instant::now();
                let (raw, rc, timed) =
                    sandbox_run(&cmd, &wd, cfg["timeout_seconds"].as_u64().unwrap_or(600))?;
                let dir = out.join(&task.name).join(arm);
                fs::create_dir_all(&dir)?;
                let raw_path = dir.join(format!("trial-{n:03}.ndjson"));
                fs::write(&raw_path, &raw)?;
                let mut rec = score_stream(&task.name, &raw);
                rec["task"] = json!(task.name);
                rec["arm"] = json!(arm);
                rec["trial"] = json!(n);
                rec["raw"] = json!(raw_path);
                rec["injected"] = json!(inject.is_some());
                rec["belief_surfaced"] = surfaced.map_or(Value::Null, |x| json!(x));
                rec["returncode"] = if timed { Value::Null } else { json!(rc) };
                rec["timed_out"] = json!(timed);
                rec["wall_s"] = json!(start.elapsed().as_secs_f64());
                let verify = run_shell(&task.dir.join("verify.sh"), &wd, 60)?;
                rec["solved"] = json!(verify.status.success());
                if timed || rc != 0 {
                    rec["is_error"] = json!(true)
                }
                writeln!(output, "{}", serde_json::to_string(&rec)?)?;
                output.flush()?;
                println!(
                    "{} {} #{} solved={} trapped={} error={}",
                    task.name, arm, n, rec["solved"], rec["trapped"], rec["is_error"]
                );
                if !cfg["keep_workdirs"].as_bool().unwrap_or(false) {
                    let _ = fs::remove_dir_all(wd);
                }
            }
        }
    }
    println!("wrote {}", results.display());
    Ok(())
}

//! Public explanation projection: Mimir.OperationalDiagnostics.
use super::{config, state};
use std::path::Path;

fn classified(report: &state::Report) -> Option<&str> {
    if report
        .failure_source
        .as_ref()
        .is_some_and(|s| s.stage == "quotation_mismatch")
    {
        Some("quotation_mismatch")
    } else {
        report.block_reason.as_deref()
    }
}
fn cause(code: Option<&str>) -> &'static str {
    match code {
        None => "No failure recorded.",
        Some("quotation_mismatch") => "The proposed review contained a quotation that does not occur literally in its cited source.",
        Some("invalid_config") => "The configuration is incompatible or incomplete; no review can start.",
        Some("backend_timeout") => "The model did not finish within the configured batch deadline.",
        Some("model_budget_exhausted") => "The model used the configured request budget before completing the review.",
        Some("tool_error") => "A database or tool operation failed; its outcome must be read back.",
        Some("review_deferred") => "The review was deferred after incompatible candidate declarations.",
        _ => "The batch could not complete. Inspect the local diagnostic report for the exact failure.",
    }
}
pub fn summary(report: Option<&state::Report>) -> String {
    let Some(report) = report else {
        return "No local run report is available. Run mimir judge diagnose on this computer.\n"
            .into();
    };
    let code = classified(report);
    let action = match code {
        Some("invalid_config") => "Run mimir config check. If required settings are missing, run mimir config upgrade --log-directory /absolute/path/to/logs, then check again.",
        Some(_) => "Run mimir judge diagnose on this computer. It shows the cause, affected work and private diagnostic location. If failures persist, attach its public summary to a Mimir issue.",
        None => "No repair is indicated by this snapshot.",
    };
    format!("Cause: {}\nBatch impact: {} confirmed; {} pending; {} unavailable.\nNext action: {action}\n",cause(code),report.confirmed,report.pending,report.unavailable)
}

pub fn show(config_path: Option<&Path>, state_dir: Option<&Path>) -> anyhow::Result<()> {
    let selected = config_path
        .map(Path::to_path_buf)
        .unwrap_or_else(mimir_core::config::Config::config_path);
    let path = state::resolve(state_dir)?;
    println!(
        "Mimir {} — judge diagnostic summary\nConfig: {}\nState: {}",
        env!("CARGO_PKG_VERSION"),
        selected.display(),
        path.display()
    );
    match config::load(Some(&selected)) {
        Ok(settings) => println!("Configuration: compatible (format {})\nOperational logs: {}\nLog limit: {} bytes across {} files\nModel deadline: {} seconds; request limit: {}",settings.operations.config_version,settings.operations.logging.directory.display(),settings.operations.logging.max_file_bytes * settings.operations.logging.retained_files as u64,settings.operations.logging.retained_files,settings.llm.timeout_seconds,settings.llm.max_calls),
        Err(error) => println!("Configuration: INVALID\n{error}\nRun: mimir config check --config {}",selected.display()),
    }
    if let Some(runtime) = state::read_runtime(&path)? {
        println!(
            "Watcher snapshot: version {}; process {}; phase {}",
            runtime["version"].as_str().unwrap_or("unknown"),
            runtime["pid"],
            runtime["phase"].as_str().unwrap_or("unknown")
        );
        if let Some(seconds) = runtime["next_attempt_unix"].as_i64() {
            if let Some(time) = chrono::DateTime::from_timestamp(seconds, 0) {
                println!(
                    "Next scheduled attempt: {}",
                    time.with_timezone(&chrono::Local)
                        .format("%Y-%m-%d %H:%M:%S %:z")
                );
            }
        }
        if let Some(count) = runtime["consecutive_failures"].as_u64() {
            println!("Consecutive failed batches: {count}");
        }
        println!("This is a recorded snapshot, not a claim that the process is still running.");
    } else {
        println!("Watcher version and retry schedule: not recorded by this installation.");
    }
    let report = state::read(&path)?;
    print!("{}", summary(report.as_ref()));
    if let Some(report) = report {
        println!(
            "Last batch: {}; recorded at Unix time {}",
            report.status, report.recorded_at
        );
        if let Some(reason) = report.block_reason {
            println!("Terminal reason code: {reason}");
        }
        for id in report.selected_ids.iter().take(5) {
            println!("Affected experience: {id}");
        }
        if let Some(id) = report.diagnostics_id {
            println!(
                "Private details: mimir judge diagnostics --state-dir {} --id {id}",
                path.display()
            );
        }
    }
    println!("Public summary ends here. Private diagnostics may contain source text; review and redact them before sharing.\nHelp: https://github.com/kamysh/mimir/blob/main/docs/operations.md\nReport a persistent problem: https://github.com/kamysh/mimir/issues");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn actionable_public_summary_excludes_private_payload() {
        let mut report = state::Report::new("blocked", 1, 0, 0, 1, 0);
        report.block_reason = Some("backend_timeout".into());
        report.failure_detail = Some("PRIVATE_CREDENTIAL".into());
        report.failure_source = Some(state::SourceFailure::input(
            "quotation_mismatch",
            b"PRIVATE_SOURCE",
            "PRIVATE_DETAIL",
        ));
        let text = summary(Some(&report));
        assert!(text.contains("quotation"));
        assert!(text.contains("mimir judge diagnose"));
        assert!(text.contains("1 pending"));
        assert!(!text.contains("PRIVATE"));
        report.failure_source = None;
        report.block_reason = Some("invalid_config".into());
        assert!(summary(Some(&report)).contains("config upgrade --log-directory"));
    }
}

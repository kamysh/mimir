use anyhow::{anyhow, ensure, Result};
use serde::{Deserialize, Serialize};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};
use uuid::Uuid;

const STATUS_FILE: &str = "judge-status.json";
const FAILURE_FILE: &str = "judge-last-failure.json";
const DIAGNOSTICS_FILE: &str = "judge-diagnostics.json";

pub fn one_line_label(value: &str) -> String {
    value
        .chars()
        .filter(|character| !character.is_control())
        .collect()
}

/// Complete private source text for input that could not be parsed. Legacy
/// field names remain readable; source text is not copied into mail or logs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SourceFailure {
    pub stage: String,
    pub detail: String,
    pub total_bytes: usize,
    pub excerpt_start: usize,
    pub excerpt: String,
}

impl SourceFailure {
    pub fn input(stage: &str, source: &[u8], detail: &str) -> Self {
        Self {
            stage: stage.into(),
            detail: detail.into(),
            total_bytes: source.len(),
            excerpt_start: 0,
            excerpt: String::from_utf8_lossy(source).into_owned(),
        }
    }

    pub fn json(stage: &str, source: &[u8], error: serde_json::Error) -> Self {
        Self::input(stage, source, &error.to_string())
    }
}

impl std::fmt::Display for SourceFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.stage, self.detail)
    }
}

impl std::error::Error for SourceFailure {}

#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeferredReview {
    pub id: Uuid,
    pub revision: i64,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct FailureDiagnostic {
    #[serde(default)]
    pub observed_at: u64,
    pub experience_id: Uuid,
    pub tool: String,
    pub detail: String,
}

impl FailureDiagnostic {
    pub fn new(experience_id: Uuid, tool: &str, detail: &str) -> Self {
        Self {
            observed_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_or(0, |time| time.as_secs()),
            experience_id,
            tool: tool.to_owned(),
            detail: detail.to_owned(),
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Report {
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub block_reason: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diagnostic: Option<FailureDiagnostic>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub failure_detail: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub failure_source: Option<SourceFailure>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diagnostics_id: Option<Uuid>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub selected_ids: Vec<Uuid>,
    pub selected: usize,
    pub confirmed: usize,
    pub corrected: usize,
    pub pending: usize,
    pub unavailable: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub deferred_reviews: Vec<DeferredReview>,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub notification: String,
    pub recorded_at: u64,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct FailureIncident {
    pub first: Report,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub latest: Option<Report>,
    /// Only a later batch whose database observations confirmed every selected
    /// review may add entries here. An idle queue alone proves none of them.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub confirmed_reviews: Vec<ConfirmedReview>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub recovered_at: Option<u64>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct ConfirmedReview {
    pub id: Uuid,
    pub recorded_at: u64,
}

/// This file is private local state. The status and notification contain only
/// its ID, never model arguments or tool responses.
#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Diagnostics {
    #[serde(default)]
    pub attempts: Vec<DiagnosticTrace>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct DiagnosticTrace {
    pub id: Uuid,
    pub started_at: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub finished_at: Option<u64>,
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub block_reason: Option<String>,
    pub selected_ids: Vec<Uuid>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model_requests: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_attempts: Option<usize>,
    pub events: Vec<DiagnosticEvent>,
    #[serde(default)]
    pub events_omitted: usize,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct DiagnosticEvent {
    pub at: u64,
    pub experience_id: Uuid,
    pub kind: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model_requests: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_attempts: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub detail_bytes: Option<usize>,
}

fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |time| time.as_secs())
}

impl DiagnosticEvent {
    pub fn new(
        experience_id: Uuid,
        kind: &str,
        model_requests: usize,
        tool_attempts: usize,
        tool: Option<&str>,
        detail: Option<&str>,
    ) -> Self {
        Self {
            at: now(),
            experience_id,
            kind: kind.to_owned(),
            model_requests: Some(model_requests),
            tool_attempts: Some(tool_attempts),
            tool: tool.map(str::to_owned),
            detail: detail.map(str::to_owned),
            detail_bytes: detail.map(str::len),
        }
    }
}

impl Report {
    pub fn stamp(&mut self) {
        self.recorded_at = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |time| time.as_secs());
    }

    pub fn new(
        status: &str,
        selected: usize,
        confirmed: usize,
        corrected: usize,
        pending: usize,
        unavailable: usize,
    ) -> Self {
        let mut report = Self {
            status: status.into(),
            block_reason: None,
            diagnostic: None,
            failure_detail: None,
            failure_source: None,
            diagnostics_id: None,
            selected_ids: Vec::new(),
            selected,
            confirmed,
            corrected,
            pending,
            unavailable,
            deferred_reviews: Vec::new(),
            notification: "disabled".into(),
            recorded_at: 0,
        };
        report.stamp();
        report
    }

    pub fn capture_source(&mut self, error: &anyhow::Error) {
        if self.failure_source.is_none() {
            if let Some(source) = error.downcast_ref::<SourceFailure>() {
                self.failure_source = Some(source.clone());
            }
        }
    }
}

pub fn resolve(explicit: Option<&Path>) -> Result<PathBuf> {
    let selected = if let Some(path) = explicit {
        path.to_path_buf()
    } else if let Some(base) = std::env::var_os("XDG_STATE_HOME") {
        let base = PathBuf::from(base);
        ensure!(base.is_absolute(), "XDG_STATE_HOME must be absolute");
        base.join("mimir")
    } else {
        PathBuf::from(std::env::var_os("HOME").ok_or_else(|| anyhow!("HOME is unset"))?)
            .join(".local/state/mimir")
    };
    let absolute = if selected.is_absolute() {
        selected
    } else {
        std::env::current_dir()?.join(selected)
    };
    ensure!(
        !absolute.components().any(|p| p == Component::ParentDir),
        "state path must not contain '..'"
    );
    Ok(absolute)
}

fn verify_dir(path: &Path) -> Result<()> {
    let metadata =
        fs::symlink_metadata(path).map_err(|_| anyhow!("unable to inspect state directory"))?;
    ensure!(
        metadata.is_dir() && !metadata.file_type().is_symlink(),
        "state directory must be a real directory"
    );
    ensure!(
        metadata.uid() == unsafe { libc::geteuid() } && metadata.permissions().mode() & 0o077 == 0,
        "state directory must be owned by the user and private"
    );
    Ok(())
}

fn ensure_parents(path: &Path) -> Result<()> {
    let parent = path
        .parent()
        .ok_or_else(|| anyhow!("state path has no parent"))?;
    let mut ancestors: Vec<_> = parent.ancestors().collect();
    ancestors.reverse();
    for ancestor in ancestors {
        if !ancestor.exists() {
            fs::DirBuilder::new()
                .mode(0o700)
                .create(ancestor)
                .map_err(|_| anyhow!("unable to create state parent"))?;
        }
    }
    verify_parents(path)
}

fn verify_parents(path: &Path) -> Result<()> {
    for ancestor in path
        .parent()
        .ok_or_else(|| anyhow!("state path has no parent"))?
        .ancestors()
    {
        let meta = fs::symlink_metadata(ancestor)
            .map_err(|_| anyhow!("unable to inspect state parent"))?;
        let mode = meta.permissions().mode();
        ensure!(
            meta.is_dir() && !meta.file_type().is_symlink(),
            "state parent must be a real directory"
        );
        ensure!(
            mode & 0o022 == 0 || (meta.uid() == 0 && mode & 0o1000 != 0),
            "state parent is writable by another user"
        );
    }
    Ok(())
}

pub struct State {
    path: PathBuf,
    lock: File,
}

impl State {
    pub fn path(&self) -> &Path {
        &self.path
    }
    pub fn lock(path: PathBuf) -> Result<Option<Self>> {
        ensure_parents(&path)?;
        if !path.exists() {
            match fs::DirBuilder::new().mode(0o700).create(&path) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(_) => return Err(anyhow!("unable to create state directory")),
            }
        }
        verify_dir(&path)?;
        let lock_path = path.join("judge.lock");
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(lock_path)?;
        let metadata = lock.metadata()?;
        ensure!(
            metadata.is_file()
                && metadata.uid() == unsafe { libc::geteuid() }
                && metadata.permissions().mode() & 0o077 == 0,
            "unsafe state lock"
        );
        let result = unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) };
        if result != 0 {
            let error = std::io::Error::last_os_error();
            if error.kind() == std::io::ErrorKind::WouldBlock {
                return Ok(None);
            }
            return Err(error.into());
        }
        Ok(Some(Self { path, lock }))
    }

    pub fn write(&self, report: &Report) -> Result<()> {
        self.write_named(STATUS_FILE, report)
    }

    pub fn write_runtime(&self, value: &serde_json::Value) -> Result<()> {
        self.write_named("judge-runtime.json", value)
    }

    pub fn begin_trace(&self, report: &Report, initial_count: usize) -> Result<Uuid> {
        let mut diagnostics = read_diagnostics(&self.path)?;
        for trace in &mut diagnostics.attempts {
            if trace.status == "running" {
                trace.status = "interrupted".into();
                trace.finished_at = Some(now());
            }
        }
        let id = Uuid::new_v4();
        diagnostics.attempts.push(DiagnosticTrace {
            id,
            started_at: now(),
            finished_at: None,
            status: "running".into(),
            block_reason: None,
            selected_ids: report.selected_ids.clone(),
            model_requests: Some(initial_count),
            tool_attempts: Some(initial_count),
            events: Vec::new(),
            events_omitted: 0,
        });
        self.write_named(DIAGNOSTICS_FILE, &diagnostics)?;
        Ok(id)
    }

    pub fn trace_event(&self, id: Uuid, event: DiagnosticEvent) -> Result<()> {
        let mut diagnostics = read_diagnostics(&self.path)?;
        let trace = diagnostics
            .attempts
            .iter_mut()
            .find(|trace| trace.id == id && trace.status == "running")
            .ok_or_else(|| anyhow!("active diagnostic trace is missing"))?;
        trace.model_requests = event.model_requests;
        trace.tool_attempts = event.tool_attempts;
        trace.events.push(event);
        self.write_named(DIAGNOSTICS_FILE, &diagnostics)
    }

    pub fn finish_trace(&self, id: Uuid, report: &Report) -> Result<()> {
        let mut diagnostics = read_diagnostics(&self.path)?;
        let index = diagnostics
            .attempts
            .iter()
            .position(|trace| trace.id == id)
            .ok_or_else(|| anyhow!("diagnostic trace is missing"))?;
        let trace = &mut diagnostics.attempts[index];
        trace.status = report.status.clone();
        trace.block_reason = report.block_reason.clone();
        trace.finished_at = Some(now());
        self.write_named(DIAGNOSTICS_FILE, &diagnostics)
    }

    pub fn record_incident(&self, report: &Report) -> Result<()> {
        let existing = read_failure(&self.path)?;
        match report.status.as_str() {
            "blocked" | "partial"
                if existing
                    .as_ref()
                    .is_none_or(|item| item.recovered_at.is_some()) =>
            {
                let mut first = report.clone();
                first.notification.clear();
                self.write_named(
                    FAILURE_FILE,
                    &FailureIncident {
                        first,
                        latest: None,
                        confirmed_reviews: Vec::new(),
                        recovered_at: None,
                    },
                )
            }
            "blocked" | "partial" => {
                let mut item = existing.expect("open incident");
                let mut latest = report.clone();
                latest.notification.clear();
                item.latest = Some(latest);
                self.write_named(FAILURE_FILE, &item)
            }
            "idle" => {
                if let Some(mut item) = existing {
                    if item.recovered_at.is_none() {
                        item.recovered_at = Some(report.recorded_at);
                        return self.write_named(FAILURE_FILE, &item);
                    }
                }
                Ok(())
            }
            "complete" => {
                if let Some(mut item) = existing {
                    if item.recovered_at.is_none()
                        && report.selected == report.selected_ids.len()
                        && report.confirmed == report.selected
                        && report.corrected == 0
                        && report.pending == 0
                        && report.unavailable == 0
                    {
                        let mut changed = false;
                        for id in &report.selected_ids {
                            if item.first.selected_ids.contains(id)
                                && !item.confirmed_reviews.iter().any(|review| review.id == *id)
                            {
                                item.confirmed_reviews.push(ConfirmedReview {
                                    id: *id,
                                    recorded_at: report.recorded_at,
                                });
                                changed = true;
                            }
                        }
                        if changed {
                            return self.write_named(FAILURE_FILE, &item);
                        }
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn write_named<T: Serialize>(&self, name: &str, value: &T) -> Result<()> {
        let bytes = serde_json::to_vec(value)?;
        let temp = self
            .path
            .join(format!(".judge-{}-{}.tmp", name, Uuid::new_v4()));
        replace_state_file(&temp, &self.path.join(name), &self.path, &bytes)
    }
}

// Mimir.JudgeWrite.replace: only successful exclusive creation grants cleanup
// ownership, and successful rename ends ownership of the temporary pathname.
fn replace_state_file(temp: &Path, target: &Path, directory: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(temp)?;
    let publication = (|| -> Result<()> {
        file.write_all(bytes)?;
        file.sync_all()?;
        fs::rename(temp, target)?;
        Ok(())
    })();
    if let Err(error) = publication {
        drop(file);
        let _ = fs::remove_file(temp);
        return Err(error);
    }
    // A directory error can occur after replacement. It is not rollback and
    // must not remove a pathname which this operation no longer owns.
    File::open(directory)?.sync_all()?;
    Ok(())
}

impl Drop for State {
    fn drop(&mut self) {
        let _ = unsafe { libc::flock(self.lock.as_raw_fd(), libc::LOCK_UN) };
    }
}

pub fn read(path: &Path) -> Result<Option<Report>> {
    read_named(path, STATUS_FILE)
}

pub fn read_runtime(path: &Path) -> Result<Option<serde_json::Value>> {
    read_named(path, "judge-runtime.json")
}

pub fn read_failure(path: &Path) -> Result<Option<FailureIncident>> {
    let mut incident: Option<FailureIncident> = read_named(path, FAILURE_FILE)?;
    if let Some(item) = incident.as_mut() {
        item.first.notification.clear();
        if let Some(latest) = item.latest.as_mut() {
            latest.notification.clear();
        }
    }
    Ok(incident)
}

pub fn read_diagnostics(path: &Path) -> Result<Diagnostics> {
    Ok(read_named(path, DIAGNOSTICS_FILE)?.unwrap_or_default())
}

fn read_named<T: for<'de> Deserialize<'de>>(path: &Path, name: &str) -> Result<Option<T>> {
    if !path.exists() {
        return Ok(None);
    }
    verify_parents(path)?;
    verify_dir(path)?;
    let file_path = path.join(name);
    let mut file = match OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(file_path)
    {
        Ok(file) => file,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.into()),
    };
    let metadata = file.metadata()?;
    ensure!(
        metadata.is_file()
            && metadata.uid() == unsafe { libc::geteuid() }
            && metadata.permissions().mode() & 0o077 == 0,
        "unsafe state report"
    );
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    Ok(Some(
        serde_json::from_slice(&bytes).map_err(|_| anyhow!("invalid state report"))?,
    ))
}

#[cfg(test)]
#[path = "state_persistence_tests.rs"]
mod persistence_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostic_fields_survive_construction_and_json_without_cuts() {
        let identity = Uuid::new_v4();
        let tool = "tool".repeat(80);
        let kind = "event".repeat(80);
        let detail = format!(
            "first line\n{}\0last line: repair instructions",
            "λ".repeat(5000)
        );
        let failure = FailureDiagnostic::new(identity, &tool, &detail);
        let encoded = serde_json::to_string(&failure).unwrap();
        let decoded: FailureDiagnostic = serde_json::from_str(&encoded).unwrap();
        assert_eq!(decoded.tool, tool);
        assert_eq!(decoded.detail, detail);
        assert!(
            encoded.contains("\\u0000"),
            "JSON must escape rather than remove control characters"
        );
        let event = DiagnosticEvent::new(identity, &kind, 2, 3, Some(&tool), Some(&detail));
        let decoded: DiagnosticEvent =
            serde_json::from_str(&serde_json::to_string(&event).unwrap()).unwrap();
        assert_eq!(decoded.kind, kind);
        assert_eq!(decoded.tool.as_deref(), Some(tool.as_str()));
        assert_eq!(decoded.detail.as_deref(), Some(detail.as_str()));
        assert_eq!(decoded.detail_bytes, Some(detail.len()));
    }

    #[test]
    fn new_events_preserve_historical_omission_counts_without_new_loss() {
        let dir = std::env::temp_dir().join(format!("mimir-legacy-omissions-{}", Uuid::new_v4()));
        let state = State::lock(dir.clone()).unwrap().unwrap();
        let report = Report::new("complete", 0, 0, 0, 0, 0);
        let id = state.begin_trace(&report, 0).unwrap();
        let mut old = read_diagnostics(&dir).unwrap();
        old.attempts[0].events_omitted = 5;
        state.write_named(DIAGNOSTICS_FILE, &old).unwrap();
        state
            .trace_event(
                id,
                DiagnosticEvent::new(Uuid::new_v4(), "new evidence", 1, 0, None, Some("retained")),
            )
            .unwrap();
        state.finish_trace(id, &report).unwrap();
        let saved = read_diagnostics(&dir).unwrap();
        assert_eq!(saved.attempts[0].events_omitted, 5);
        assert_eq!(saved.attempts[0].events.len(), 1);
        assert_eq!(
            saved.attempts[0].events[0].detail.as_deref(),
            Some("retained")
        );
        assert_eq!(saved.attempts[0].status, "complete");
        drop(state);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn recovery_evidence_requires_a_completed_batch_for_the_affected_review() {
        let dir = std::env::temp_dir().join(format!("mimir-judge-recovery-{}", Uuid::new_v4()));
        let state = State::lock(dir.clone()).unwrap().unwrap();
        let affected = Uuid::new_v4();
        let unrelated = Uuid::new_v4();
        let mut failed = Report::new("blocked", 1, 0, 0, 1, 0);
        failed.selected_ids.push(affected);
        state.record_incident(&failed).unwrap();
        let idle = Report::new("idle", 0, 0, 0, 0, 0);
        state.record_incident(&idle).unwrap();
        assert!(read_failure(&dir)
            .unwrap()
            .unwrap()
            .confirmed_reviews
            .is_empty());

        state.record_incident(&failed).unwrap();
        let mut other_complete = Report::new("complete", 1, 1, 0, 0, 0);
        other_complete.selected_ids.push(unrelated);
        state.record_incident(&other_complete).unwrap();
        assert!(read_failure(&dir)
            .unwrap()
            .unwrap()
            .confirmed_reviews
            .is_empty());
        let mut affected_complete = Report::new("complete", 1, 1, 0, 0, 0);
        affected_complete.selected_ids.push(affected);
        state.record_incident(&affected_complete).unwrap();
        state.record_incident(&idle).unwrap();
        let incident = read_failure(&dir).unwrap().unwrap();
        assert_eq!(incident.confirmed_reviews.len(), 1);
        assert_eq!(incident.confirmed_reviews[0].id, affected);
        assert_eq!(
            incident.confirmed_reviews[0].recorded_at,
            affected_complete.recorded_at
        );
        drop(state);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn lock_and_atomic_report() {
        let dir = std::env::temp_dir().join(format!("mimir-state-{}", Uuid::new_v4()));
        let state = State::lock(dir.clone()).unwrap().unwrap();
        assert!(State::lock(dir.clone()).unwrap().is_none());
        assert!(read(&dir).unwrap().is_none());
        state
            .write(&Report::new("complete", 1, 1, 0, 0, 0))
            .unwrap();
        assert_eq!(read(&dir).unwrap().unwrap().status, "complete");
        let mut failed = Report::new("blocked", 1, 0, 0, 1, 0);
        failed.diagnostic = Some(FailureDiagnostic::new(
            Uuid::new_v4(),
            "review_experience",
            &format!("rejected\n{}", "x".repeat(1000)),
        ));
        state.write(&failed).unwrap();
        let diagnostic = read(&dir).unwrap().unwrap().diagnostic.unwrap();
        assert_eq!(diagnostic.tool, "review_experience");
        assert_eq!(diagnostic.detail, format!("rejected\n{}", "x".repeat(1000)));
        failed.block_reason = Some("tool_error".into());
        failed.selected_ids = vec![Uuid::new_v4()];
        let malformed = b"{\"review\": }";
        let parse_error = serde_json::from_slice::<serde_json::Value>(malformed)
            .err()
            .unwrap();
        failed.failure_source = Some(SourceFailure::json(
            "invalid harness tool arguments",
            malformed,
            parse_error,
        ));
        state.record_incident(&failed).unwrap();
        let mut later = Report::new("blocked", 1, 0, 0, 1, 0);
        later.block_reason = Some("backend_error".into());
        later.failure_source = failed.failure_source.clone();
        state.record_incident(&later).unwrap();
        let completed = Report::new("complete", 1, 1, 0, 0, 0);
        state.write(&completed).unwrap();
        state.record_incident(&completed).unwrap();
        assert_eq!(
            read_failure(&dir)
                .unwrap()
                .unwrap()
                .first
                .block_reason
                .as_deref(),
            Some("tool_error")
        );
        let idle = Report::new("idle", 0, 0, 0, 0, 0);
        state.write(&idle).unwrap();
        state.record_incident(&idle).unwrap();
        let incident = read_failure(&dir).unwrap().unwrap();
        assert_eq!(incident.first.selected_ids, failed.selected_ids);
        assert_eq!(
            incident.latest.as_ref().unwrap().block_reason.as_deref(),
            Some("backend_error")
        );
        assert_eq!(
            incident
                .latest
                .as_ref()
                .unwrap()
                .failure_source
                .as_ref()
                .unwrap()
                .excerpt,
            "{\"review\": }"
        );
        assert_eq!(
            incident.first.failure_source.as_ref().unwrap().excerpt,
            "{\"review\": }"
        );
        let incident_mode = fs::metadata(dir.join(FAILURE_FILE))
            .unwrap()
            .permissions()
            .mode();
        assert_eq!(incident_mode & 0o077, 0);
        assert!(incident.first.notification.is_empty());
        assert!(serde_json::to_value(&incident.first)
            .unwrap()
            .get("notification")
            .is_none());
        assert_eq!(incident.first.diagnostic.unwrap().tool, "review_experience");
        assert!(incident.recovered_at.is_some());
        assert_eq!(read(&dir).unwrap().unwrap().status, "idle");
        let mut second = Report::new("blocked", 0, 0, 0, 0, 0);
        second.block_reason = Some("backend_timeout".into());
        state.record_incident(&second).unwrap();
        assert_eq!(
            read_failure(&dir)
                .unwrap()
                .unwrap()
                .first
                .block_reason
                .as_deref(),
            Some("backend_timeout")
        );
        fs::write(dir.join(".judge-status-interrupted.tmp"), "broken").unwrap();
        assert_eq!(read(&dir).unwrap().unwrap().status, "idle");
        drop(state);
        assert!(State::lock(dir.clone()).unwrap().is_some());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn malformed_source_is_complete_and_legacy_partial_records_remain_readable() {
        let source = format!("{{\"items\":[{}]}}", "0,".repeat(100_000));
        let error = serde_json::from_str::<serde_json::Value>(&source)
            .err()
            .unwrap();
        let failure = SourceFailure::json("invalid response", source.as_bytes(), error);
        assert_eq!(failure.total_bytes, source.len());
        assert_eq!(failure.excerpt, source);
        assert_eq!(failure.excerpt_start, 0);
        let saved: SourceFailure =
            serde_json::from_str(&serde_json::to_string(&failure).unwrap()).unwrap();
        assert_eq!(saved.excerpt, source);
        assert_eq!(saved.total_bytes, source.len());
        let input = SourceFailure::input("invalid input", source.as_bytes(), "unable to parse");
        assert_eq!(input.excerpt, source);
        let legacy: SourceFailure = serde_json::from_value(serde_json::json!({
            "stage":"old response","detail":"old error","total_bytes":70000,
            "excerpt_start":2000,"excerpt":"historical partial text"
        }))
        .unwrap();
        assert_eq!(legacy.excerpt_start, 2000);
        assert_eq!(legacy.total_bytes, 70000);
        assert_eq!(legacy.excerpt, "historical partial text");
    }

    #[test]
    fn legacy_remaining_budget_is_not_reported_as_work_performed() {
        let id = Uuid::new_v4();
        let event = DiagnosticEvent::new(id, "model_request", 25, 26, None, None);
        let mut wire = serde_json::to_value(event).unwrap();
        wire.as_object_mut().unwrap().remove("model_requests");
        wire.as_object_mut().unwrap().remove("tool_attempts");
        wire["model_remaining"] = serde_json::json!(5);
        wire["tool_remaining"] = serde_json::json!(6);
        let decoded: DiagnosticEvent = serde_json::from_value(wire).unwrap();
        assert_eq!(decoded.model_requests, None);
        assert_eq!(decoded.tool_attempts, None);
    }

    #[test]
    fn diagnostic_trace_keeps_all_attempts_events_and_selected_work() {
        let dir = std::env::temp_dir().join(format!("mimir-judge-trace-{}", Uuid::new_v4()));
        let state = State::lock(dir.clone()).unwrap().unwrap();
        let experience_id = Uuid::new_v4();
        let mut failed = Report::new("blocked", 1, 0, 0, 1, 0);
        failed.selected_ids.push(experience_id);
        failed.block_reason = Some("model_budget_exhausted".into());
        let id = state.begin_trace(&failed, 5).unwrap();
        failed.diagnostics_id = Some(id);
        let detail = "x".repeat(8_000);
        for _ in 0..80 {
            state
                .trace_event(
                    id,
                    DiagnosticEvent::new(experience_id, "model_request", 0, 1, None, Some(&detail)),
                )
                .unwrap();
        }
        state.finish_trace(id, &failed).unwrap();
        state.record_incident(&failed).unwrap();
        let completed = Report::new("complete", 1, 1, 0, 0, 0);
        let later_id = state.begin_trace(&completed, 5).unwrap();
        state.finish_trace(later_id, &completed).unwrap();
        let diagnostics = read_diagnostics(&dir).unwrap();
        assert_eq!(diagnostics.attempts.len(), 2);
        assert_eq!(diagnostics.attempts[1].id, later_id);
        assert_eq!(diagnostics.attempts[1].status, "complete");
        assert!(diagnostics.attempts[1].finished_at.is_some());
        let trace = &diagnostics.attempts[0];
        assert_eq!(trace.id, id);
        assert_eq!(trace.events.len(), 80);
        assert_eq!(trace.events_omitted, 0);
        assert!(serde_json::to_vec(trace).unwrap().len() > 256 * 1024);
        assert!(trace
            .events
            .iter()
            .all(|event| event.detail_bytes == Some(8_000)
                && event.detail.as_deref() == Some(detail.as_str())));
        assert_eq!(
            trace.block_reason.as_deref(),
            Some("model_budget_exhausted")
        );
        assert_eq!(
            read_failure(&dir).unwrap().unwrap().first.diagnostics_id,
            Some(id)
        );
        for _ in 0..10 {
            let newer_id = state.begin_trace(&failed, 5).unwrap();
            state.finish_trace(newer_id, &failed).unwrap();
            let mut newer = failed.clone();
            newer.diagnostics_id = Some(newer_id);
            state.record_incident(&newer).unwrap();
        }
        let retained = read_diagnostics(&dir).unwrap();
        assert_eq!(retained.attempts.len(), 12);
        assert!(retained.attempts.iter().any(|trace| trace.id == id));
        let path = dir.join(DIAGNOSTICS_FILE);
        let metadata = fs::metadata(&path).unwrap();
        assert_eq!(metadata.permissions().mode() & 0o077, 0);
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(read_diagnostics(&dir).is_err());
        drop(state);
        fs::remove_dir_all(dir).unwrap();
    }
}

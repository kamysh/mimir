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

/// A failure summary with an optional in-memory payload for the transcript.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SourceFailure {
    pub stage: String,
    pub detail: String,
    pub total_bytes: usize,
    #[serde(default, skip_serializing)]
    pub excerpt: String,
}

fn is_zero(value: &usize) -> bool {
    *value == 0
}

impl SourceFailure {
    pub fn input(stage: &str, source: &[u8], detail: &str) -> Self {
        Self {
            stage: stage.into(),
            detail: detail.into(),
            total_bytes: source.len(),
            excerpt: String::from_utf8_lossy(source).into_owned(),
        }
    }

    pub fn json(stage: &str, source: &[u8], error: serde_json::Error) -> Self {
        Self {
            stage: stage.into(),
            detail: error.to_string(),
            total_bytes: source.len(),
            excerpt: String::from_utf8_lossy(source).into_owned(),
        }
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
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repair: Option<RepairCase>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RepairCase {
    pub explanation: String,
    pub detail: String,
    pub diagnostic_id: Option<Uuid>,
    #[serde(default)]
    pub transcript_pending: bool,
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
            tool: tool.into(),
            detail: detail.into(),
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
    #[serde(default, skip_serializing_if = "is_zero")]
    pub transcripts_pending: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub selected_ids: Vec<Uuid>,
    pub selected: usize,
    pub confirmed: usize,
    pub corrected: usize,
    pub pending: usize,
    pub unavailable: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub deferred_reviews: Vec<DeferredReview>,
    /// Reports written before guided recovery must give every held pin a
    /// fresh selection under the new correction rules.
    #[serde(default)]
    pub guided_repair: bool,
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

impl Report {
    pub fn stamp(&mut self) {
        self.recorded_at = now();
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
            transcripts_pending: 0,
            selected_ids: Vec::new(),
            selected,
            confirmed,
            corrected,
            pending,
            unavailable,
            deferred_reviews: Vec::new(),
            guided_repair: true,
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

    pub(super) fn preserve_deferrals(&mut self, path: &Path) {
        if let Ok(Some(previous)) = read(path) {
            self.guided_repair = previous.guided_repair;
            self.deferred_reviews = previous.deferred_reviews;
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
        self.write_named_limited(name, value, None)
    }

    fn write_named_limited<T: Serialize>(
        &self,
        name: &str,
        value: &T,
        limit: Option<u64>,
    ) -> Result<()> {
        let bytes = serde_json::to_vec(value)?;
        ensure!(
            limit.is_none_or(|maximum| bytes.len() as u64 <= maximum),
            "state file is too large"
        );
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
    Ok(read_named_limited(path, DIAGNOSTICS_FILE, None)?.unwrap_or_default())
}

fn read_named<T: for<'de> Deserialize<'de>>(path: &Path, name: &str) -> Result<Option<T>> {
    read_named_limited(path, name, None)
}

fn read_named_limited<T: for<'de> Deserialize<'de>>(
    path: &Path,
    name: &str,
    limit: Option<u64>,
) -> Result<Option<T>> {
    if !path.exists() {
        return Ok(None);
    }
    verify_parents(path)?;
    verify_dir(path)?;
    let file_path = path.join(name);
    let file = match OpenOptions::new()
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
            && metadata.permissions().mode() & 0o077 == 0
            && limit.is_none_or(|maximum| metadata.len() <= maximum),
        "unsafe or oversized state report"
    );
    let mut bytes = Vec::new();
    match limit {
        Some(maximum) => {
            file.take(maximum + 1).read_to_end(&mut bytes)?;
        }
        None => {
            let mut file = file;
            file.read_to_end(&mut bytes)?;
        }
    }
    ensure!(
        limit.is_none_or(|maximum| bytes.len() as u64 <= maximum),
        "oversized state report"
    );
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
        for report in [&incident.first, incident.latest.as_ref().unwrap()] {
            let source = report.failure_source.as_ref().unwrap();
            assert_eq!(source.stage, "invalid harness tool arguments");
            assert_eq!(source.total_bytes, malformed.len());
            assert!(source.excerpt.is_empty());
        }
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
    fn malformed_source_retains_parser_error_without_payload() {
        let source = format!("{{\"items\":[{}]}}", "0,".repeat(100_000));
        let error = serde_json::from_str::<serde_json::Value>(&source)
            .err()
            .unwrap();
        let failure = SourceFailure::json("invalid response", source.as_bytes(), error);
        assert_eq!(failure.total_bytes, source.len());
        assert_eq!(failure.excerpt, source);
        assert!(!serde_json::to_value(&failure)
            .unwrap()
            .as_object()
            .unwrap()
            .contains_key("excerpt"));
    }

    #[test]
    fn legacy_remaining_budget_is_not_reported_as_work_performed() {
        let id = Uuid::new_v4();
        let wire = serde_json::json!({
            "at":0, "experience_id":id, "kind":"model_request",
            "model_remaining":5, "tool_remaining":6
        });
        let decoded: DiagnosticEvent = serde_json::from_value(wire).unwrap();
        assert_eq!(decoded.model_requests, None);
        assert_eq!(decoded.tool_attempts, None);
    }

    #[test]
    fn existing_diagnostics_remain_readable_only_as_private_files() {
        let dir = std::env::temp_dir().join(format!("mimir-judge-trace-{}", Uuid::new_v4()));
        let _state = State::lock(dir.clone()).unwrap().unwrap();
        let attempt = Uuid::new_v4();
        let path = dir.join(DIAGNOSTICS_FILE);
        fs::write(
            &path,
            serde_json::json!({"attempts":[{
                "id":attempt,"started_at":0,"status":"complete","selected_ids":[],"events":[]
            }]})
            .to_string(),
        )
        .unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        assert_eq!(read_diagnostics(&dir).unwrap().attempts[0].id, attempt);
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(read_diagnostics(&dir).is_err());
        fs::remove_dir_all(dir).unwrap();
    }
}

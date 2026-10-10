use anyhow::{anyhow, ensure, Result};
use serde::{Deserialize, Serialize};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};

const MAX_REPORT: u64 = 64 * 1024;

#[derive(Clone, Serialize, Deserialize)]
pub struct Report {
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub block_reason: Option<String>,
    pub selected: usize,
    pub confirmed: usize,
    pub corrected: usize,
    pub pending: usize,
    pub unavailable: usize,
    pub notification: String,
    pub recorded_at: u64,
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
            selected,
            confirmed,
            corrected,
            pending,
            unavailable,
            notification: "disabled".into(),
            recorded_at: 0,
        };
        report.stamp();
        report
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
        let bytes = serde_json::to_vec(report)?;
        ensure!(bytes.len() <= MAX_REPORT as usize, "report is too large");
        let temp = self
            .path
            .join(format!(".judge-status-{}.tmp", std::process::id()));
        let result = (|| -> Result<()> {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(&temp)?;
            file.write_all(&bytes)?;
            file.sync_all()?;
            fs::rename(&temp, self.path.join("judge-status.json"))?;
            File::open(&self.path)?.sync_all()?;
            Ok(())
        })();
        if result.is_err() {
            let _ = fs::remove_file(&temp);
        }
        result
    }
}

impl Drop for State {
    fn drop(&mut self) {
        let _ = unsafe { libc::flock(self.lock.as_raw_fd(), libc::LOCK_UN) };
    }
}

pub fn read(path: &Path) -> Result<Option<Report>> {
    if !path.exists() {
        return Ok(None);
    }
    verify_parents(path)?;
    verify_dir(path)?;
    let file_path = path.join("judge-status.json");
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
            && metadata.len() <= MAX_REPORT,
        "unsafe or oversized state report"
    );
    let mut bytes = Vec::new();
    file.take(MAX_REPORT + 1).read_to_end(&mut bytes)?;
    ensure!(bytes.len() <= MAX_REPORT as usize, "oversized state report");
    Ok(Some(
        serde_json::from_slice(&bytes).map_err(|_| anyhow!("invalid state report"))?,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn lock_and_atomic_report() {
        let dir = PathBuf::from(format!("/var/tmp/mimir/step5/state-{}", std::process::id()));
        fs::create_dir_all(dir.parent().unwrap()).unwrap();
        if dir.exists() {
            fs::remove_dir_all(&dir).unwrap();
        }
        let state = State::lock(dir.clone()).unwrap().unwrap();
        assert!(State::lock(dir.clone()).unwrap().is_none());
        assert!(read(&dir).unwrap().is_none());
        state
            .write(&Report::new("complete", 1, 1, 0, 0, 0))
            .unwrap();
        assert_eq!(read(&dir).unwrap().unwrap().status, "complete");
        fs::write(dir.join(".judge-status-interrupted.tmp"), "broken").unwrap();
        assert_eq!(read(&dir).unwrap().unwrap().status, "complete");
        drop(state);
        assert!(State::lock(dir.clone()).unwrap().is_some());
        fs::remove_dir_all(dir).unwrap();
    }
}

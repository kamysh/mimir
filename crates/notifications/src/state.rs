use anyhow::{anyhow, ensure, Result};
use serde::{de::DeserializeOwned, Serialize};
use std::{
    fs::{self, File, OpenOptions},
    io::{Read, Write},
    os::{
        fd::AsRawFd,
        unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt},
    },
    path::{Component, Path, PathBuf},
};

const MAX_STATE: u64 = 1024 * 1024;
const STATE_FILE: &str = "notification-outbox.json";
const OAUTH_FILE: &str = "notification-oauth.json";

pub(crate) struct StateDir {
    path: PathBuf,
    lock: File,
}

fn verify_parents(path: &Path) -> Result<()> {
    for ancestor in path.ancestors() {
        let meta = fs::symlink_metadata(ancestor)
            .map_err(|_| anyhow!("unable to inspect notification state parent"))?;
        let mode = meta.permissions().mode();
        ensure!(
            meta.is_dir() && !meta.file_type().is_symlink(),
            "notification state parent must be a real directory"
        );
        ensure!(
            mode & 0o022 == 0 || (meta.uid() == 0 && mode & 0o1000 != 0),
            "notification state parent is writable by another user"
        );
    }
    Ok(())
}

fn ensure_dir(path: &Path) -> Result<()> {
    ensure!(
        path.is_absolute() && !path.components().any(|p| p == Component::ParentDir),
        "notification state path must be absolute without '..'"
    );
    let mut ancestors: Vec<_> = path.ancestors().collect();
    ancestors.reverse();
    for ancestor in ancestors {
        if !ancestor.exists() {
            match fs::DirBuilder::new().mode(0o700).create(ancestor) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(_) => return Err(anyhow!("unable to create notification state directory")),
            }
        }
    }
    verify_parents(path)?;
    let meta = fs::symlink_metadata(path)?;
    ensure!(
        meta.uid() == unsafe { libc::geteuid() } && meta.permissions().mode() & 0o077 == 0,
        "notification state directory must be private and user-owned"
    );
    Ok(())
}

impl StateDir {
    pub(crate) fn lock(path: &Path) -> Result<Self> {
        ensure_dir(path)?;
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(path.join("notification.lock"))?;
        let meta = lock.metadata()?;
        ensure!(
            meta.is_file()
                && meta.uid() == unsafe { libc::geteuid() }
                && meta.permissions().mode() & 0o077 == 0,
            "unsafe notification lock"
        );
        let result = unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) };
        if result != 0 {
            return Err(anyhow!("notification outbox is busy"));
        }
        Ok(Self {
            path: path.to_owned(),
            lock,
        })
    }

    pub(crate) fn read<T: DeserializeOwned>(&self) -> Result<Option<T>> {
        self.read_named(STATE_FILE)
    }

    pub(crate) fn read_oauth<T: DeserializeOwned>(&self) -> Result<Option<T>> {
        self.read_named(OAUTH_FILE)
    }

    fn read_named<T: DeserializeOwned>(&self, name: &str) -> Result<Option<T>> {
        let file = match OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(self.path.join(name))
        {
            Ok(file) => file,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error.into()),
        };
        let meta = file.metadata()?;
        ensure!(
            meta.is_file()
                && meta.uid() == unsafe { libc::geteuid() }
                && meta.permissions().mode() & 0o077 == 0
                && meta.len() <= MAX_STATE,
            "unsafe or oversized notification state"
        );
        let mut bytes = Vec::new();
        file.take(MAX_STATE + 1).read_to_end(&mut bytes)?;
        ensure!(
            bytes.len() <= MAX_STATE as usize,
            "oversized notification state"
        );
        Ok(Some(
            serde_json::from_slice(&bytes).map_err(|_| anyhow!("invalid notification state"))?,
        ))
    }

    pub(crate) fn write<T: Serialize>(&self, value: &T) -> Result<()> {
        self.write_named(STATE_FILE, value)
    }

    pub(crate) fn write_oauth<T: Serialize>(&self, value: &T) -> Result<()> {
        self.write_named(OAUTH_FILE, value)
    }

    fn write_named<T: Serialize>(&self, name: &str, value: &T) -> Result<()> {
        let bytes = serde_json::to_vec(value)?;
        ensure!(
            bytes.len() <= MAX_STATE as usize,
            "notification state is too large"
        );
        let temp = self
            .path
            .join(format!(".notification-{}.tmp", uuid::Uuid::new_v4()));
        let result = (|| -> Result<()> {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(&temp)?;
            file.write_all(&bytes)?;
            file.sync_all()?;
            fs::rename(&temp, self.path.join(name))?;
            File::open(&self.path)?.sync_all()?;
            Ok(())
        })();
        if result.is_err() {
            let _ = fs::remove_file(&temp);
        }
        result
    }
}

impl Drop for StateDir {
    fn drop(&mut self) {
        let _ = unsafe { libc::flock(self.lock.as_raw_fd(), libc::LOCK_UN) };
    }
}

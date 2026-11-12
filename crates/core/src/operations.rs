//! File-based startup compatibility and complete append-only operational logging.
//! Contracts: OperationalConfiguration, ConfigurationProtocol, OperationalLogProtocol.
use anyhow::{ensure, Context, Result};
use serde::{Deserialize, Serialize};
#[cfg(unix)]
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::{
    fs::{self, File, OpenOptions},
    io::{self, Write},
    path::{Path, PathBuf},
};

pub const CONFIG_VERSION: u32 = 1;
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Logging {
    pub directory: PathBuf,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Operations {
    pub config_version: u32,
    pub logging: Logging,
}

impl Operations {
    pub fn decode(value: &toml::Value) -> Result<Self> {
        let version = value.get("config_version").and_then(toml::Value::as_integer)
            .context("config_version is required: run `mimir config upgrade --log-directory /absolute/path/to/logs`")?;
        ensure!(version == i64::from(CONFIG_VERSION), "unsupported config_version {version}; this binary supports {CONFIG_VERSION}. Run `mimir config check`; do not downgrade a newer configuration");
        let table = value.get("logging").context("logging.directory is required: run `mimir config upgrade --log-directory /absolute/path/to/logs`")?;
        let directory = table
            .get("directory")
            .and_then(toml::Value::as_str)
            .context("logging.directory must be an absolute directory path")?;
        ensure!(
            !directory.trim().is_empty() && Path::new(directory).is_absolute(),
            "logging.directory must be a nonempty absolute path"
        );
        for retired in ["max_file_bytes", "retained_files"] {
            ensure!(table.get(retired).is_none(), "Remove logging.{retired}, or run `mimir config upgrade`: operational logs no longer have size or retention ceilings");
        }
        Ok(Self {
            config_version: CONFIG_VERSION,
            logging: Logging {
                directory: directory.into(),
            },
        })
    }
    pub fn defaults() -> Result<Self> {
        let base = std::env::var_os("XDG_STATE_HOME")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|p| PathBuf::from(p).join(".local/state")))
            .context("HOME or XDG_STATE_HOME is required to select a log directory")?;
        ensure!(base.is_absolute(), "XDG_STATE_HOME/HOME must be absolute");
        Ok(Self {
            config_version: CONFIG_VERSION,
            logging: Logging {
                directory: base.join("mimir/logs"),
            },
        })
    }
    pub fn header(&self) -> Result<String> {
        Ok(toml::to_string_pretty(self)?)
    }
}

/// Preserve comments and all unrelated tables. Reject malformed/future input
/// before writing; prepare a private owned temporary file and atomically replace.
pub fn upgrade(path: &Path, directory: Option<&Path>) -> Result<()> {
    let original = fs::read_to_string(path).context("unable to read configuration")?;
    let mut document: toml_edit::DocumentMut = original
        .parse()
        .map_err(|_| anyhow::anyhow!("invalid Mimir config TOML; no changes made"))?;
    if let Some(version) = document.get("config_version") {
        ensure!(
            version.as_integer() == Some(i64::from(CONFIG_VERSION)),
            "unsupported config_version; no changes made (automatic downgrades are forbidden)"
        );
    }
    document["config_version"] = toml_edit::value(i64::from(CONFIG_VERSION));
    if let Some(llm) = document
        .get_mut("llm")
        .and_then(toml_edit::Item::as_table_like_mut)
    {
        for retired in [
            "timeout_seconds",
            "max_calls",
            "max_output_tokens",
            "max_budget_usd",
        ] {
            llm.remove(retired);
        }
    }
    if let Some(logging) = document.get("logging") {
        ensure!(
            logging.is_table() || logging.is_inline_table(),
            "logging must be a TOML table; no changes made"
        );
    }
    if let Some(directory) = directory {
        document["logging"]["directory"] =
            toml_edit::value(directory.to_str().context("log directory must be UTF-8")?);
    }
    if let Some(logging) = document
        .get_mut("logging")
        .and_then(toml_edit::Item::as_table_like_mut)
    {
        logging.remove("max_file_bytes");
        logging.remove("retained_files");
    }
    if let Some(email) = document
        .get_mut("email")
        .and_then(toml_edit::Item::as_table_like_mut)
    {
        for retired in ["timeout_seconds", "retry_seconds", "max_attempts"] {
            email.remove(retired);
        }
    }
    if let Some(embeddings) = document
        .get_mut("embeddings")
        .and_then(toml_edit::Item::as_table_like_mut)
    {
        if embeddings
            .get("batch_size")
            .and_then(toml_edit::Item::as_integer)
            == Some(0)
        {
            embeddings.remove("batch_size");
        }
    }
    let content = document.to_string();
    let parsed: toml::Value =
        toml::from_str(&content).map_err(|_| anyhow::anyhow!("invalid upgraded config TOML"))?;
    Operations::decode(&parsed)?;
    let _: crate::config::Config = parsed
        .try_into()
        .map_err(|_| anyhow::anyhow!("invalid application configuration; no changes made"))?;
    if content == original {
        return Ok(());
    }
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let temporary = parent.join(format!(".mimir-config-{}.tmp", uuid::Uuid::new_v4()));
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    options.mode(0o600);
    let mut file = options
        .open(&temporary)
        .context("cannot create private configuration update")?;
    let mut owned = true;
    let result = (|| -> Result<()> {
        file.write_all(content.as_bytes())?;
        file.sync_all()?;
        ensure!(
            fs::read_to_string(path)? == original,
            "configuration changed during upgrade; retry after completing the other edit"
        );
        fs::rename(&temporary, path)?;
        owned = false;
        File::open(parent)?.sync_all()?;
        Ok(())
    })();
    if result.is_err() && owned {
        let _ = fs::remove_file(&temporary);
    }
    result.context("configuration upgrade failed; inspect `mimir config check` before retrying")
}

impl Logging {
    pub fn prepare(&self) -> Result<()> {
        let mut builder = fs::DirBuilder::new();
        builder.recursive(true);
        #[cfg(unix)]
        builder.mode(0o700);
        builder
            .create(&self.directory)
            .context("cannot create logging.directory")?;
        // Opening the lock verifies writability before application activity.
        self.lock()?;
        Ok(())
    }
    fn open(&self, path: &Path, append: bool) -> io::Result<File> {
        let mut options = OpenOptions::new();
        options
            .create(true)
            .write(true)
            .append(append)
            .truncate(!append);
        #[cfg(unix)]
        options.mode(0o600);
        options.open(path)
    }
    fn lock(&self) -> io::Result<File> {
        let file = self.open(&self.directory.join("mimir-log.lock"), true)?;
        file.lock()?;
        Ok(file)
    }
    pub fn write(&self, bytes: &[u8]) -> io::Result<()> {
        let _lock = self.lock()?;
        let current = self.directory.join("mimir.log");
        let mut file = self.open(&current, true)?;
        let original_length = file.metadata()?.len();
        if let Err(error) = file.write_all(bytes) {
            file.set_len(original_length).map_err(|cleanup| io::Error::other(format!("Log append failed: {error}; restoring the original log length also failed: {cleanup}")))?;
            return Err(error);
        }
        Ok(())
    }
    pub fn event(&self, component: &str, message: &str) -> Result<()> {
        self.write(
            format!(
                "{} {component}: {message}\n",
                chrono::Utc::now().to_rfc3339()
            )
            .as_bytes(),
        )?;
        Ok(())
    }
}

/// Tracing builds one complete event buffer; Drop publishes it under the same
/// process-independent lock as judge events. Never duplicate errors to stderr.
pub struct LogWriter {
    logging: Logging,
    buffer: Vec<u8>,
}
impl LogWriter {
    pub fn new(logging: Logging) -> Self {
        Self {
            logging,
            buffer: Vec::new(),
        }
    }
}
impl Write for LogWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.buffer.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        if !self.buffer.is_empty() {
            self.logging.write(&self.buffer)?;
            self.buffer.clear();
        }
        Ok(())
    }
}
impl Drop for LogWriter {
    fn drop(&mut self) {
        if let Err(error) = self.flush() {
            eprintln!("Operational logging unavailable: {error}; business operations continue");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const DB: &str = "# preserve this comment\n[database]\nhost='localhost'\nport=5432\ndbname='mimir'\nuser='mimir'\npassword='test-only-secret' # preserve this too\n";
    fn directory() -> PathBuf {
        let p = std::env::temp_dir().join(format!("mimir-operations-{}", uuid::Uuid::new_v4()));
        fs::create_dir(&p).unwrap();
        p
    }
    #[test]
    fn upgrade_preserves_settings_is_idempotent_and_refuses_future_format() {
        let dir = directory();
        let path = dir.join("config.toml");
        fs::write(&path, DB).unwrap();
        assert!(crate::config::Config::load_from_path(&path)
            .unwrap_err()
            .to_string()
            .contains("config_version"));
        upgrade(&path, Some(&dir.join("logs"))).unwrap();
        let first = fs::read_to_string(&path).unwrap();
        assert!(first.contains(DB));
        let (config, operations) = crate::config::Config::load_with_operations(&path).unwrap();
        assert_eq!(
            config.database.password.as_deref(),
            Some("test-only-secret")
        );
        assert_eq!(operations.config_version, 1);
        upgrade(&path, None).unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), first);
        let future = first.replace("config_version = 1", "config_version = 2");
        fs::write(&path, &future).unwrap();
        assert!(upgrade(&path, None).is_err());
        assert!(crate::config::Config::load_from_path(&path).is_err());
        assert_eq!(fs::read_to_string(&path).unwrap(), future);
        assert_eq!(fs::read_dir(&dir).unwrap().count(), 1);
        fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn upgrade_removes_only_retired_model_limits() {
        let dir = directory();
        let path = dir.join("config.toml");
        fs::write(&path, format!("{DB}\n[llm]\nbackend='codex'\nmodel='chosen' # keep model\nargs=['a','b']\ntimeout_seconds=300\nmax_calls=20\nmax_output_tokens=4096\nmax_budget_usd=1.0\n")).unwrap();
        upgrade(&path, Some(&dir.join("logs"))).unwrap();
        let first = fs::read_to_string(&path).unwrap();
        let value: toml::Value = toml::from_str(&first).unwrap();
        assert_eq!(value["llm"]["model"].as_str(), Some("chosen"));
        assert!(first.contains("# keep model"));
        assert!(first.contains(DB));
        assert_eq!(value["llm"]["args"].as_array().unwrap().len(), 2);
        for key in [
            "timeout_seconds",
            "max_calls",
            "max_output_tokens",
            "max_budget_usd",
        ] {
            assert!(value["llm"].get(key).is_none());
        }
        upgrade(&path, None).unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), first);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn required_directory_and_retention_bounds_are_enforced() {
        for metadata in [
            "config_version=1\n",
            "config_version=1\n[logging]\ndirectory='relative'\n",
            "config_version=1\n[logging]\ndirectory='/tmp/logs'\nretained_files=0\n",
            "config_version=1\n[logging]\ndirectory='/tmp/logs'\nmax_file_bytes=16777217\n",
        ] {
            assert!(Operations::decode(&toml::from_str::<toml::Value>(metadata).unwrap()).is_err());
        }
    }
    #[test]
    fn concurrent_repeated_errors_retain_complete_entries() {
        let dir = directory();
        let logging = Logging {
            directory: dir.clone(),
        };
        logging.prepare().unwrap();
        std::thread::scope(|scope| {
            for worker in 0..4 {
                let logging = logging.clone();
                scope.spawn(move || {
                    for n in 0..80 {
                        logging
                            .event(
                                "test",
                                &format!("worker {worker} error {n}: {}", "x".repeat(8000)),
                            )
                            .unwrap();
                    }
                });
            }
        });
        let content = fs::read_to_string(dir.join("mimir.log")).unwrap();
        assert_eq!(content.lines().count(), 320);
        for worker in 0..4 {
            for n in 0..80 {
                assert!(
                    content.contains(&format!("worker {worker} error {n}: {}", "x".repeat(8000)))
                );
            }
        }
        logging.event("test", "last error").unwrap();
        assert_eq!(fs::read_dir(&dir).unwrap().count(), 2);
        fs::remove_dir_all(dir).unwrap();
    }
}

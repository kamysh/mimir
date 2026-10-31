//! File-based startup compatibility and bounded operational logging.
//! Contracts: OperationalConfiguration, ConfigurationUpgrade, OperationalLogRetention.
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
    #[serde(default = "default_bytes")]
    pub max_file_bytes: u64,
    #[serde(default = "default_files")]
    pub retained_files: usize,
}
fn default_bytes() -> u64 {
    1_048_576
}
fn default_files() -> usize {
    4
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
            !directory.trim().is_empty()
                && directory.len() <= 4096
                && Path::new(directory).is_absolute(),
            "logging.directory must be a nonempty absolute path of at most 4096 UTF-8 bytes"
        );
        let integer = |key: &str, default: i64, min: i64, max: i64| -> Result<i64> {
            let n = match table.get(key) {
                None => default,
                Some(v) => v
                    .as_integer()
                    .with_context(|| format!("logging.{key} must be an integer"))?,
            };
            ensure!(
                (min..=max).contains(&n),
                "logging.{key} must be between {min} and {max}"
            );
            Ok(n)
        };
        Ok(Self {
            config_version: CONFIG_VERSION,
            logging: Logging {
                directory: directory.into(),
                max_file_bytes: integer("max_file_bytes", default_bytes() as i64, 4096, 16_777_216)?
                    as u64,
                retained_files: integer("retained_files", default_files() as i64, 1, 16)? as usize,
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
                max_file_bytes: default_bytes(),
                retained_files: default_files(),
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
        let limit = self.max_file_bytes;
        let bytes = &bytes[..bytes.len().min(limit as usize)];
        // Remove obsolete numbered slots when retention is reduced. These are
        // the only names owned by this logger; unrelated files remain untouched.
        for index in self.retained_files..16 {
            let path = self.directory.join(format!("mimir.log.{index}"));
            if path.exists() {
                fs::remove_file(path)?;
            }
        }
        for index in 0..self.retained_files {
            let path = if index == 0 {
                current.clone()
            } else {
                self.directory.join(format!("mimir.log.{index}"))
            };
            if let Ok(meta) = fs::metadata(&path) {
                if meta.len() > limit {
                    self.open(&path, true)?.set_len(limit)?;
                }
            }
        }
        let length = match fs::metadata(&current) {
            Ok(m) => m.len(),
            Err(e) if e.kind() == io::ErrorKind::NotFound => 0,
            Err(e) => return Err(e),
        };
        if length.saturating_add(bytes.len() as u64) > limit {
            if self.retained_files == 1 {
                self.open(&current, false)?;
            } else {
                let last = self
                    .directory
                    .join(format!("mimir.log.{}", self.retained_files - 1));
                if last.exists() {
                    fs::remove_file(last)?;
                }
                for index in (1..self.retained_files).rev() {
                    let from = if index == 1 {
                        current.clone()
                    } else {
                        self.directory.join(format!("mimir.log.{}", index - 1))
                    };
                    let to = self.directory.join(format!("mimir.log.{index}"));
                    if from.exists() {
                        fs::rename(from, to)?;
                    }
                }
            }
        }
        self.open(&current, true)?.write_all(bytes)
    }
    pub fn event(&self, component: &str, message: &str) -> Result<()> {
        let message: String = message
            .chars()
            .filter(|c| !c.is_control())
            .take(8192)
            .collect();
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

/// Tracing builds one bounded event buffer; Drop publishes it under the same
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
        let remaining = (self.logging.max_file_bytes as usize)
            .min(32768)
            .saturating_sub(self.buffer.len());
        self.buffer
            .extend_from_slice(&bytes[..bytes.len().min(remaining)]);
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
        let _ = self.flush();
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
    fn concurrent_repeated_errors_and_retention_reduction_remain_bounded() {
        let dir = directory();
        let logging = Logging {
            directory: dir.clone(),
            max_file_bytes: 4096,
            retained_files: 3,
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
        let sizes: Vec<_> = fs::read_dir(&dir)
            .unwrap()
            .map(|e| e.unwrap().metadata().unwrap().len())
            .collect();
        assert_eq!(sizes.len(), 4);
        assert!(sizes.iter().all(|n| *n <= 4096));
        assert!(sizes.iter().sum::<u64>() <= 3 * 4096);
        let reduced = Logging {
            retained_files: 1,
            ..logging
        };
        reduced.event("test", "last error").unwrap();
        assert_eq!(fs::read_dir(&dir).unwrap().count(), 2);
        fs::remove_dir_all(dir).unwrap();
    }
}

//! File-based startup compatibility and append-only operational logging.
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
        for key in ["max_file_bytes", "retained_files"] {
            ensure!(
                table.get(key).is_none(),
                "logging.{key} is retired: logs are append-only; run `mimir config upgrade` to remove retired logging settings"
            );
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
    if let Some(judge) = document
        .get_mut("judge")
        .and_then(toml_edit::Item::as_table_like_mut)
    {
        judge.remove("batch_size");
    }
    if let Some(logging) = document
        .get_mut("logging")
        .and_then(toml_edit::Item::as_table_like_mut)
    {
        for retired in ["max_file_bytes", "retained_files"] {
            logging.remove(retired);
        }
    }
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
    fn open(&self, path: &Path) -> io::Result<File> {
        let mut options = OpenOptions::new();
        options.create(true).append(true);
        #[cfg(unix)]
        options.mode(0o600);
        options.open(path)
    }
    fn lock(&self) -> io::Result<File> {
        let file = self.open(&self.directory.join("mimir-log.lock"))?;
        file.lock()?;
        Ok(file)
    }
    pub fn write(&self, bytes: &[u8]) -> io::Result<()> {
        let _lock = self.lock()?;
        self.open(&self.directory.join("mimir.log"))?
            .write_all(bytes)
    }
    pub fn event(&self, component: &str, message: &str) -> Result<()> {
        let message: String = message.chars().filter(|c| !c.is_control()).collect();
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

/// Tracing retains the complete event buffer; Drop publishes it under the same
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
    fn upgrade_removes_only_the_judges_retired_batch_count() {
        let dir = directory();
        let path = dir.join("config.toml");
        fs::write(&path, format!("config_version=1\n{DB}\n[logging]\ndirectory={}\n[embeddings]\nbackend='local'\nbatch_size=4 # preserve embedding setting\n[judge]\nbatch_size=5\nproject='user-project' # preserve scope\nmcp_args=['user-argument']\n[llm]\nbackend='command'\nmodel='chosen'\ncommand='/bin/true'\n",
            toml::Value::String(dir.join("logs").display().to_string()))).unwrap();
        upgrade(&path, None).unwrap();
        let first = fs::read_to_string(&path).unwrap();
        let value: toml::Value = toml::from_str(&first).unwrap();
        assert!(value["judge"].get("batch_size").is_none());
        assert_eq!(value["judge"]["project"].as_str(), Some("user-project"));
        assert_eq!(
            value["judge"]["mcp_args"][0].as_str(),
            Some("user-argument")
        );
        assert_eq!(value["embeddings"]["batch_size"].as_integer(), Some(4));
        assert!(first.contains("# preserve embedding setting"));
        assert!(first.contains("# preserve scope"));
        assert!(first.contains(DB));
        upgrade(&path, None).unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), first);
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
    fn required_directory_and_retired_settings_are_reported() {
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
    fn log_entries_and_tracing_buffers_keep_complete_text() {
        let dir = directory();
        let logging = Logging {
            directory: dir.clone(),
        };
        logging.prepare().unwrap();
        let message = format!("{}-repair-instruction", "資料".repeat(10_000));
        logging.event("test", &message).unwrap();
        let event = fs::read(dir.join("mimir.log")).unwrap();
        assert!(event.ends_with(format!(" test: {message}\n").as_bytes()));
        let first = format!("{}-first-end", "first".repeat(20_000));
        let second = format!("{}-second-end", "second".repeat(15_000));
        let third = b"after-flush";
        {
            let mut writer = LogWriter::new(logging.clone());
            assert_eq!(writer.write(first.as_bytes()).unwrap(), first.len());
            assert_eq!(writer.write(second.as_bytes()).unwrap(), second.len());
            writer.flush().unwrap();
            assert_eq!(writer.write(third).unwrap(), third.len());
        }
        let mut expected = event;
        expected.extend_from_slice(first.as_bytes());
        expected.extend_from_slice(second.as_bytes());
        expected.extend_from_slice(third);
        assert_eq!(fs::read(dir.join("mimir.log")).unwrap(), expected);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn concurrent_appends_preserve_every_entry_and_existing_archives() {
        let dir = directory();
        let logging = Logging {
            directory: dir.clone(),
        };
        logging.prepare().unwrap();
        let prior = format!("{}-prior-end\n", "prior".repeat(250_000));
        fs::write(dir.join("mimir.log"), &prior).unwrap();
        let archives = [
            ("mimir.log.1", b"first archive".as_slice()),
            ("mimir.log.15", b"last archive".as_slice()),
            ("unrelated", b"unrelated evidence".as_slice()),
        ];
        for (name, bytes) in archives {
            fs::write(dir.join(name), bytes).unwrap();
        }
        let entries: Vec<_> = (0..4)
            .map(|worker| format!("worker-{worker}:{}:end-{worker}\n", "資料".repeat(200_000)))
            .collect();
        std::thread::scope(|scope| {
            for entry in &entries {
                let logging = &logging;
                scope.spawn(move || logging.write(entry.as_bytes()).unwrap());
            }
        });
        let actual = fs::read(dir.join("mimir.log")).unwrap();
        assert!(actual.starts_with(prior.as_bytes()));
        let mut remaining = &actual[prior.len()..];
        let mut unseen = entries.clone();
        while !unseen.is_empty() {
            let index = unseen
                .iter()
                .position(|entry| remaining.starts_with(entry.as_bytes()))
                .expect("interleaved or missing log entry");
            let entry = unseen.remove(index);
            remaining = &remaining[entry.len()..];
        }
        assert!(remaining.is_empty());
        for (name, bytes) in archives {
            assert_eq!(fs::read(dir.join(name)).unwrap(), bytes);
        }
        assert_eq!(fs::read_dir(&dir).unwrap().count(), 5);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn retired_log_settings_require_upgrade_and_unrelated_settings_survive() {
        let dir = directory();
        let path = dir.join("config.toml");
        for settings in [
            "max_file_bytes=1048576",
            "retained_files=4",
            "max_file_bytes='wrong-type'\nretained_files=0",
        ] {
            fs::write(&path, format!("config_version=1\n{DB}\n[logging]\ndirectory={} # keep directory\n{settings}\ncustom='keep-value' # keep setting\n",
                toml::Value::String(dir.join("logs").display().to_string()))).unwrap();
            let error = crate::config::Config::load_with_operations(&path)
                .unwrap_err()
                .to_string();
            assert!(error.contains("is retired"), "{error}");
            assert!(error.contains("mimir config upgrade"), "{error}");
            upgrade(&path, None).unwrap();
            let first = fs::read_to_string(&path).unwrap();
            assert!(first.contains(DB));
            assert!(first.contains("# keep directory"));
            assert!(first.contains("custom='keep-value' # keep setting"));
            let value: toml::Value = toml::from_str(&first).unwrap();
            assert!(value["logging"].get("max_file_bytes").is_none());
            assert!(value["logging"].get("retained_files").is_none());
            assert_eq!(
                value["logging"]["directory"].as_str(),
                dir.join("logs").to_str()
            );
            crate::config::Config::load_with_operations(&path).unwrap();
            upgrade(&path, None).unwrap();
            assert_eq!(fs::read_to_string(&path).unwrap(), first);
        }
        fs::remove_dir_all(dir).unwrap();
    }
}

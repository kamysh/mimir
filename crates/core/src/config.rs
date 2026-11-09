use serde::{Deserialize, Serialize};

// ── Embedding config ───────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum EmbeddingBackend {
    Voyage,
    #[serde(rename = "openai")]
    OpenAi,
    Local,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(try_from = "EmbeddingInput")]
pub struct EmbeddingsConfig {
    pub backend: EmbeddingBackend,
    /// Used by Voyage and OpenAI backends. Ignored for local.
    #[serde(default)]
    pub model: String,
    /// Required for Voyage and OpenAI. Not needed for local.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub api_key: Option<String>,
    /// Local backend: directory to cache downloaded model files.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cache_dir: Option<String>,
}

pub(crate) const RETIRED_EMBEDDING_BATCH: &str = "embeddings.batch_size is obsolete: run `mimir config upgrade` to remove it, then `mimir config check`. Embedding processes the complete request without a grouping limit.";

#[derive(Deserialize)]
struct EmbeddingInput {
    backend: EmbeddingBackend,
    #[serde(default)]
    model: String,
    api_key: Option<String>,
    cache_dir: Option<String>,
    // Preserve acceptance of unrelated future settings, but never silently
    // reinterpret an explicitly retired setting. Values are not retained.
    #[serde(flatten)]
    extra: std::collections::BTreeMap<String, serde::de::IgnoredAny>,
}

impl TryFrom<EmbeddingInput> for EmbeddingsConfig {
    type Error = &'static str;

    fn try_from(input: EmbeddingInput) -> Result<Self, Self::Error> {
        if input.extra.contains_key("batch_size") {
            return Err(RETIRED_EMBEDDING_BATCH);
        }
        Ok(Self {
            backend: input.backend,
            model: input.model,
            api_key: input.api_key,
            cache_dir: input.cache_dir,
        })
    }
}

// ── SSL mode ───────────────────────────────────────────────────────────────

#[cfg(test)]
mod embedding_policy_tests {
    use super::*;

    #[test]
    fn retired_embedding_batch_values_are_never_silently_reinterpreted() {
        for value in [
            "0",
            "4",
            "-1",
            "false",
            "'private-retired-value'",
            "[]",
            "{}",
        ] {
            let error = toml::from_str::<EmbeddingsConfig>(&format!(
                "backend='local'\nbatch_size={value}\n"
            ))
            .unwrap_err()
            .to_string();
            assert!(error.contains(RETIRED_EMBEDDING_BATCH), "{error}");
            assert!(!error.contains("private-retired-value"), "{error}");
        }
        let error = serde_json::from_value::<EmbeddingsConfig>(serde_json::json!({
            "backend":"local", "batch_size":null
        }))
        .unwrap_err()
        .to_string();
        assert!(error.contains(RETIRED_EMBEDDING_BATCH), "{error}");
    }

    #[test]
    fn complete_input_configuration_round_trips_without_a_batch_policy() {
        let input =
            "backend='local'\ncache_dir='/fixture/cache'\nunrelated='preserved compatibility'\n";
        let config: EmbeddingsConfig = toml::from_str(input).unwrap();
        let saved = toml::to_string(&config).unwrap();
        assert!(!saved.contains("batch_size"));
        assert_eq!(toml::from_str::<EmbeddingsConfig>(&saved).unwrap(), config);
        assert_eq!(config.cache_dir.as_deref(), Some("/fixture/cache"));
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Default)]
#[serde(rename_all = "kebab-case")]
pub enum SslMode {
    Disable,
    #[default]
    Prefer,
    Require,
    VerifyCa,
    VerifyFull,
}

// ── Database config ────────────────────────────────────────────────────────

#[derive(Clone, Serialize, Deserialize, PartialEq)]
pub struct DatabaseConfig {
    // ── Required ──────────────────────────────────────────────────────────
    pub host: String,
    pub port: u16,
    pub dbname: String,
    pub user: String,
    /// Literal password; precedes PGPASSWORD and password-file lookup.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub password: Option<String>,
    /// Password file; precedes PGPASSFILE and ~/.pgpass.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pgpassfile: Option<String>,

    // ── TLS (optional) ────────────────────────────────────────────────────
    /// SSL negotiation mode. Default: prefer.
    #[serde(default)]
    pub ssl_mode: SslMode,
    /// Path to PEM-encoded CA certificate for verify-ca / verify-full.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ssl_root_cert: Option<String>,
    /// Path to PEM-encoded client certificate (mutual TLS).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ssl_client_cert: Option<String>,
    /// Path to PEM-encoded client private key (mutual TLS).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ssl_client_key: Option<String>,
}

impl std::fmt::Debug for DatabaseConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DatabaseConfig")
            .field("host", &self.host)
            .field("port", &self.port)
            .field("dbname", &self.dbname)
            .field("user", &self.user)
            .field("password", &self.password.as_ref().map(|_| "[REDACTED]"))
            .field("pgpassfile", &self.pgpassfile)
            .field("ssl_mode", &self.ssl_mode)
            .finish_non_exhaustive()
    }
}

// ── Global config ──────────────────────────────────────────────────────────

#[derive(Clone, Serialize, Deserialize)]
pub struct Config {
    pub database: DatabaseConfig,
    /// Optional — required for load_document and query_document.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub embeddings: Option<EmbeddingsConfig>,
    /// Judge-owned sections, validated by `mimir judge` rather than the belief engine.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub llm: Option<toml::Table>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub judge: Option<toml::Table>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub email: Option<toml::Table>,
    /// Optional until sweeping; no retention period is chosen by the application.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub retirement: Option<toml::Value>,
}

#[derive(Clone, Debug)]
pub struct RetirementPolicy {
    hours: f64,
    duration: chrono::Duration,
}
impl RetirementPolicy {
    pub fn grace_hours(&self) -> f64 {
        self.hours
    }
    pub(crate) fn duration(&self) -> chrono::Duration {
        self.duration
    }
}

#[derive(Debug)]
pub struct RetirementIssue(crate::interaction::NeedsInput);
impl RetirementIssue {
    pub fn correction(&self) -> &crate::interaction::NeedsInput {
        &self.0
    }
}
impl std::fmt::Display for RetirementIssue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0.issues()[0].fault().message)
    }
}
impl std::error::Error for RetirementIssue {}

#[cfg(test)]
mod retirement_tests {
    use super::*;
    fn setting(value: toml::Value) -> toml::Value {
        let mut table = toml::Table::new();
        table.insert("grace_hours".into(), value);
        toml::Value::Table(table)
    }
    #[test]
    fn missing_and_invalid_retention_never_choose_a_period() {
        let mut cases = vec![
            None,
            Some(toml::Value::String("not a table".into())),
            Some(toml::Value::Table(toml::Table::new())),
        ];
        cases.extend(
            [
                toml::Value::String("24".into()),
                toml::Value::Float(-1.0),
                toml::Value::Float(f64::NAN),
                toml::Value::Float(f64::INFINITY),
                toml::Value::Float(1e300),
            ]
            .map(|value| Some(setting(value))),
        );
        for value in cases {
            let issue = retirement_policy(value.as_ref()).unwrap_err();
            assert_eq!(
                issue.correction().issues()[0].location(),
                crate::interaction::Location::Configuration
            );
            let encoded = serde_json::to_value(issue.correction()).unwrap();
            assert_eq!(encoded["status"], "needs_input");
            assert_eq!(encoded["business_changes"], "none");
            assert!(encoded.to_string().contains("user"));
        }
    }
    #[test]
    fn only_explicit_policy_can_choose_zero_and_subminute_period_is_kept() {
        let zero = retirement_policy(Some(&setting(toml::Value::Integer(0)))).unwrap();
        assert_eq!(zero.duration(), chrono::Duration::zero());
        let precise = retirement_policy(Some(&setting(toml::Value::Float(0.000001)))).unwrap();
        assert_eq!(precise.duration().num_nanoseconds(), Some(3_600_000));
        assert_eq!(precise.grace_hours(), 0.000001);
    }
}

pub(crate) fn retirement_policy(
    raw: Option<&toml::Value>,
) -> Result<RetirementPolicy, RetirementIssue> {
    use crate::interaction::{CorrectionItem, Location, NeedsInput};
    use crate::validation::{Code, Fault, Segment};
    let issue = |code, field: Option<&str>, message: &str| {
        let mut path = vec![Segment::Key("retirement".into())];
        if let Some(field) = field {
            path.push(Segment::Key(field.into()));
        }
        RetirementIssue(NeedsInput::new(CorrectionItem::new(Location::Configuration,
            Fault{path,code,message:message.into()},
            "A user-chosen finite nonnegative retirement.grace_hours value in Mimir configuration.".into(),
            "Ask the user to choose or repair [retirement].grace_hours, then reload the client configuration. Do not send a per-call override or guess a default.".into()
        ).expect("fixed policy diagnostics contain a repair"),vec![]).expect("a policy diagnostic contains an issue"))
    };
    let Some(raw) = raw else {
        return Err(issue(Code::MissingField,Some("grace_hours"),"Sweeping is paused: the user has not configured retirement.grace_hours. No retention period was chosen."));
    };
    let table = raw.as_table().ok_or_else(|| {
        issue(
            Code::WrongType,
            None,
            "retirement must be a configuration table containing the user's grace_hours choice.",
        )
    })?;
    if let Some(unknown) = table.keys().find(|key| key.as_str() != "grace_hours") {
        return Err(issue(
            Code::UnknownField,
            Some(unknown),
            "This retirement setting is unknown; the accepted field is grace_hours.",
        ));
    }
    let hours = table.get("grace_hours").ok_or_else(|| {
        issue(
            Code::MissingField,
            Some("grace_hours"),
            "Sweeping is paused: retirement.grace_hours requires an explicit user decision.",
        )
    })?;
    let hours = hours
        .as_float()
        .or_else(|| hours.as_integer().map(|number| number as f64))
        .ok_or_else(|| {
            issue(
                Code::WrongType,
                Some("grace_hours"),
                "retirement.grace_hours must be a number chosen by the user.",
            )
        })?;
    let duration=std::time::Duration::try_from_secs_f64(hours * 3600.0)
        .ok().and_then(|value|chrono::Duration::from_std(value).ok())
        .ok_or_else(||issue(Code::InvalidNumber,Some("grace_hours"),"retirement.grace_hours must be finite, nonnegative and representable by the clock. No replacement period was chosen."))?;
    Ok(RetirementPolicy { hours, duration })
}

impl std::fmt::Debug for Config {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Config { contents: [REDACTED] }")
    }
}

/// A complete private file is linked into an absent target name. The owned
/// temporary name is never the public configuration path.
fn write_private_config(path: &std::path::Path, content: &str) -> anyhow::Result<()> {
    prepare_private_config(path, |file| {
        use std::io::Write;
        file.write_all(content.as_bytes())
    })
}

fn prepare_private_config(
    path: &std::path::Path,
    write: impl FnOnce(&mut std::fs::File) -> std::io::Result<()>,
) -> anyhow::Result<()> {
    use anyhow::Context;
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| std::path::Path::new("."));
    let mut directories = std::fs::DirBuilder::new();
    directories.recursive(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        directories.mode(0o700);
    }
    directories
        .create(parent)
        .context("unable to prepare the config directory")?;
    let temporary = parent.join(format!(
        ".mimir-config-{}-{}.tmp",
        std::process::id(),
        uuid::Uuid::new_v4()
    ));
    let mut options = std::fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options
        .open(&temporary)
        .context("unable to create a private temporary config")?;
    struct OwnedTemporary(std::path::PathBuf);
    impl Drop for OwnedTemporary {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    let owned = OwnedTemporary(temporary);
    write(&mut file)
        .context("unable to finish writing the private config; the target was not changed")?;
    file.sync_all()
        .context("unable to sync the private config; the target was not changed")?;
    // hard_link is create-if-absent on the same filesystem. Unlike rename,
    // it cannot replace an existing file, including one created during a race.
    std::fs::hard_link(&owned.0, path)?;
    std::fs::remove_file(&owned.0)
        .context("config is complete; unable to remove its owned temporary name")?;
    #[cfg(unix)]
    std::fs::File::open(parent)?.sync_all().context("config is complete but directory durability is uncertain; read it back and retry the same request")?;
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
pub enum ConfigCreation {
    Created(std::path::PathBuf),
    AlreadyConfigured(std::path::PathBuf),
}

fn matching_existing_config(
    path: &std::path::Path,
    pairs: &[(String, String)],
    requested: &Config,
) -> anyhow::Result<ConfigCreation> {
    // Validate the full installed format, but compare ONLY the explicitly
    // requested fields. Never print existing values or serialize over the file.
    let existing = Config::load_from_path(path)?;
    let current = toml::Value::try_from(&existing)?;
    let desired = toml::Value::try_from(requested)?;
    let mut conflicts = std::collections::BTreeSet::new();
    for (key, _) in pairs {
        let (section, field) = match key.as_str() {
            "backend" | "model" | "api_key" | "cache_dir" => ("embeddings", key.as_str()),
            _ => ("database", key.as_str()),
        };
        if current.get(section).and_then(|v| v.get(field))
            != desired.get(section).and_then(|v| v.get(field))
        {
            conflicts.insert(format!("{section}.{field}"));
        }
    }
    anyhow::ensure!(conflicts.is_empty(),
        "Config already exists at {} with different requested fields: {}. No settings were changed. Ask the user whether to keep the existing settings or explicitly edit these fields; do not overwrite the file or guess replacement values.",
        path.display(), conflicts.into_iter().collect::<Vec<_>>().join(", "));
    // Also finishes directory durability if a previous successful publication
    // lost its acknowledgement. File contents and permissions stay untouched.
    #[cfg(unix)]
    {
        std::fs::File::open(path)?.sync_all()?;
        let parent = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or_else(|| std::path::Path::new("."));
        std::fs::File::open(parent)?.sync_all()?;
    }
    Ok(ConfigCreation::AlreadyConfigured(path.to_owned()))
}

impl Config {
    pub fn retirement_policy(&self) -> Result<RetirementPolicy, RetirementIssue> {
        retirement_policy(self.retirement.as_ref())
    }
    pub fn config_path() -> std::path::PathBuf {
        if let Some(path) = std::env::var_os("MIMIR_CONFIG") {
            return std::path::PathBuf::from(path);
        }
        let base = std::env::var("XDG_CONFIG_HOME")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|_| {
                let home = std::env::var("HOME").unwrap_or_default();
                std::path::PathBuf::from(home).join(".config")
            });
        base.join("mimir").join("config.toml")
    }

    pub fn load() -> anyhow::Result<Self> {
        let path = Self::config_path();
        if !path.exists() {
            anyhow::bail!(
                "no config file found at {}\n\
                 Run `mimir init` to create one.",
                path.display()
            );
        }
        Self::load_from_path(&path)
    }

    /// Load an explicitly selected file without changing process-global
    /// environment. The judge uses this before spawning any MCP child.
    pub fn load_from_path(path: &std::path::Path) -> anyhow::Result<Self> {
        Self::load_with_operations(path).map(|(config, _)| config)
    }

    pub fn load_with_operations(
        path: &std::path::Path,
    ) -> anyhow::Result<(Self, crate::operations::Operations)> {
        let content = std::fs::read_to_string(path)
            .map_err(|_| anyhow::anyhow!("unable to read Mimir config at {}", path.display()))?;
        let value: toml::Value = toml::from_str(&content).map_err(|_| {
            anyhow::anyhow!("invalid Mimir config TOML (source omitted to protect credentials)")
        })?;
        let operations = crate::operations::Operations::decode(&value)?;
        anyhow::ensure!(
            value
                .get("embeddings")
                .and_then(|table| table.get("batch_size"))
                .is_none(),
            RETIRED_EMBEDDING_BATCH
        );
        let config = value
            .try_into()
            .map_err(|_| anyhow::anyhow!("invalid Mimir database/embedding configuration"))?;
        Ok((config, operations))
    }

    /// Write a template config at the default path and return the path.
    /// Fails if the file already exists.
    pub fn create_template() -> anyhow::Result<std::path::PathBuf> {
        let path = Self::config_path();
        if path.exists() {
            anyhow::bail!("config already exists at {}", path.display());
        }
        let content = crate::operations::Operations::defaults()?.header()? + CONFIG_TEMPLATE;
        write_private_config(&path, &content)?;
        Ok(path)
    }

    /// Build a config non-interactively from `KEY=VALUE` overrides on top of
    /// sane defaults (host=localhost, port=5432, dbname=mimir, user=mimir, no
    /// embeddings). An existing valid file is preserved and checked against
    /// only the requested fields; conflicts require a user decision.
    ///
    /// Recognised keys: host, port, dbname, user, password, pgpassfile, ssl_mode, ssl_root_cert,
    /// ssl_client_cert, ssl_client_key, backend, model, api_key,
    /// cache_dir. `backend`/`model`/`api_key`/`cache_dir` populate
    /// `[embeddings]`, which is included only if `backend` is given.
    pub fn create_from_kv(pairs: &[(String, String)]) -> anyhow::Result<ConfigCreation> {
        Self::create_from_kv_at(&Self::config_path(), pairs)
    }

    fn create_from_kv_at(
        path: &std::path::Path,
        pairs: &[(String, String)],
    ) -> anyhow::Result<ConfigCreation> {
        let mut database = DatabaseConfig {
            host: "localhost".to_string(),
            port: 5432,
            dbname: "mimir".to_string(),
            user: "mimir".to_string(),
            password: None,
            pgpassfile: None,
            ssl_mode: SslMode::default(),
            ssl_root_cert: None,
            ssl_client_cert: None,
            ssl_client_key: None,
        };
        let mut embeddings: Option<EmbeddingsConfig> = None;

        for (key, value) in pairs {
            match key.as_str() {
                "host" => database.host = value.clone(),
                "port" => {
                    database.port = value
                        .parse()
                        .map_err(|_| anyhow::anyhow!("invalid port: {value}"))?
                }
                "dbname" => database.dbname = value.clone(),
                "user" => database.user = value.clone(),
                "password" => database.password = Some(value.clone()),
                "pgpassfile" => database.pgpassfile = Some(value.clone()),
                "ssl_mode" => {
                    database.ssl_mode = match value.as_str() {
                        "disable" => SslMode::Disable,
                        "prefer" => SslMode::Prefer,
                        "require" => SslMode::Require,
                        "verify-ca" => SslMode::VerifyCa,
                        "verify-full" => SslMode::VerifyFull,
                        other => anyhow::bail!(
                            "invalid ssl_mode: {other} (expected disable/prefer/require/verify-ca/verify-full)"
                        ),
                    }
                }
                "ssl_root_cert" => database.ssl_root_cert = Some(value.clone()),
                "ssl_client_cert" => database.ssl_client_cert = Some(value.clone()),
                "ssl_client_key" => database.ssl_client_key = Some(value.clone()),
                "backend" => {
                    let backend = match value.as_str() {
                        "voyage" => EmbeddingBackend::Voyage,
                        "openai" => EmbeddingBackend::OpenAi,
                        "local" => EmbeddingBackend::Local,
                        other => {
                            anyhow::bail!("invalid backend: {other} (expected voyage/openai/local)")
                        }
                    };
                    let e = embeddings.get_or_insert_with(|| EmbeddingsConfig {
                        backend: EmbeddingBackend::Local,
                        model: String::new(),
                        api_key: None,
                        cache_dir: None,
                    });
                    e.backend = backend;
                }
                "model" => {
                    embeddings
                        .get_or_insert_with(|| EmbeddingsConfig {
                            backend: EmbeddingBackend::Local,
                            model: String::new(),
                            api_key: None,
                            cache_dir: None,
                        })
                        .model = value.clone();
                }
                "api_key" => {
                    embeddings
                        .get_or_insert_with(|| EmbeddingsConfig {
                            backend: EmbeddingBackend::Local,
                            model: String::new(),
                            api_key: None,
                            cache_dir: None,
                        })
                        .api_key = Some(value.clone());
                }
                "batch_size" => anyhow::bail!(RETIRED_EMBEDDING_BATCH),
                "cache_dir" => {
                    embeddings
                        .get_or_insert_with(|| EmbeddingsConfig {
                            backend: EmbeddingBackend::Local,
                            model: String::new(),
                            api_key: None,
                            cache_dir: None,
                        })
                        .cache_dir = Some(value.clone());
                }
                other => anyhow::bail!("unrecognised config key: {other}"),
            }
        }

        let config = Config {
            database,
            embeddings,
            llm: None,
            judge: None,
            email: None,
            retirement: None,
        };
        if std::fs::symlink_metadata(path).is_ok() {
            return matching_existing_config(path, pairs, &config);
        }
        let content = crate::operations::Operations::defaults()?.header()?
            + &toml::to_string_pretty(&config)?;
        match write_private_config(path, &content) {
            Ok(()) => Ok(ConfigCreation::Created(path.to_owned())),
            Err(error)
                if error
                    .downcast_ref::<std::io::Error>()
                    .is_some_and(|e| e.kind() == std::io::ErrorKind::AlreadyExists) =>
            {
                matching_existing_config(path, pairs, &config)
            }
            Err(error) => Err(error),
        }
    }
}

const CONFIG_TEMPLATE: &str = r#"# ~/.config/mimir/config.toml — mimir global configuration
#
# Generated by `mimir init`. Edit and save to activate.

[database]

# ── Required ──────────────────────────────────────────────────────────────────
# PostgreSQL server address and application database.
# Password precedence: password below, nonempty PGPASSWORD, then password file.
# File selection: pgpassfile below, PGPASSFILE, then ~/.pgpass (chmod 600).

host   = "localhost"   # hostname or IP of the PostgreSQL server
port   = 5432          # PostgreSQL port
dbname = "mimir"       # name of the mimir database (must already exist)
user   = "mimir"       # PostgreSQL role used by mimir at runtime
# password = "literal password"   # Optional; TOML string escaping applies.
# pgpassfile = "/path/to/pgpass"   # Optional explicit password file.

# ── TLS (optional) ────────────────────────────────────────────────────────────
# Controls SSL/TLS negotiation between mimir and PostgreSQL.
#
# ssl_mode values:
#   disable     — never use TLS, even if the server offers it
#   prefer      — try TLS first, fall back to plain text (default)
#   require     — require TLS, but do not verify the server certificate
#   verify-ca   — require TLS and verify the server certificate is signed
#                 by a trusted CA (system trust or ssl_root_cert)
#   verify-full — like verify-ca, and also verify the server hostname
#                 matches the certificate CN/SAN (system trust or ssl_root_cert)
#
# ssl_mode      = "prefer"
# ssl_root_cert = "/path/to/ca.crt"      # CA certificate for verify-ca / verify-full
#
# Mutual TLS — present a client certificate to the server:
# ssl_client_cert = "/path/to/client.crt"
# ssl_client_key  = "/path/to/client.key"

# ── Embeddings (required for load_document / query_document) ──────────────────
# Without this section, the document RAG tools are disabled.
#
# Three backends are available:
#
#   local  — BGE-Base-EN-v1.5 (768 dims) via fastembed + ONNX Runtime.
#            No API key required. Model (~120 MB) is downloaded from HuggingFace
#            on first use and cached locally. Fully offline after that.
#
#   voyage — Voyage AI API (1024 dims for voyage-3-lite, etc.)
#            Requires api_key from voyageai.com. Never commit this file.
#
#   openai — OpenAI Embeddings API (1536 dims for text-embedding-3-small, etc.)
#            Requires api_key from platform.openai.com. Never commit this file.
#
# All load_document calls must use the same backend/model — mixing models
# produces incorrect similarity rankings and requires a full re-index to fix.
#
# [embeddings]
# backend = "local"
#
# --- or ---
#
# [embeddings]
# backend = "voyage"
# model   = "voyage-3-lite"
# api_key = "pa-..."
#
# Optional learning runtime (see runtime/config.example.toml for email and APIs):
# [judge]
# mcp_command = "mimir-mcp"
#
# [llm]
# backend = "claude-code" # codex | command | api
# model = "YOUR_MODEL"
#
# [email]
# enabled = false
"#;

#[cfg(test)]
mod runtime_config_tests {
    use super::*;

    #[test]
    fn old_config_and_runtime_sections_round_trip_without_debug_secrets() {
        let base = "[database]\nhost='localhost'\nport=5432\ndbname='test'\nuser='test'\n";
        let old: Config = toml::from_str(base).unwrap();
        assert!(old.llm.is_none() && old.email.is_none() && old.judge.is_none());
        let text = format!("{base}\n[llm]\nbackend='api'\napi_key='secret-api'\n[email]\npassword='secret-email'\n[email.oauth]\nrefresh_token='secret-token'\n[judge]\nbatch_size=5\n");
        let cfg: Config = toml::from_str(&text).unwrap();
        assert!(!format!("{cfg:?}").contains("secret"));
        let saved = toml::to_string(&cfg).unwrap();
        let again: Config = toml::from_str(&saved).unwrap();
        assert_eq!(cfg.llm, again.llm);
        assert_eq!(cfg.email, again.email);
        assert_eq!(cfg.judge, again.judge);
    }

    #[test]
    #[cfg(unix)]
    fn config_creation_is_private_and_cannot_overwrite() {
        use std::os::unix::fs::PermissionsExt;
        let dir = std::env::temp_dir().join(format!("mimir-config-{}", uuid::Uuid::new_v4()));
        let path = dir.join("config.toml");
        write_private_config(&path, "secret").unwrap();
        assert_eq!(
            std::fs::metadata(&dir).unwrap().permissions().mode() & 0o777,
            0o700
        );
        assert_eq!(
            std::fs::metadata(&path).unwrap().permissions().mode() & 0o777,
            0o600
        );
        assert!(write_private_config(&path, "replacement").is_err());
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "secret");
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[cfg(test)]
mod complete_creation_tests {
    use super::*;
    use std::io::Write;
    fn fixture() -> std::path::PathBuf {
        std::env::temp_dir().join(format!("mimir-complete-config-{}", uuid::Uuid::new_v4()))
    }
    #[test]
    fn interrupted_write_and_a_concurrent_creator_never_expose_partial_or_replace_files(
    ) -> anyhow::Result<()> {
        let directory = fixture();
        let path = directory.join("config.toml");
        let failed = prepare_private_config(&path, |file| {
            file.write_all(b"partial secret")?;
            Err(std::io::Error::other("controlled interrupted write"))
        });
        assert!(failed.is_err());
        assert!(!path.exists());
        assert_eq!(std::fs::read_dir(&directory)?.count(), 0);
        let failed = prepare_private_config(&path, |file| {
            file.write_all(b"our complete config")?;
            std::fs::write(&path, b"another creator's config")
        });
        assert!(failed.is_err());
        assert_eq!(std::fs::read(&path)?, b"another creator's config");
        assert_eq!(std::fs::read_dir(&directory)?.count(), 1);
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }
    #[test]
    fn retries_compare_only_requested_fields_and_preserve_all_existing_bytes() -> anyhow::Result<()>
    {
        let directory = fixture();
        let path = directory.join("config.toml");
        let initial = vec![
            ("host".into(), "first-host".into()),
            ("port".into(), "5433".into()),
            ("password".into(), "secret-value".into()),
        ];
        assert_eq!(
            Config::create_from_kv_at(&path, &initial)?,
            ConfigCreation::Created(path.clone())
        );
        let mut original = std::fs::read_to_string(&path)?;
        original.push_str("\n# preserve this comment\n[email]\npassword='other-secret'\n");
        std::fs::write(&path, &original)?;
        let repeated = vec![("host".into(), "first-host".into())];
        assert_eq!(
            Config::create_from_kv_at(&path, &repeated)?,
            ConfigCreation::AlreadyConfigured(path.clone())
        );
        assert_eq!(std::fs::read_to_string(&path)?, original);
        let error = Config::create_from_kv_at(
            &path,
            &[
                ("password".into(), "different-secret".into()),
                ("host".into(), "other-host".into()),
            ],
        )
        .unwrap_err()
        .to_string();
        assert!(
            error.contains("database.password")
                && error.contains("database.host")
                && error.contains("Ask the user")
        );
        assert!(
            !error.contains("secret-value")
                && !error.contains("different-secret")
                && !error.contains("other-secret")
        );
        assert_eq!(std::fs::read_to_string(&path)?, original);
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }
    #[test]
    fn malformed_existing_files_and_invalid_requests_are_preserved() -> anyhow::Result<()> {
        let directory = fixture();
        std::fs::create_dir_all(&directory)?;
        let path = directory.join("config.toml");
        let original = "malformed='private-secret'\n[broken";
        std::fs::write(&path, original)?;
        for pairs in [
            vec![("host".into(), "localhost".into())],
            vec![("port".into(), "invalid".into())],
        ] {
            let error = Config::create_from_kv_at(&path, &pairs)
                .unwrap_err()
                .to_string();
            assert!(!error.contains("private-secret"));
            assert_eq!(std::fs::read_to_string(&path)?, original);
        }
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }
    #[test]
    #[cfg(unix)]
    fn creation_preserves_existing_parent_permissions_and_dangling_symlinks() -> anyhow::Result<()>
    {
        use std::os::unix::fs::{symlink, PermissionsExt};
        let directory = fixture();
        std::fs::create_dir_all(&directory)?;
        std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o750))?;
        let path = directory.join("config.toml");
        write_private_config(&path, "complete")?;
        assert_eq!(
            std::fs::metadata(&directory)?.permissions().mode() & 0o777,
            0o750
        );
        std::fs::remove_file(&path)?;
        symlink("missing-owned-by-someone-else", &path)?;
        assert!(write_private_config(&path, "replacement").is_err());
        assert_eq!(
            std::fs::read_link(&path)?,
            std::path::Path::new("missing-owned-by-someone-else")
        );
        assert!(!directory.join("missing-owned-by-someone-else").exists());
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }
}

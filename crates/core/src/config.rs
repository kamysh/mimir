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
pub struct EmbeddingsConfig {
    pub backend: EmbeddingBackend,
    /// Used by Voyage and OpenAI backends. Ignored for local.
    #[serde(default)]
    pub model: String,
    /// Required for Voyage and OpenAI. Not needed for local.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub api_key: Option<String>,
    /// Local backend: batch size for embedding calls (0 = no limit).
    #[serde(default)]
    pub batch_size: usize,
    /// Local backend: directory to cache downloaded model files.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cache_dir: Option<String>,
}

// ── SSL mode ───────────────────────────────────────────────────────────────

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

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct DatabaseConfig {
    // ── Required ──────────────────────────────────────────────────────────
    pub host: String,
    pub port: u16,
    pub dbname: String,
    pub user: String,

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
}

impl std::fmt::Debug for Config {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Config { contents: [REDACTED] }")
    }
}

fn write_private_config(path: &std::path::Path, content: &str) -> anyhow::Result<()> {
    use std::io::Write;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(parent, std::fs::Permissions::from_mode(0o700))?;
        }
    }
    let mut options = std::fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    options.open(path)?.write_all(content.as_bytes())?;
    Ok(())
}

impl Config {
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
        let content = std::fs::read_to_string(path)
            .map_err(|_| anyhow::anyhow!("unable to read Mimir config"))?;
        // TOML diagnostics can contain the offending source line, including secrets.
        toml::from_str(&content).map_err(|_| anyhow::anyhow!("invalid Mimir config TOML"))
    }

    /// Write a template config at the default path and return the path.
    /// Fails if the file already exists.
    pub fn create_template() -> anyhow::Result<std::path::PathBuf> {
        let path = Self::config_path();
        if path.exists() {
            anyhow::bail!("config already exists at {}", path.display());
        }
        write_private_config(&path, CONFIG_TEMPLATE)?;
        Ok(path)
    }

    /// Build a config non-interactively from `KEY=VALUE` overrides on top of
    /// sane defaults (host=localhost, port=5432, dbname=mimir, user=mimir, no
    /// embeddings), write it to the default path, and return the path. Fails
    /// if the file already exists — same safety contract as `create_template`.
    ///
    /// Recognised keys: host, port, dbname, user, ssl_mode, ssl_root_cert,
    /// ssl_client_cert, ssl_client_key, backend, model, api_key, batch_size,
    /// cache_dir. `backend`/`model`/`api_key`/`batch_size`/`cache_dir` populate
    /// `[embeddings]`, which is included only if `backend` is given.
    pub fn create_from_kv(pairs: &[(String, String)]) -> anyhow::Result<std::path::PathBuf> {
        let path = Self::config_path();
        if path.exists() {
            anyhow::bail!("config already exists at {}", path.display());
        }

        let mut database = DatabaseConfig {
            host: "localhost".to_string(),
            port: 5432,
            dbname: "mimir".to_string(),
            user: "mimir".to_string(),
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
                        batch_size: 0,
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
                            batch_size: 0,
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
                            batch_size: 0,
                            cache_dir: None,
                        })
                        .api_key = Some(value.clone());
                }
                "batch_size" => {
                    let batch_size = value
                        .parse()
                        .map_err(|_| anyhow::anyhow!("invalid batch_size: {value}"))?;
                    embeddings
                        .get_or_insert_with(|| EmbeddingsConfig {
                            backend: EmbeddingBackend::Local,
                            model: String::new(),
                            api_key: None,
                            batch_size: 0,
                            cache_dir: None,
                        })
                        .batch_size = batch_size;
                }
                "cache_dir" => {
                    embeddings
                        .get_or_insert_with(|| EmbeddingsConfig {
                            backend: EmbeddingBackend::Local,
                            model: String::new(),
                            api_key: None,
                            batch_size: 0,
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
        };
        let content = toml::to_string_pretty(&config)?;

        write_private_config(&path, &content)?;
        Ok(path)
    }
}

const CONFIG_TEMPLATE: &str = r#"# ~/.config/mimir/config.toml — mimir global configuration
#
# Generated by `mimir init`. Edit and save to activate.

[database]

# ── Required ──────────────────────────────────────────────────────────────────
# PostgreSQL server address and application database.
# mimir never stores a password. Add a ~/.pgpass entry instead:
#   HOST:PORT:DBNAME:USER:password
# The file must be chmod 600 or PostgreSQL will ignore it.

host   = "localhost"   # hostname or IP of the PostgreSQL server
port   = 5432          # PostgreSQL port
dbname = "mimir"       # name of the mimir database (must already exist)
user   = "mimir"       # PostgreSQL role used by mimir at runtime

# ── TLS (optional) ────────────────────────────────────────────────────────────
# Controls SSL/TLS negotiation between mimir and PostgreSQL.
#
# ssl_mode values:
#   disable     — never use TLS, even if the server offers it
#   prefer      — try TLS first, fall back to plain text (default)
#   require     — require TLS, but do not verify the server certificate
#   verify-ca   — require TLS and verify the server certificate is signed
#                 by a trusted CA (ssl_root_cert must be set)
#   verify-full — like verify-ca, and also verify the server hostname
#                 matches the certificate CN/SAN (ssl_root_cert must be set)
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
# batch_size = 5
# mcp_command = "mimir-mcp"
#
# [llm]
# backend = "claude-code" # codex | command | api
# model = "YOUR_MODEL"
# timeout_seconds = 300
# max_calls = 20
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

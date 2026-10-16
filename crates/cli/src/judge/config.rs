//! Typed, offline validation of the optional judge-owned TOML sections.
//! No Debug implementation is derived for structs containing credentials.
use anyhow::{anyhow, ensure, Result};
use mimir_core::config::Config;
use mimir_notifications::config::EmailConfig;
use serde::Deserialize;
use std::path::{Component, Path, PathBuf};

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum Backend {
    ClaudeCode,
    Codex,
    Command,
    Api,
}

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum Provider {
    Openai,
    Anthropic,
    Openrouter,
    Deepseek,
    Zai,
    Gemini,
    OpenaiCompatible,
}

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum ReasoningEffort {
    Minimal,
    Low,
    Medium,
    High,
    Xhigh,
}

impl ReasoningEffort {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Minimal => "minimal",
            Self::Low => "low",
            Self::Medium => "medium",
            Self::High => "high",
            Self::Xhigh => "xhigh",
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JudgeConfig {
    #[serde(default = "default_batch_size")]
    pub batch_size: usize,
    pub project: Option<String>,
    #[serde(default = "default_mcp_command")]
    pub mcp_command: String,
    #[serde(default)]
    pub mcp_args: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LlmConfig {
    pub backend: Backend,
    pub model: String,
    pub reasoning_effort: Option<ReasoningEffort>,
    #[serde(default = "default_llm_timeout")]
    pub timeout_seconds: u64,
    #[serde(default = "default_max_calls")]
    pub max_calls: usize,
    #[serde(default = "default_max_output_tokens")]
    pub max_output_tokens: usize,
    pub max_budget_usd: Option<f64>,
    pub provider: Option<Provider>,
    pub api_key: Option<String>,
    pub base_url: Option<String>,
    pub command: Option<String>,
    #[serde(default)]
    pub args: Vec<String>,
}

#[allow(dead_code)] // Parsed settings are consumed by the Step 5 runner.
pub struct RuntimeConfig {
    pub path: PathBuf,
    pub core: Config,
    pub judge: JudgeConfig,
    pub llm: LlmConfig,
    pub email: EmailConfig,
}

fn default_batch_size() -> usize {
    5
}
fn default_mcp_command() -> String {
    "mimir-mcp".into()
}
fn default_llm_timeout() -> u64 {
    300
}
fn default_max_calls() -> usize {
    20
}
fn default_max_output_tokens() -> usize {
    4096
}

pub fn resolved_path(explicit: Option<&Path>) -> Result<PathBuf> {
    let selected = explicit
        .map(Path::to_path_buf)
        .unwrap_or_else(Config::config_path);
    let absolute = if selected.is_absolute() {
        selected
    } else {
        std::env::current_dir()
            .map_err(|_| anyhow!("unable to resolve config path"))?
            .join(selected)
    };
    ensure!(
        !absolute
            .components()
            .any(|part| part == Component::ParentDir),
        "config path must not contain '..'"
    );
    Ok(absolute)
}

#[cfg(unix)]
fn validate_access_modes(
    file_mode: u32,
    file_uid: u32,
    parents: &[(u32, u32)],
    owner: u32,
) -> Result<()> {
    ensure!(file_uid == owner, "config file has another owner");
    let mut private_directory = false;
    for &(mode, uid) in parents {
        let root_sticky = uid == 0 && mode & 0o1000 != 0;
        ensure!(
            mode & 0o022 == 0 || root_sticky,
            "config parent is writable by another user"
        );
        private_directory |= uid == owner && mode & 0o077 == 0;
    }
    ensure!(
        file_mode & 0o077 == 0 || private_directory,
        "config file is accessible to others"
    );
    Ok(())
}

#[cfg(unix)]
fn validate_file_security(path: &Path) -> Result<()> {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    let mut file = None;
    let mut parents = Vec::new();
    for (index, component) in path.ancestors().enumerate() {
        let metadata = std::fs::symlink_metadata(component)
            .map_err(|_| anyhow!("unable to inspect config path"))?;
        ensure!(
            !metadata.file_type().is_symlink(),
            "config path contains a symlink"
        );
        let mode = metadata.permissions().mode();
        if index == 0 {
            ensure!(metadata.is_file(), "config must be a regular file");
            file = Some((mode, metadata.uid()));
        } else {
            ensure!(metadata.is_dir(), "config parent is not a directory");
            parents.push((mode, metadata.uid()));
        }
    }
    let (mode, uid) = file.ok_or_else(|| anyhow!("unable to inspect config path"))?;
    validate_access_modes(mode, uid, &parents, unsafe { libc::geteuid() })
}

#[cfg(not(unix))]
fn validate_file_security(_path: &Path) -> Result<()> {
    anyhow::bail!("judge config permissions require Unix")
}

fn section<T: for<'de> Deserialize<'de>>(
    table: Option<&toml::Table>,
    name: &'static str,
) -> Result<T> {
    let table = table.ok_or_else(|| anyhow!("missing [{name}] settings"))?;
    toml::Value::Table(table.clone())
        .try_into()
        .map_err(|_| anyhow!("invalid [{name}] structure"))
}

fn nonempty(value: &str, name: &'static str) -> Result<()> {
    ensure!(
        !value.trim().is_empty() && value == value.trim() && !value.chars().any(char::is_control),
        "invalid {name}"
    );
    Ok(())
}

fn arguments(args: &[String], name: &'static str) -> Result<()> {
    ensure!(args.len() <= 128, "too many {name}");
    for arg in args {
        nonempty(arg, name)?;
    }
    Ok(())
}

fn endpoint(raw: &str) -> Result<()> {
    let url = url::Url::parse(raw).map_err(|_| anyhow!("invalid llm.base_url"))?;
    let host = url
        .host_str()
        .ok_or_else(|| anyhow!("invalid llm.base_url"))?;
    let loopback = host.eq_ignore_ascii_case("localhost")
        || host
            .parse::<std::net::IpAddr>()
            .is_ok_and(|ip| ip.is_loopback());
    ensure!(
        url.scheme() == "https" || (url.scheme() == "http" && loopback),
        "llm.base_url requires HTTPS except on loopback"
    );
    ensure!(
        url.username().is_empty()
            && url.password().is_none()
            && url.query().is_none()
            && url.fragment().is_none(),
        "llm.base_url must not contain credentials, query, or fragment"
    );
    Ok(())
}

impl JudgeConfig {
    fn validate(&self) -> Result<()> {
        ensure!(
            (1..=100).contains(&self.batch_size),
            "judge.batch_size must be 1..=100"
        );
        if let Some(project) = &self.project {
            nonempty(project, "judge.project")?;
        }
        nonempty(&self.mcp_command, "judge.mcp_command")?;
        let command_path = Path::new(&self.mcp_command);
        let mut components = command_path.components();
        let plain_name =
            matches!(components.next(), Some(Component::Normal(_))) && components.next().is_none();
        ensure!(
            plain_name || (command_path.is_absolute() && command_path.file_name().is_some()),
            "judge.mcp_command must be an absolute path or command name"
        );
        arguments(&self.mcp_args, "judge.mcp_args")
    }
}

impl LlmConfig {
    fn validate(&self) -> Result<()> {
        nonempty(&self.model, "llm.model")?;
        ensure!(
            (1..=86400).contains(&self.timeout_seconds),
            "llm.timeout_seconds must be 1..=86400"
        );
        ensure!(
            (1..=10000).contains(&self.max_calls),
            "llm.max_calls must be 1..=10000"
        );
        ensure!(
            (1..=1000000).contains(&self.max_output_tokens),
            "llm.max_output_tokens must be 1..=1000000"
        );
        arguments(&self.args, "llm.args")?;
        if let Some(value) = self.max_budget_usd {
            ensure!(
                value.is_finite() && value > 0.0,
                "llm.max_budget_usd must be positive and finite"
            );
        }
        if let Some(value) = &self.base_url {
            endpoint(value)?;
        }
        ensure!(
            self.reasoning_effort.is_none() || self.backend == Backend::Codex,
            "llm.reasoning_effort is Codex only"
        );
        match self.backend {
            Backend::ClaudeCode | Backend::Codex => {
                ensure!(
                    self.provider.is_none()
                        && self.api_key.is_none()
                        && self.base_url.is_none()
                        && self.command.is_none()
                        && self.args.is_empty(),
                    "harness backend cannot use API or command settings"
                );
                ensure!(
                    self.backend == Backend::ClaudeCode || self.max_budget_usd.is_none(),
                    "llm.max_budget_usd is Claude Code only"
                );
            }
            Backend::Command => {
                let command = self
                    .command
                    .as_deref()
                    .ok_or_else(|| anyhow!("llm.command is required"))?;
                nonempty(command, "llm.command")?;
                ensure!(
                    Path::new(command).is_absolute() && Path::new(command).file_name().is_some(),
                    "llm.command must be absolute"
                );
                ensure!(
                    self.provider.is_none()
                        && self.api_key.is_none()
                        && self.base_url.is_none()
                        && self.max_budget_usd.is_none(),
                    "command backend cannot use API or budget settings"
                );
            }
            Backend::Api => {
                let provider = self
                    .provider
                    .ok_or_else(|| anyhow!("llm.provider is required"))?;
                let key = self
                    .api_key
                    .as_deref()
                    .ok_or_else(|| anyhow!("llm.api_key is required"))?;
                nonempty(key, "llm.api_key")?;
                ensure!(
                    self.command.is_none() && self.args.is_empty() && self.max_budget_usd.is_none(),
                    "API backend cannot use command or harness budget settings"
                );
                ensure!(
                    provider != Provider::OpenaiCompatible || self.base_url.is_some(),
                    "llm.base_url is required for openai-compatible"
                );
            }
        }
        Ok(())
    }
}

pub fn load(explicit: Option<&Path>) -> Result<RuntimeConfig> {
    let path = resolved_path(explicit)?;
    validate_file_security(&path)?;
    let core = Config::load_from_path(&path)?;
    let judge: JudgeConfig = section(core.judge.as_ref(), "judge")?;
    let llm: LlmConfig = section(core.llm.as_ref(), "llm")?;
    let email: EmailConfig = match core.email.as_ref() {
        Some(table) => section(Some(table), "email")?,
        None => EmailConfig::default(),
    };
    judge.validate()?;
    llm.validate()?;
    email.validate()?;
    Ok(RuntimeConfig {
        path,
        core,
        judge,
        llm,
        email,
    })
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::{symlink, PermissionsExt};

    const DATABASE: &str =
        "[database]\nhost='localhost'\nport=5432\ndbname='mimir'\nuser='mimir'\n";
    const HARNESS: &str =
        "[judge]\nbatch_size=5\n[llm]\nbackend='claude-code'\nmodel='test-model'\n";

    struct Fixture(PathBuf);
    impl Fixture {
        fn new(mode: u32) -> Self {
            let base = Path::new("/var/tmp/mimir/step4");
            std::fs::create_dir_all(base).unwrap();
            let path = base.join(format!("fixture-{}", uuid::Uuid::new_v4()));
            std::fs::create_dir(&path).unwrap();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(mode)).unwrap();
            Self(path)
        }
        fn config(&self, text: &str, mode: u32) -> PathBuf {
            let path = self.0.join("config.toml");
            std::fs::write(&path, text).unwrap();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(mode)).unwrap();
            path
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    fn valid(text: &str) -> bool {
        let fixture = Fixture::new(0o700);
        load(Some(&fixture.config(text, 0o600))).is_ok()
    }

    #[test]
    fn old_config_still_parses_without_runtime_sections() {
        let old: Config = toml::from_str(DATABASE).unwrap();
        assert!(old.judge.is_none() && old.llm.is_none() && old.email.is_none());
        assert!(valid(&format!(
            "{DATABASE}{HARNESS}[email]\nenabled=false\npassword='PLACEHOLDER'\n"
        )));
    }

    #[test]
    fn api_provider_and_endpoint_matrix() {
        for provider in [
            "openai",
            "anthropic",
            "openrouter",
            "deepseek",
            "zai",
            "gemini",
        ] {
            assert!(valid(&format!("{DATABASE}[judge]\n[llm]\nbackend='api'\nprovider='{provider}'\nmodel='chosen-model'\napi_key='private-key'\n")), "{provider}");
        }
        assert!(valid(&format!("{DATABASE}[judge]\n[llm]\nbackend='api'\nprovider='openai-compatible'\nmodel='chosen-model'\napi_key='private-key'\nbase_url='http://127.0.0.1:8080/v1'\n")));
        assert!(!valid(&format!("{DATABASE}[judge]\n[llm]\nbackend='api'\nprovider='openai-compatible'\nmodel='chosen-model'\napi_key='private-key'\n")));
        assert!(!valid(&format!("{DATABASE}[judge]\n[llm]\nbackend='api'\nprovider='openai'\nmodel='chosen-model'\napi_key='private-key'\nbase_url='http://example.com/v1'\n")));
    }

    #[test]
    fn command_and_budget_combinations() {
        assert!(valid(&format!("{DATABASE}[judge]\n[llm]\nbackend='command'\nmodel='chosen-model'\ncommand='/usr/bin/adapter'\nargs=['--json']\n")));
        assert!(!valid(&format!("{DATABASE}[judge]\n[llm]\nbackend='command'\nmodel='chosen-model'\ncommand='relative/adapter'\n")));
        assert!(!valid(&format!("{DATABASE}[judge]\nmcp_command='.'\n[llm]\nbackend='claude-code'\nmodel='chosen-model'\n")));
        assert!(!valid(&format!(
            "{DATABASE}[judge]\n[llm]\nbackend='codex'\nmodel='chosen-model'\nmax_budget_usd=1.0\n"
        )));
        assert!(!valid(&format!(
            "{DATABASE}[judge]\n[llm]\nbackend='claude-code'\nmodel='chosen-model'\nmax_calls=0\n"
        )));
        assert!(!valid(&format!("{DATABASE}[judge]\n[llm]\nbackend='command'\nmodel='chosen-model'\ncommand='/usr/bin/adapter'\nargs=['']\n")));
    }

    #[test]
    fn codex_model_and_effort_are_explicit_and_validated() {
        for effort in ["minimal", "low", "medium", "high", "xhigh"] {
            assert!(valid(&format!(
                "{DATABASE}[judge]\n[llm]\nbackend='codex'\nmodel='gpt-6.1-sol'\nreasoning_effort='{effort}'\n"
            )));
        }
        assert!(valid(&format!(
            "{DATABASE}[judge]\n[llm]\nbackend='codex'\nmodel='gpt-6.1-sol'\n"
        )));
        assert!(!valid(&format!(
            "{DATABASE}[judge]\n[llm]\nbackend='codex'\nmodel='gpt-6.1-sol'\nreasoning_effort='invalid'\n"
        )));
        assert!(!valid(&format!(
            "{DATABASE}[judge]\n[llm]\nbackend='claude-code'\nmodel='chosen-model'\nreasoning_effort='high'\n"
        )));
    }

    #[test]
    fn email_password_google_and_microsoft_oauth() {
        let common = format!("{DATABASE}{HARNESS}[email]\nenabled=true\nhost='smtp.example.com'\nport=587\ntls='starttls'\nfrom='a@example.com'\nto=['b@example.com']\nusername='a@example.com'\n");
        assert!(valid(&format!(
            "{common}auth='password'\npassword='private'\n"
        )));
        assert!(valid(&format!("{common}auth='oauth2'\n[email.oauth]\nprovider='google'\nclient_id='client'\nrefresh_token='token'\n")));
        assert!(valid(&format!("{common}auth='oauth2'\n[email.oauth]\nprovider='microsoft'\nclient_id='client'\nrefresh_token='token'\ntenant='common'\nscope='https://outlook.office.com/SMTP.Send offline_access'\n")));
        assert!(!valid(&format!("{common}auth='oauth2'\n[email.oauth]\nprovider='microsoft'\nclient_id='client'\nrefresh_token='token'\ntenant='common'\nscope='SMTP.Send offline_access'\n")));
        assert!(!valid(&format!("{common}auth='oauth2'\npassword='bad'\n[email.oauth]\nprovider='google'\nclient_id='client'\nrefresh_token='token'\n")));
    }

    #[test]
    fn unknown_fields_and_malformed_toml_hide_secrets() {
        let fixture = Fixture::new(0o700);
        let unknown = fixture.config(
            &format!("{DATABASE}{HARNESS}unknown='VERY_PRIVATE_VALUE'\n"),
            0o600,
        );
        let error = load(Some(&unknown)).err().unwrap().to_string();
        assert!(error.contains("[llm]"));
        assert!(!error.contains("VERY_PRIVATE_VALUE"));
        let malformed = fixture.config(
            &format!("{DATABASE}{HARNESS}api_key='VERY_PRIVATE_VALUE\n"),
            0o600,
        );
        let error = load(Some(&malformed)).err().unwrap().to_string();
        assert!(!error.contains("VERY_PRIVATE_VALUE"));
    }

    #[test]
    fn permission_alternatives_and_symlink_policy() {
        let private_dir = Fixture::new(0o700);
        assert!(load(Some(
            &private_dir.config(&format!("{DATABASE}{HARNESS}"), 0o644)
        ))
        .is_ok());
        let public_dir = Fixture::new(0o755);
        let path = public_dir.config(&format!("{DATABASE}{HARNESS}"), 0o600);
        assert!(load(Some(&path)).is_ok());
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).unwrap();
        assert!(
            load(Some(&path)).is_ok(),
            "private ancestor protects this file"
        );
        let owner = unsafe { libc::geteuid() };
        assert!(validate_access_modes(0o600, owner, &[(0o755, owner)], owner).is_ok());
        assert!(validate_access_modes(0o644, owner, &[(0o700, owner)], owner).is_ok());
        assert!(validate_access_modes(0o644, owner, &[(0o755, owner)], owner).is_err());
        assert!(validate_access_modes(0o600, owner, &[(0o777, owner)], owner).is_err());
        let link = public_dir.0.join("link.toml");
        symlink(&path, &link).unwrap();
        assert!(load(Some(&link)).is_err());
        let directory_link = private_dir.0.join("linked-directory");
        symlink(&public_dir.0, &directory_link).unwrap();
        assert!(load(Some(&directory_link.join("config.toml"))).is_err());
    }
}

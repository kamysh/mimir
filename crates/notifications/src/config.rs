use anyhow::{anyhow, ensure, Result};
use serde::Deserialize;

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Tls {
    Starttls,
    Tls,
}

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Auth {
    Password,
    Oauth2,
    None,
}

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum OAuthProvider {
    Google,
    Microsoft,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OAuthConfig {
    pub provider: OAuthProvider,
    pub client_id: String,
    pub client_secret: Option<String>,
    pub refresh_token: String,
    pub tenant: Option<String>,
    pub scope: Option<String>,
}

#[derive(Deserialize, Default)]
#[serde(deny_unknown_fields)]
pub struct EmailConfig {
    #[serde(default)]
    pub enabled: bool,
    pub host: Option<String>,
    pub port: Option<u16>,
    pub tls: Option<Tls>,
    #[serde(rename = "from")]
    pub from_address: Option<String>,
    #[serde(default)]
    pub to: Vec<String>,
    pub username: Option<String>,
    pub auth: Option<Auth>,
    pub password: Option<String>,
    pub oauth: Option<OAuthConfig>,
    #[serde(default = "default_timeout")]
    pub timeout_seconds: u64,
    #[serde(default = "default_retry")]
    pub retry_seconds: u64,
    #[serde(default = "default_attempts")]
    pub max_attempts: usize,
}

fn default_timeout() -> u64 {
    15
}
fn default_retry() -> u64 {
    300
}
fn default_attempts() -> usize {
    5
}

fn nonempty(value: &str, name: &'static str) -> Result<()> {
    ensure!(
        !value.trim().is_empty() && value == value.trim() && !value.chars().any(char::is_control),
        "invalid {name}"
    );
    Ok(())
}

fn address(value: &str) -> bool {
    let Some((local, domain)) = value.split_once('@') else {
        return false;
    };
    !local.is_empty()
        && !domain.is_empty()
        && !domain.contains('@')
        && !value.chars().any(|c| c.is_whitespace() || c.is_control())
}

impl EmailConfig {
    pub fn validate(&self) -> Result<()> {
        if !self.enabled {
            return Ok(());
        }
        let host = self
            .host
            .as_deref()
            .ok_or_else(|| anyhow!("email.host is required"))?;
        nonempty(host, "email.host")?;
        ensure!(
            !host.contains('/') && !host.contains(':'),
            "invalid email.host"
        );
        ensure!(self.port.is_some_and(|n| n > 0), "email.port is required");
        ensure!(self.tls.is_some(), "email.tls is required");
        let from = self
            .from_address
            .as_deref()
            .ok_or_else(|| anyhow!("email.from is required"))?;
        ensure!(address(from), "invalid email.from");
        ensure!(
            !self.to.is_empty() && self.to.iter().all(|s| address(s)),
            "invalid email.to"
        );
        ensure!(
            (1..=300).contains(&self.timeout_seconds),
            "email.timeout_seconds must be 1..=300"
        );
        ensure!(
            (1..=86400).contains(&self.retry_seconds),
            "email.retry_seconds must be 1..=86400"
        );
        ensure!(
            (1..=100).contains(&self.max_attempts),
            "email.max_attempts must be 1..=100"
        );
        match self.auth.ok_or_else(|| anyhow!("email.auth is required"))? {
            Auth::Password => {
                nonempty(
                    self.username
                        .as_deref()
                        .ok_or_else(|| anyhow!("email.username is required"))?,
                    "email.username",
                )?;
                nonempty(
                    self.password
                        .as_deref()
                        .ok_or_else(|| anyhow!("email.password is required"))?,
                    "email.password",
                )?;
                ensure!(
                    self.oauth.is_none(),
                    "email.oauth conflicts with password auth"
                );
            }
            Auth::Oauth2 => {
                nonempty(
                    self.username
                        .as_deref()
                        .ok_or_else(|| anyhow!("email.username is required"))?,
                    "email.username",
                )?;
                ensure!(
                    self.password.is_none(),
                    "email.password conflicts with OAuth2"
                );
                let oauth = self
                    .oauth
                    .as_ref()
                    .ok_or_else(|| anyhow!("email.oauth is required"))?;
                nonempty(&oauth.client_id, "email.oauth.client_id")?;
                nonempty(&oauth.refresh_token, "email.oauth.refresh_token")?;
                ensure!(
                    oauth.client_id.len() <= 1024 && oauth.refresh_token.len() <= 8192,
                    "email.oauth credential is too long"
                );
                if let Some(secret) = &oauth.client_secret {
                    nonempty(secret, "email.oauth.client_secret")?;
                    ensure!(
                        secret.len() <= 8192,
                        "email.oauth.client_secret is too long"
                    );
                }
                match oauth.provider {
                    OAuthProvider::Google => {
                        ensure!(
                            oauth.tenant.is_none(),
                            "email.oauth.tenant is Microsoft only"
                        );
                        ensure!(
                            oauth
                                .scope
                                .as_deref()
                                .is_none_or(|scope| scope == "https://mail.google.com/"),
                            "email.oauth.scope must be the Gmail SMTP scope"
                        );
                    }
                    OAuthProvider::Microsoft => {
                        let tenant = oauth
                            .tenant
                            .as_deref()
                            .ok_or_else(|| anyhow!("email.oauth.tenant is required"))?;
                        ensure!(
                            !tenant.is_empty()
                                && tenant.len() <= 253
                                && !tenant.contains("..")
                                && tenant.bytes().all(|byte| byte.is_ascii_alphanumeric()
                                    || matches!(byte, b'-' | b'.')),
                            "invalid email.oauth.tenant"
                        );
                        let scope = oauth
                            .scope
                            .as_deref()
                            .ok_or_else(|| anyhow!("email.oauth.scope is required"))?;
                        let scopes: Vec<_> = scope.split_whitespace().collect();
                        ensure!(
                            scopes.contains(&"https://outlook.office.com/SMTP.Send")
                                && scopes.contains(&"offline_access"),
                            "email.oauth.scope requires SMTP.Send and offline_access"
                        );
                    }
                }
            }
            Auth::None => ensure!(
                self.username.is_none() && self.password.is_none() && self.oauth.is_none(),
                "unauthenticated email cannot have credential settings"
            ),
        }
        Ok(())
    }
}

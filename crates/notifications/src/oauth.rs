//! OAuth refresh for SMTP. Token endpoints are fixed by provider in production;
//! loopback overrides exist only inside local tests.
use crate::{
    config::{EmailConfig, OAuthProvider},
    state::StateDir,
};
use reqwest::{redirect::Policy, Client};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const MAX_REPLY: usize = 16 * 1024;
const MAX_TOKEN: usize = 8192;
const EXPIRY_MARGIN: u64 = 60;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AuthError {
    Retryable,
    NeedsAttention,
    Storage,
}

pub(crate) struct AccessToken {
    pub value: String,
    pub cached: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct TokenCache {
    schema_version: u32,
    identity_hash: Vec<u8>,
    refresh_token: String,
    access_token: Option<String>,
    expires_at: u64,
}

#[derive(Deserialize)]
struct RefreshReply {
    access_token: String,
    token_type: String,
    expires_in: u64,
    refresh_token: Option<String>,
}

fn valid_token(token: &str) -> bool {
    !token.is_empty() && token.len() <= MAX_TOKEN && !token.chars().any(char::is_control)
}

fn identity(config: &EmailConfig) -> Result<Vec<u8>, AuthError> {
    let oauth = config.oauth.as_ref().ok_or(AuthError::NeedsAttention)?;
    let provider = match oauth.provider {
        OAuthProvider::Google => "google",
        OAuthProvider::Microsoft => "microsoft",
    };
    let material = serde_json::to_vec(&(
        provider,
        config.host.as_deref(),
        config.username.as_deref(),
        &oauth.client_id,
        oauth.client_secret.as_deref(),
        oauth.tenant.as_deref(),
        oauth.scope.as_deref(),
        &oauth.refresh_token,
    ))
    .map_err(|_| AuthError::NeedsAttention)?;
    Ok(Sha256::digest(material).to_vec())
}

fn endpoint(config: &EmailConfig) -> Result<String, AuthError> {
    let oauth = config.oauth.as_ref().ok_or(AuthError::NeedsAttention)?;
    match oauth.provider {
        OAuthProvider::Google => Ok("https://oauth2.googleapis.com/token".into()),
        OAuthProvider::Microsoft => Ok(format!(
            "https://login.microsoftonline.com/{}/oauth2/v2.0/token",
            oauth.tenant.as_deref().ok_or(AuthError::NeedsAttention)?
        )),
    }
}

async fn refresh(
    config: &EmailConfig,
    refresh_token: &str,
    url: &str,
) -> Result<RefreshReply, AuthError> {
    let oauth = config.oauth.as_ref().ok_or(AuthError::NeedsAttention)?;
    let client = Client::builder()
        .timeout(std::time::Duration::from_secs(config.timeout_seconds))
        .redirect(Policy::none())
        .build()
        .map_err(|_| AuthError::Retryable)?;
    let mut form = vec![
        ("grant_type", "refresh_token"),
        ("refresh_token", refresh_token),
        ("client_id", oauth.client_id.as_str()),
    ];
    if let Some(secret) = &oauth.client_secret {
        form.push(("client_secret", secret));
    }
    if oauth.provider == OAuthProvider::Microsoft {
        form.push((
            "scope",
            oauth.scope.as_deref().ok_or(AuthError::NeedsAttention)?,
        ));
    }
    let mut response = client
        .post(url)
        .form(&form)
        .send()
        .await
        .map_err(|_| AuthError::Retryable)?;
    let status = response.status();
    if !status.is_success() {
        return Err(if status.is_client_error() || status.is_redirection() {
            AuthError::NeedsAttention
        } else {
            AuthError::Retryable
        });
    }
    if response
        .content_length()
        .is_some_and(|size| size > MAX_REPLY as u64)
    {
        return Err(AuthError::NeedsAttention);
    }
    let mut bytes = Vec::new();
    while let Some(chunk) = response.chunk().await.map_err(|_| AuthError::Retryable)? {
        if bytes.len().saturating_add(chunk.len()) > MAX_REPLY {
            return Err(AuthError::NeedsAttention);
        }
        bytes.extend_from_slice(&chunk);
    }
    let reply: RefreshReply =
        serde_json::from_slice(&bytes).map_err(|_| AuthError::NeedsAttention)?;
    if !reply.token_type.eq_ignore_ascii_case("bearer")
        || !valid_token(&reply.access_token)
        || reply.expires_in == 0
        || reply
            .refresh_token
            .as_deref()
            .is_some_and(|token| !valid_token(token))
    {
        return Err(AuthError::NeedsAttention);
    }
    Ok(reply)
}

pub(crate) async fn access_token(
    config: &EmailConfig,
    state: &StateDir,
    now: u64,
    force_refresh: bool,
    endpoint_override: Option<&str>,
) -> Result<AccessToken, AuthError> {
    let id = identity(config)?;
    let oauth = config.oauth.as_ref().ok_or(AuthError::NeedsAttention)?;
    let previous: Option<TokenCache> = state.read_oauth().map_err(|_| AuthError::Storage)?;
    if let Some(cache) = &previous {
        if cache.schema_version != 1 || cache.identity_hash != id {
            return Err(AuthError::NeedsAttention);
        }
        if !valid_token(&cache.refresh_token)
            || cache
                .access_token
                .as_deref()
                .is_some_and(|token| !valid_token(token))
        {
            return Err(AuthError::NeedsAttention);
        }
        if !force_refresh && cache.expires_at > now.saturating_add(EXPIRY_MARGIN) {
            if let Some(access) = &cache.access_token {
                return Ok(AccessToken {
                    value: access.clone(),
                    cached: true,
                });
            }
        }
    }
    let current_refresh = previous
        .as_ref()
        .map_or(oauth.refresh_token.as_str(), |cache| &cache.refresh_token);
    let url = match endpoint_override {
        Some(url) => url.to_owned(),
        None => endpoint(config)?,
    };
    let reply = refresh(config, current_refresh, &url).await?;
    let cache = TokenCache {
        schema_version: 1,
        identity_hash: id,
        refresh_token: reply
            .refresh_token
            .unwrap_or_else(|| current_refresh.to_owned()),
        access_token: Some(reply.access_token.clone()),
        expires_at: now.saturating_add(reply.expires_in),
    };
    // The new refresh token must be durable before SMTP can use the access token.
    state.write_oauth(&cache).map_err(|_| AuthError::Storage)?;
    Ok(AccessToken {
        value: reply.access_token,
        cached: false,
    })
}

pub(crate) fn invalidate_access(config: &EmailConfig, state: &StateDir) -> Result<(), AuthError> {
    let id = identity(config)?;
    let Some(mut cache): Option<TokenCache> = state.read_oauth().map_err(|_| AuthError::Storage)?
    else {
        return Err(AuthError::NeedsAttention);
    };
    if cache.schema_version != 1 || cache.identity_hash != id {
        return Err(AuthError::NeedsAttention);
    }
    cache.access_token = None;
    cache.expires_at = 0;
    state.write_oauth(&cache).map_err(|_| AuthError::Storage)
}

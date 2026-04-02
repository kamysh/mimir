use anyhow::Result;
use sqlx::{
    postgres::{PgConnectOptions, PgPoolOptions, PgSslMode},
    PgPool,
};
use std::str::FromStr;

use crate::config::{DatabaseConfig, SslMode};

// public first: unqualified CREATE TABLE → public, not ag_catalog.
// ag_catalog second: AGE operators resolve correctly.
const SEARCH_PATH: &str = "public,ag_catalog";

/// Build a postgres:// URL from config fields with all components properly
/// percent-encoded.  The URL contains no password so that sqlx applies
/// ~/.pgpass lookup after the final host/port/user/database values are set —
/// the same behaviour as psql.  Using PgConnectOptions::new() + builder is
/// intentionally avoided: new() runs apply_pgpass() at construction time with
/// OS-default values before any builder fields are applied.
fn pg_url(cfg: &DatabaseConfig) -> Result<String> {
    let mut url = url::Url::parse("postgres://placeholder/placeholder")
        .expect("static URL is valid");
    url.set_username(&cfg.user)
        .map_err(|()| anyhow::anyhow!("invalid postgres username: {:?}", cfg.user))?;
    url.set_host(Some(&cfg.host))
        .map_err(|e| anyhow::anyhow!("invalid postgres host {:?}: {e}", cfg.host))?;
    url.set_port(Some(cfg.port))
        .map_err(|()| anyhow::anyhow!("invalid postgres port: {}", cfg.port))?;
    url.path_segments_mut()
        .map_err(|()| anyhow::anyhow!("cannot build URL path"))?
        .clear()
        .push(&cfg.dbname);
    Ok(url.to_string())
}

pub async fn connect(cfg: &DatabaseConfig) -> Result<PgPool> {
    let ssl_mode = match cfg.ssl_mode {
        SslMode::Disable    => PgSslMode::Disable,
        SslMode::Allow      => PgSslMode::Allow,
        SslMode::Prefer     => PgSslMode::Prefer,
        SslMode::Require    => PgSslMode::Require,
        SslMode::VerifyCa   => PgSslMode::VerifyCa,
        SslMode::VerifyFull => PgSslMode::VerifyFull,
    };

    let statement_cache = if cfg.pgbouncer { 0 } else { 1024 };

    let mut opts = PgConnectOptions::from_str(&pg_url(cfg)?)?
        .ssl_mode(ssl_mode)
        .statement_cache_capacity(statement_cache)
        .options([("search_path", SEARCH_PATH)]);

    if let Some(ref path) = cfg.ssl_root_cert {
        opts = opts.ssl_root_cert(path);
    }
    if let Some(ref path) = cfg.ssl_client_cert {
        opts = opts.ssl_client_cert(path);
    }
    if let Some(ref path) = cfg.ssl_client_key {
        opts = opts.ssl_client_key(path);
    }

    let pool = PgPoolOptions::new()
        .max_connections(cfg.max_connections)
        .connect_with(opts)
        .await?;
    Ok(pool)
}
use anyhow::Result;
use sqlx::{
    postgres::{PgConnectOptions, PgPoolOptions, PgSslMode},
    PgPool,
};

use crate::config::{DatabaseConfig, SslMode};

// public first: unqualified CREATE TABLE → public, not ag_catalog.
// ag_catalog second: AGE operators resolve correctly.
const SEARCH_PATH: &str = "public,ag_catalog";

fn apply_search_path(opts: PgConnectOptions) -> PgConnectOptions {
    opts.options([("search_path", SEARCH_PATH)])
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

    // statement_cache_capacity = 0 disables prepared statements, which is
    // required for PgBouncer transaction pooling mode.
    let statement_cache = if cfg.pgbouncer { 0 } else { 1024 };

    let mut opts = PgConnectOptions::new()
        .host(&cfg.host)
        .port(cfg.port)
        .database(&cfg.dbname)
        .username(&cfg.user)
        .ssl_mode(ssl_mode)
        .statement_cache_capacity(statement_cache);

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
        .connect_with(apply_search_path(opts))
        .await?;
    Ok(pool)
}
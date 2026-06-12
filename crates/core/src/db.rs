use anyhow::Result;
use deadpool_postgres::Pool;
use postgres_native_tls::MakeTlsConnector;
use sqlx::postgres::{PgConnectOptions, PgPoolOptions, PgSslMode};
use std::str::FromStr;

use crate::config::{DatabaseConfig, SslMode};

const SEARCH_PATH: &str = "public,ag_catalog";

/// Read password from ~/.pgpass for (host, port, dbname, user).
/// Format per line: hostname:port:database:username:password  ('*' wildcard allowed)
fn pgpass_lookup(host: &str, port: u16, dbname: &str, user: &str) -> Option<String> {
    let home = std::env::var("HOME").ok()?;
    let path = std::path::Path::new(&home).join(".pgpass");
    let content = std::fs::read_to_string(path).ok()?;
    let port_s = port.to_string();
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = line.splitn(5, ':').collect();
        if parts.len() != 5 {
            continue;
        }
        let m = |pat: &str, val: &str| pat == "*" || pat == val;
        if m(parts[0], host) && m(parts[1], &port_s) && m(parts[2], dbname) && m(parts[3], user) {
            return Some(parts[4].to_owned());
        }
    }
    None
}

/// Build a postgres:// URL from config fields with all components properly
/// percent-encoded. The URL contains no password so that sqlx / tokio-postgres
/// applies ~/.pgpass lookup — the same behaviour as psql.
fn pg_url(cfg: &DatabaseConfig) -> Result<String> {
    let mut url =
        url::Url::parse("postgres://placeholder/placeholder").expect("static URL is valid");
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

/// Run sqlx migrations against the database. Called once at startup before
/// handing the connection off to the tokio-postgres pool.
pub async fn migrate(cfg: &DatabaseConfig) -> Result<()> {
    let ssl_mode = match cfg.ssl_mode {
        SslMode::Disable => PgSslMode::Disable,
        SslMode::Allow => PgSslMode::Allow,
        SslMode::Prefer => PgSslMode::Prefer,
        SslMode::Require => PgSslMode::Require,
        SslMode::VerifyCa => PgSslMode::VerifyCa,
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
        .max_connections(1)
        .connect_with(opts)
        .await?;
    sqlx::migrate!().run(&pool).await?;
    Ok(())
}

/// Build a tokio-postgres connection pool via deadpool-postgres.
/// search_path is set on every new connection via connection options.
pub async fn connect_pool(cfg: &DatabaseConfig) -> Result<Pool> {
    let mut pg_cfg = tokio_postgres::Config::new();
    pg_cfg.host(&cfg.host);
    pg_cfg.port(cfg.port);
    pg_cfg.dbname(&cfg.dbname);
    pg_cfg.user(&cfg.user);
    pg_cfg.options(&format!("-c search_path={SEARCH_PATH}"));
    if let Some(pw) = pgpass_lookup(&cfg.host, cfg.port, &cfg.dbname, &cfg.user) {
        pg_cfg.password(pw);
    }

    // Build TLS connector. For Disable we use NoTls; otherwise native-tls.
    let pool = match cfg.ssl_mode {
        SslMode::Disable => {
            let mgr = deadpool_postgres::Manager::new(pg_cfg, tokio_postgres::NoTls);
            Pool::builder(mgr)
                .max_size(cfg.max_connections as usize)
                .build()?
        }
        _ => {
            let mut tls_builder = native_tls::TlsConnector::builder();
            match cfg.ssl_mode {
                SslMode::Require | SslMode::Allow | SslMode::Prefer => {
                    tls_builder.danger_accept_invalid_certs(false);
                }
                SslMode::VerifyCa | SslMode::VerifyFull => {
                    if let Some(ref path) = cfg.ssl_root_cert {
                        let pem = std::fs::read(path)?;
                        let cert = native_tls::Certificate::from_pem(&pem)?;
                        tls_builder.add_root_certificate(cert);
                    }
                }
                SslMode::Disable => unreachable!(),
            }
            if let Some(ref cert_path) = cfg.ssl_client_cert {
                if let Some(ref key_path) = cfg.ssl_client_key {
                    let cert_pem = std::fs::read(cert_path)?;
                    let key_pem = std::fs::read(key_path)?;
                    // Build PKCS#8 identity from cert + key PEM.
                    let identity =
                        native_tls::Identity::from_pkcs8(&cert_pem, &key_pem)?;
                    tls_builder.identity(identity);
                }
            }
            let connector = MakeTlsConnector::new(tls_builder.build()?);
            let mgr = deadpool_postgres::Manager::new(pg_cfg, connector);
            Pool::builder(mgr)
                .max_size(cfg.max_connections as usize)
                .build()?
        }
    };

    // Eagerly verify connectivity.
    let _ = pool.get().await?;
    Ok(pool)
}

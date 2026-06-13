use anyhow::Result;
use postgres_native_tls::MakeTlsConnector;
use std::path::PathBuf;
use tokio_postgres::Client;

use crate::config::{DatabaseConfig, SslMode};

const SEARCH_PATH: &str = "public,ag_catalog";

/// Read password from ~/.pgpass for (host, port, dbname, user).
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

/// Run kryzhen migrations against the database. Called once at startup.
pub async fn migrate(cfg: &DatabaseConfig) -> Result<()> {
    let migrations_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("migrations");
    let migrations = kryzhen::file::load_dir(&migrations_dir)?;
    let mut client = connect(cfg).await?;
    kryzhen::migrate(&mut client, &migrations, false).await?;
    Ok(())
}

/// Open a single tokio-postgres connection.
///
/// tokio-postgres handles SslMode::Prefer natively: it sends an SSLRequest and
/// falls back to plaintext if the server declines TLS. This requires passing
/// the TLS connector directly to `cfg.connect()` — deadpool commits the
/// connector type before the SSLRequest exchange, breaking Prefer fallback.
pub async fn connect(cfg: &DatabaseConfig) -> Result<Client> {
    let mut pg_cfg = tokio_postgres::Config::new();
    pg_cfg.host(&cfg.host);
    pg_cfg.port(cfg.port);
    pg_cfg.dbname(&cfg.dbname);
    pg_cfg.user(&cfg.user);
    pg_cfg.options(format!("-c search_path={SEARCH_PATH}"));
    if let Some(pw) = pgpass_lookup(&cfg.host, cfg.port, &cfg.dbname, &cfg.user) {
        pg_cfg.password(pw);
    }

    pg_cfg.ssl_mode(match cfg.ssl_mode {
        SslMode::Disable => tokio_postgres::config::SslMode::Disable,
        SslMode::Prefer => tokio_postgres::config::SslMode::Prefer,
        SslMode::Require | SslMode::VerifyCa | SslMode::VerifyFull => {
            tokio_postgres::config::SslMode::Require
        }
    });

    if cfg.ssl_mode == SslMode::Disable {
        let (client, conn) = pg_cfg.connect(tokio_postgres::NoTls).await?;
        tokio::spawn(async move {
            if let Err(e) = conn.await {
                tracing::error!("postgres connection error: {e}");
            }
        });
        return Ok(client);
    }

    let mut tls_builder = native_tls::TlsConnector::builder();
    match cfg.ssl_mode {
        SslMode::Require | SslMode::Prefer => {
            tls_builder.danger_accept_invalid_certs(true);
        }
        SslMode::VerifyCa | SslMode::VerifyFull => {
            if let Some(ref path) = cfg.ssl_root_cert {
                let pem = std::fs::read(path)?;
                let cert = native_tls::Certificate::from_pem(&pem)?;
                tls_builder.add_root_certificate(cert);
            }
        }
        _ => {}
    }
    if let Some(ref cert_path) = cfg.ssl_client_cert {
        if let Some(ref key_path) = cfg.ssl_client_key {
            let cert_pem = std::fs::read(cert_path)?;
            let key_pem = std::fs::read(key_path)?;
            let identity = native_tls::Identity::from_pkcs8(&cert_pem, &key_pem)?;
            tls_builder.identity(identity);
        }
    }
    let tls = MakeTlsConnector::new(tls_builder.build()?);
    let (client, conn) = pg_cfg.connect(tls).await?;
    tokio::spawn(async move {
        if let Err(e) = conn.await {
            tracing::error!("postgres connection error: {e}");
        }
    });
    Ok(client)
}

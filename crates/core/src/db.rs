use anyhow::Result;
use include_dir::{include_dir, Dir};
use tokio_postgres::Client;

use crate::config::{DatabaseConfig, SslMode};

const SEARCH_PATH: &str = "public,ag_catalog";

static MIGRATIONS_DIR: Dir<'static> = include_dir!("$CARGO_MANIFEST_DIR/migrations");
const RECEIPT_JSON: &str = include_str!("../migrations/.kryzhen-import-receipt.json");

fn embedded_migrations() -> anyhow::Result<Vec<kryzhen::Migration>> {
    let mut files: Vec<_> = MIGRATIONS_DIR
        .files()
        .filter(|f| f.path().extension().and_then(|e| e.to_str()) == Some("sql"))
        .collect();
    files.sort_by_key(|f| f.path());
    let mut all = Vec::new();
    for f in files {
        let label = f.path().to_string_lossy();
        let text = f
            .contents_utf8()
            .ok_or_else(|| anyhow::anyhow!("migration file is not valid UTF-8: {}", label))?;
        let blocks = kryzhen::parser::parse_file(text, &label)?;
        all.extend(kryzhen::file::apply_implicit_deps(blocks));
    }
    Ok(all)
}

/// Run kryzhen migrations against the database. Called once at startup.
///
/// Migrations and the sqlx import receipt are embedded at compile time.
/// If `_sqlx_migrations` exists (pre-v0.10 mimir DB), imports the sqlx history
/// into `mallard.applied_migrations` first — idempotent if already done or absent.
pub async fn migrate(cfg: &DatabaseConfig) -> Result<()> {
    let migrations = embedded_migrations()?;
    let mut client = connect(cfg).await?;
    // Parallel MCP connections can start with the same new embedded migration.
    // Serialize schema changes across processes, not just within one client.
    client
        .query("SELECT pg_advisory_lock(671942184)", &[])
        .await?;
    let receipt: kryzhen::sqlx_import::Receipt = serde_json::from_str(RECEIPT_JSON)?;
    let result: Result<()> = async {
        kryzhen::sqlx_import::import(&mut client, &receipt, &migrations)
            .await
            .map_err(anyhow::Error::from)?;
        kryzhen::migrate(&mut client, &migrations, Some("public"), false).await?;
        Ok(())
    }
    .await;
    let unlocked = client
        .query("SELECT pg_advisory_unlock(671942184)", &[])
        .await;
    result?;
    unlocked?;
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
    if let Some(pw) = crate::password::resolve(
        cfg.password.as_deref(),
        cfg.pgpassfile.as_deref(),
        &cfg.host,
        cfg.port,
        &cfg.dbname,
        &cfg.user,
    ) {
        pg_cfg.password(pw);
    }

    pg_cfg.ssl_mode(match cfg.ssl_mode {
        SslMode::Disable => tokio_postgres::config::SslMode::Disable,
        SslMode::Prefer => tokio_postgres::config::SslMode::Prefer,
        SslMode::Require | SslMode::VerifyCa | SslMode::VerifyFull => {
            tokio_postgres::config::SslMode::Require
        }
    });

    let tls = crate::tls::connector(
        &cfg.ssl_mode,
        cfg.ssl_root_cert.as_deref(),
        cfg.ssl_client_cert.as_deref(),
        cfg.ssl_client_key.as_deref(),
    )?;
    let (client, conn) = pg_cfg.connect(tls).await?;
    tokio::spawn(async move {
        if let Err(e) = conn.await {
            tracing::error!("postgres connection error: {e}");
        }
    });
    Ok(client)
}

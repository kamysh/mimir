use anyhow::Result;
use include_dir::{include_dir, Dir};
use tokio_postgres::Client;

use crate::config::{DatabaseConfig, SslMode};

const SEARCH_PATH: &str = "public,ag_catalog";

/// Empty-payload commit hints; listeners must read the durable pending queue.
pub const REVIEW_QUEUE_CHANNEL: &str = "mimir_review_queue_changed";

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
    let receipt: kryzhen::sqlx_import::Receipt = mimir_json::from_str(RECEIPT_JSON)?;
    let result: Result<()> = async {
        kryzhen::sqlx_import::import(&mut client, &receipt, &migrations)
            .await
            .map_err(anyhow::Error::from)?;
        apply_migrations(&mut client, &migrations).await?;
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

/// Kryzhen 2's template executor restricts search_path to the target schema.
/// Mimir's immutable historical SQL also resolves AGE operators in ag_catalog.
/// Keep Kryzhen's validation and ledger, but execute the original SQL with the
/// application's search path. The body and both ledger rows commit atomically.
async fn apply_migrations(client: &mut Client, migrations: &[kryzhen::Migration]) -> Result<()> {
    kryzhen::validation::check_duplicate_names(migrations)?;
    let ordered = kryzhen::graph::topo_sort(migrations.to_vec())?;
    kryzhen::postgres::ensure_schema(client).await?;
    let checksums = kryzhen::postgres::load_applied(client).await?;
    let applied = kryzhen::postgres::load_applied_for_schema(client, "public").await?;
    kryzhen::validation::check_checksums(&ordered, &checksums)?;
    for migration in &ordered {
        if applied.contains(&migration.name) {
            continue;
        }
        let mut tx = client.transaction().await?;
        tx.batch_execute(&format!("SET LOCAL search_path TO {SEARCH_PATH}"))
            .await?;
        tx.batch_execute(&migration.script).await?;
        kryzhen::postgres::record_applied(&mut tx, migration, "public").await?;
        tx.commit().await?;
    }
    Ok(())
}

/// Build the shared PostgreSQL settings for ordinary clients and listeners.
///
/// tokio-postgres handles SslMode::Prefer natively: it sends an SSLRequest and
/// falls back to plaintext if the server declines TLS. This requires passing
/// the TLS connector directly to `cfg.connect()` — deadpool commits the
/// connector type before the SSLRequest exchange, breaking Prefer fallback.
fn postgres_config(cfg: &DatabaseConfig) -> tokio_postgres::Config {
    let mut pg_cfg = tokio_postgres::Config::new();
    pg_cfg.host(&cfg.host);
    pg_cfg.port(cfg.port);
    pg_cfg.dbname(&cfg.dbname);
    pg_cfg.user(&cfg.user);
    // The driver otherwise schedules idle liveness probes after two hours.
    // Connection lifetime belongs to the caller, without a replacement timer.
    pg_cfg.keepalives(false);
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
    pg_cfg
}

fn tls_connector(cfg: &DatabaseConfig) -> Result<postgres_native_tls::MakeTlsConnector> {
    crate::tls::connector(
        &cfg.ssl_mode,
        cfg.ssl_root_cert.as_deref(),
        cfg.ssl_client_cert.as_deref(),
        cfg.ssl_client_key.as_deref(),
    )
}

/// Open a client and drive its ordinary query connection in the background.
pub async fn connect(cfg: &DatabaseConfig) -> Result<Client> {
    let (client, conn) = postgres_config(cfg).connect(tls_connector(cfg)?).await?;
    tokio::spawn(async move {
        if let Err(e) = conn.await {
            tracing::error!("postgres connection error: {e}");
        }
    });
    Ok(client)
}

/// Returned only after the server acknowledges LISTEN. Private fields prevent
/// callers from constructing an unsubscribed value. Retain it across the initial
/// queue scan so a change remains available to the subsequent event wait.
pub struct ReviewQueueSubscription {
    client: Client,
    events: tokio::sync::mpsc::UnboundedReceiver<Result<()>>,
    reader: tokio::task::JoinHandle<()>,
}

impl ReviewQueueSubscription {
    pub async fn connect(cfg: &DatabaseConfig) -> Result<Self> {
        Self::connect_channel(cfg, REVIEW_QUEUE_CHANNEL).await
    }

    async fn connect_channel(cfg: &DatabaseConfig, channel: &'static str) -> Result<Self> {
        Self::connect_channels(cfg, &[channel]).await
    }

    async fn connect_channels(cfg: &DatabaseConfig, channels: &[&'static str]) -> Result<Self> {
        Self::connect_filtered(cfg, channels, None).await
    }

    async fn connect_filtered(
        cfg: &DatabaseConfig,
        channels: &[&'static str],
        payload: Option<String>,
    ) -> Result<Self> {
        let (client, mut connection) = postgres_config(cfg).connect(tls_connector(cfg)?).await?;
        let (sent, events) = tokio::sync::mpsc::unbounded_channel();
        let observed_channels = channels.to_vec();
        let reader = tokio::spawn(async move {
            while let Some(message) = std::future::poll_fn(|cx| connection.poll_message(cx)).await {
                let event = match message {
                    Ok(tokio_postgres::AsyncMessage::Notification(notification))
                        if observed_channels.contains(&notification.channel())
                            && payload
                                .as_ref()
                                .is_none_or(|expected| notification.payload() == expected) =>
                    {
                        Ok(())
                    }
                    Ok(_) => continue,
                    Err(error) => {
                        let _ = sent.send(Err(error.into()));
                        return;
                    }
                };
                if sent.send(event).is_err() {
                    return;
                }
            }
            let _ = sent.send(Err(anyhow::anyhow!(
                "owned database listener disconnected: {observed_channels:?}"
            )));
        });
        let subscription = Self {
            client,
            events,
            reader,
        };
        for channel in channels {
            subscription
                .client
                .batch_execute(&format!("LISTEN {channel}"))
                .await?;
        }
        Ok(subscription)
    }

    /// A hint to rescan; this is not a saved review or a count of changed rows.
    pub async fn changed(&mut self) -> Result<()> {
        self.events
            .recv()
            .await
            .ok_or_else(|| anyhow::anyhow!("review queue listener stopped"))?
    }
}

/// Review preparation owns both its source revision and its embedding owner.
/// This is separate from the new-review queue: acknowledgement cannot wake
/// the watcher into repeatedly reviewing the work it just completed.
pub(crate) struct ReviewPreparationSubscription(ReviewQueueSubscription);

impl ReviewPreparationSubscription {
    pub(crate) async fn connect(cfg: &DatabaseConfig) -> Result<Self> {
        Ok(Self(
            ReviewQueueSubscription::connect_channels(
                cfg,
                &[
                    "mimir_review_state_changed",
                    "mimir_embedding_owners_changed",
                ],
            )
            .await?,
        ))
    }

    pub(crate) async fn changed(&mut self) -> Result<()> {
        self.0.changed().await
    }
}

/// Subscribed before checking an owner's durable row. Empty hints never
/// identify which job stopped; each request must recheck its own owner.
pub(crate) struct EmbeddingOwnerSubscription(ReviewQueueSubscription);

/// Acknowledged subscription for one action. Cancellation notifications stop
/// its owned body before waiting on any further database read; ACK notifications
/// only tell a canceller to reread the durable pending execution rows.
pub(crate) struct OperationExecutionSubscription(ReviewQueueSubscription);

impl OperationExecutionSubscription {
    pub(crate) async fn cancelled(cfg: &DatabaseConfig, token: uuid::Uuid) -> Result<Self> {
        Ok(Self(
            ReviewQueueSubscription::connect_filtered(
                cfg,
                &["mimir_operation_cancelled"],
                Some(token.to_string()),
            )
            .await?,
        ))
    }

    pub(crate) async fn stopped(cfg: &DatabaseConfig, token: uuid::Uuid) -> Result<Self> {
        Ok(Self(
            ReviewQueueSubscription::connect_filtered(
                cfg,
                &["mimir_operation_execution_stopped"],
                Some(token.to_string()),
            )
            .await?,
        ))
    }

    pub(crate) async fn changed(&mut self) -> Result<()> {
        self.0.changed().await
    }
}

impl EmbeddingOwnerSubscription {
    pub(crate) async fn connect(cfg: &DatabaseConfig) -> Result<Self> {
        Ok(Self(
            ReviewQueueSubscription::connect_channel(cfg, "mimir_embedding_owners_changed").await?,
        ))
    }

    pub(crate) async fn changed(&mut self) -> Result<()> {
        self.0.changed().await
    }
}

impl Drop for ReviewQueueSubscription {
    fn drop(&mut self) {
        self.reader.abort();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_connections_disable_idle_probes_without_choosing_deadlines() {
        let mut cfg: DatabaseConfig = toml::from_str(
            "host='fixture.invalid'\nport=1\ndbname='fixture'\nuser='fixture'\npassword='fixture-only'\n",
        )
        .unwrap();
        for mode in [
            SslMode::Disable,
            SslMode::Prefer,
            SslMode::Require,
            SslMode::VerifyCa,
            SslMode::VerifyFull,
        ] {
            cfg.ssl_mode = mode;
            let parameters = postgres_config(&cfg);
            assert!(!parameters.get_keepalives());
            assert!(parameters.get_connect_timeout().is_none());
            assert!(parameters.get_tcp_user_timeout().is_none());
        }
    }
}

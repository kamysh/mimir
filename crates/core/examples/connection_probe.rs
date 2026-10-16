//! Exercised by tests/database-connections.py against a disposable server.
use anyhow::Result;
use mimir_core::{config::Config, db};

#[tokio::main]
async fn main() -> Result<()> {
    let path = std::env::args().nth(1).expect("config path");
    let cfg = Config::load_from_path(std::path::Path::new(&path))?;
    if std::env::args().nth(2).as_deref() == Some("migrate") {
        db::migrate(&cfg.database).await?;
    }
    let client = db::connect(&cfg.database).await?;
    let row = client
        .query_one(
            "SELECT ssl FROM pg_stat_ssl WHERE pid=pg_backend_pid()",
            &[],
        )
        .await?;
    println!("ssl={}", row.get::<_, bool>(0));
    Ok(())
}

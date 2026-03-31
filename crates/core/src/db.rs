use anyhow::Result;
use sqlx::{
    postgres::{PgConnectOptions, PgPoolOptions},
    PgPool,
};
use std::str::FromStr;

// public first: unqualified CREATE TABLE → public, not ag_catalog.
// ag_catalog second: AGE operators resolve correctly.
const SEARCH_PATH: &str = "public,ag_catalog";

fn apply_search_path(opts: PgConnectOptions) -> PgConnectOptions {
    opts.options([("search_path", SEARCH_PATH)])
}

pub async fn connect(dsn: &str) -> Result<PgPool> {
    let opts = apply_search_path(PgConnectOptions::from_str(dsn)?);
    let pool = PgPoolOptions::new()
        .max_connections(10)
        .connect_with(opts)
        .await?;
    Ok(pool)
}
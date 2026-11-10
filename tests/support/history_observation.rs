//! Read physical learning history without decoding old JSON into today's schema.
use chrono::{DateTime, Utc};
use tokio_postgres::{Error, Transaction};
use uuid::Uuid;

#[derive(Debug, PartialEq)]
pub struct Head {
    pub identity: Uuid,
    pub project: String,
    pub revision: i64,
    pub review_revision: i64,
    pub reviewed_revision: i64,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, PartialEq)]
pub struct HistoryRow {
    pub experience: Uuid,
    pub revision: i64,
    pub source_revision: i64,
    pub created_at: DateTime<Utc>,
    // PostgreSQL's JSONB output is retained as JSON text so old fields and
    // arbitrary-precision numbers are not lost through a current decoder.
    pub payload_json: String,
}

#[derive(Debug, PartialEq)]
pub struct History {
    pub heads: Vec<Head>,
    pub source_rows: Vec<HistoryRow>,
    pub review_rows: Vec<HistoryRow>,
}

async fn rows(tx: &Transaction<'_>, sql: &str) -> Result<Vec<HistoryRow>, Error> {
    tx.query(sql, &[])
        .await?
        .into_iter()
        .map(|row| {
            Ok(HistoryRow {
                experience: row.try_get(0)?,
                revision: row.try_get(1)?,
                source_revision: row.try_get(2)?,
                created_at: row.try_get(3)?,
                payload_json: row.try_get(4)?,
            })
        })
        .collect()
}

pub async fn observe(tx: &Transaction<'_>) -> Result<History, Error> {
    let heads = tx.query("SELECT id, project, revision, review_revision, reviewed_revision, updated_at FROM public.mimir_experiences ORDER BY id", &[])
        .await?.into_iter().map(|row| Ok(Head { identity: row.try_get(0)?, project: row.try_get(1)?,
            revision: row.try_get(2)?, review_revision: row.try_get(3)?, reviewed_revision: row.try_get(4)?, updated_at: row.try_get(5)? })).collect::<Result<_, Error>>()?;
    Ok(History {
        heads,
        source_rows: rows(tx, "SELECT experience_id, revision, revision, created_at, payload::text FROM public.mimir_experience_versions ORDER BY experience_id, revision").await?,
        review_rows: rows(tx, "SELECT experience_id, revision, experience_revision, created_at, payload::text FROM public.mimir_review_versions ORDER BY experience_id, revision").await?,
    })
}

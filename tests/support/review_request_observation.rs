//! Preserve original review requests, including old rows without one.
use tokio_postgres::{Error, Transaction};
use uuid::Uuid;

#[derive(Debug, PartialEq)]
pub struct ReviewRequest {
    pub experience: Uuid,
    pub revision: i64,
    pub request_json: Option<String>,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Vec<ReviewRequest>, Error> {
    tx.query("SELECT experience_id, revision, request::text FROM public.mimir_review_versions ORDER BY experience_id, revision", &[])
        .await?.into_iter().map(|row| Ok(ReviewRequest {
            experience: row.try_get(0)?, revision: row.try_get(1)?, request_json: row.try_get(2)?,
        })).collect()
}

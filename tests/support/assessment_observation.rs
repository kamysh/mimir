//! Read assessment payloads and stored numeric contributions independently.
use tokio_postgres::{Error, Transaction};
use uuid::Uuid;

#[derive(Debug, PartialEq)]
pub struct Assessment {
    pub experience: Uuid,
    pub review_revision: i64,
    pub belief: Uuid,
    pub scope: String,
    pub rubric: String,
    pub positive: f64,
    pub negative: f64,
    pub benefit: f64,
    pub benefit_weight: f64,
    pub payload_json: String,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Vec<Assessment>, Error> {
    tx.query("SELECT experience_id, review_revision, belief_id, scope, rubric, positive, negative, benefit, benefit_weight, payload::text FROM public.mimir_assessment_contributions ORDER BY experience_id, review_revision, belief_id, scope, rubric", &[])
        .await?.into_iter().map(|row| Ok(Assessment {
            experience: row.try_get(0)?, review_revision: row.try_get(1)?, belief: row.try_get(2)?,
            scope: row.try_get(3)?, rubric: row.try_get(4)?, positive: row.try_get(5)?,
            negative: row.try_get(6)?, benefit: row.try_get(7)?, benefit_weight: row.try_get(8)?,
            payload_json: row.try_get(9)?,
        })).collect()
}

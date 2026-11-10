//! Observe all candidate reservations, including retired or missing nodes.
use tokio_postgres::{Error, Transaction};
use uuid::Uuid;

#[derive(Debug, PartialEq)]
pub struct Candidate {
    pub experience: Uuid,
    pub key: String,
    pub kind: String,
    pub node: Uuid,
    pub declaration_json: String,
    pub retired: bool,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Vec<Candidate>, Error> {
    tx.query("SELECT experience_id, candidate_key, kind, node_id, declaration::text, retired FROM public.mimir_review_candidates ORDER BY experience_id, candidate_key", &[])
        .await?.into_iter().map(|row| Ok(Candidate {
            experience: row.try_get(0)?, key: row.try_get(1)?, kind: row.try_get(2)?,
            node: row.try_get(3)?, declaration_json: row.try_get(4)?, retired: row.try_get(5)?,
        })).collect()
}

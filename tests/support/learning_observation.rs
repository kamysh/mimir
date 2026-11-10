//! Read learning records from one consistent database view.
#[path = "assessment_observation.rs"]
pub mod assessments;
#[path = "candidate_observation.rs"]
pub mod candidates;
#[path = "history_observation.rs"]
pub mod history;
#[path = "ownership_observation.rs"]
pub mod owners;
#[path = "review_request_observation.rs"]
pub mod requests;

use anyhow::{bail, Result};
use tokio_postgres::Transaction;

#[derive(Debug, PartialEq)]
pub struct LearningObservation {
    pub history: history::History,
    pub owners: Vec<owners::ItemOwner>,
    pub candidates: Vec<candidates::Candidate>,
    pub assessments: Vec<assessments::Assessment>,
    pub requests: Vec<requests::ReviewRequest>,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<LearningObservation> {
    let isolation: String = tx
        .query_one("SHOW transaction_isolation", &[])
        .await?
        .try_get(0)?;
    if isolation != "repeatable read" && isolation != "serializable" {
        bail!("Use one repeatable-read or serializable transaction to observe the database consistently");
    }
    Ok(LearningObservation {
        history: history::observe(tx).await?,
        owners: owners::observe(tx).await?,
        candidates: candidates::observe(tx).await?,
        assessments: assessments::observe(tx).await?,
        requests: requests::observe(tx).await?,
    })
}

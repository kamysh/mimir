use super::state::{DeferredReview, RepairCase};
use anyhow::{Context, Result};
use mimir_core::{config::DatabaseConfig, db};
use tokio_postgres::Client;
use uuid::Uuid;

pub(super) enum Storage {
    Database,
    #[cfg(test)]
    Fixture,
}

impl Storage {
    pub async fn connect(self, database: &DatabaseConfig) -> Result<Option<Client>> {
        match self {
            Self::Database => connect(database).await.map(Some),
            #[cfg(test)]
            Self::Fixture => Ok(None),
        }
    }
}

#[derive(Debug)]
pub(super) struct Access;
impl std::fmt::Display for Access {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(fmt, "Could not access the PostgreSQL review repair cases")
    }
}
impl std::error::Error for Access {}

pub(super) async fn connect(database: &DatabaseConfig) -> Result<Client> {
    db::connect(database).await.context(Access)
}

// The case is also the durable request to notify the operator. The watcher
// hands it to the deduplicating mail outbox, including after a restart.
pub(super) async fn open(
    client: &Client,
    id: Uuid,
    revision: i64,
    case: &RepairCase,
) -> Result<bool> {
    let row = client
        .query_opt(
            "WITH source AS (SELECT id, revision FROM mimir_experiences
         WHERE id = $1 AND revision = $2 AND reviewed_revision < revision FOR SHARE)
         INSERT INTO mimir_review_repair_cases (experience_id, source_revision, remedy)
         SELECT id, revision, $3 FROM source
         ON CONFLICT (experience_id, source_revision) DO UPDATE SET remedy=EXCLUDED.remedy
         WHERE mimir_review_repair_cases.remedy->>'remedy' IS DISTINCT FROM EXCLUDED.remedy->>'remedy'
         RETURNING experience_id",
            &[&id, &revision, &serde_json::to_value(case)?],
        )
        .await?;
    Ok(row.is_some())
}

pub(super) async fn lookup(
    database: &DatabaseConfig,
    id: Uuid,
    revision: i64,
) -> Result<Option<DeferredReview>> {
    let client = db::connect(database).await?;
    let row = client.query_opt("SELECT remedy FROM mimir_review_repair_cases WHERE experience_id=$1 AND source_revision=$2", &[&id, &revision]).await?;
    row.map(|row| {
        Ok(DeferredReview {
            id,
            revision,
            repair: Some(serde_json::from_value(row.get(0))?),
        })
    })
    .transpose()
}

pub(super) async fn list(
    client: &Client,
    project: &Option<String>,
) -> Result<Vec<(DeferredReview, i64, i64)>> {
    let rows = client
        .query(
            "SELECT c.experience_id, c.source_revision, c.remedy, e.revision, e.reviewed_revision
        FROM mimir_review_repair_cases c JOIN mimir_experiences e ON e.id=c.experience_id
        WHERE $1::text IS NULL OR e.project=$1",
            &[project],
        )
        .await?;
    rows.into_iter()
        .map(|row| {
            Ok((
                DeferredReview {
                    id: row.get(0),
                    revision: row.get(1),
                    repair: Some(serde_json::from_value(row.get(2))?),
                },
                row.get(3),
                row.get(4),
            ))
        })
        .collect()
}

pub(super) async fn close(client: &Client, case: &DeferredReview) -> Result<()> {
    client
        .execute(
            "DELETE FROM mimir_review_repair_cases WHERE experience_id=$1 AND source_revision=$2",
            &[&case.id, &case.revision],
        )
        .await?;
    Ok(())
}

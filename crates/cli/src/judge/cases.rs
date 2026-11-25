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
         WHERE mimir_review_repair_cases.remedy IS DISTINCT FROM EXCLUDED.remedy
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

/// Reopen only a recorded obstruction that the current handler actually fixes.
/// Keep the case for outcome confirmation while omitting its queue exclusion.
pub(super) async fn handler_restored(client: &Client, case: &DeferredReview) -> Result<bool> {
    if !case
        .repair
        .as_ref()
        .is_some_and(|r| r.remedy == super::state::Remedy::EditReview)
    {
        return Ok(false);
    }
    let row = client
        .query_opt(
            "SELECT t.transcript FROM mimir_failed_review_transcripts t
         JOIN mimir_experiences e ON e.id=t.experience_id
         WHERE t.experience_id=$1 AND t.source_revision=$2
           AND e.revision=$2 AND e.reviewed_revision < e.revision
         ORDER BY t.created_at DESC FETCH FIRST 1 ROW ONLY",
            &[&case.id, &case.revision],
        )
        .await?;
    Ok(row.is_some_and(|row| restored_transcript(&row.get::<_, serde_json::Value>(0))))
}

fn restored_transcript(transcript: &serde_json::Value) -> bool {
    let Some(events) = transcript["events"].as_array() else {
        return false;
    };
    let [.., previous, last] = events.as_slice() else {
        return false;
    };
    if previous["kind"] == "automatic_review_correction" {
        // The old shortcut emitted its result directly. The corrected loop
        // records a tool_request before submission and feeds the reply back.
        return last["kind"] == "tool_result"
            && last["tool"] == "review_experience"
            && last["detail"]["status"] == "needs_correction";
    }
    if previous["kind"] == "tool_request"
        && previous["tool"] == "explain_belief"
        && last["kind"] == "tool_rejection"
        && last["tool"] == "explain_belief"
        && matches!(
            last["detail"].as_str(),
            Some("invalid explain limit" | "missing explain offset")
        )
    {
        let args = &previous["detail"];
        return args["id"]
            .as_str()
            .is_some_and(|id| id.parse::<Uuid>().is_ok())
            && args
                .get("limit")
                .is_none_or(|v| v.as_u64().is_some_and(|n| n > 0))
            && args.get("offset").is_none_or(|v| v.as_u64().is_some());
    }
    false
}

#[cfg(test)]
mod tests {
    use super::restored_transcript;
    use serde_json::json;

    #[test]
    fn reopens_only_failures_handled_by_the_repaired_protocol() {
        let auto = json!({"kind":"automatic_review_correction"});
        let rejection = json!({"kind":"tool_result","tool":"review_experience",
            "detail":{"status":"needs_correction"}});
        assert!(restored_transcript(&json!({"events":[auto,rejection]})));
        let request = json!({"kind":"tool_request","tool":"review_experience","detail":{}});
        assert!(!restored_transcript(
            &json!({"events":[auto,request,rejection]})
        ));
        assert!(!restored_transcript(&json!({"events":[auto,
            {"kind":"tool_result","tool":"review_experience","detail":{"status":"needs_input"}}]})));
        assert!(!restored_transcript(
            &json!({"events":[auto,rejection,{"kind":"model_done"}]})
        ));
        for args in [
            json!({"id":"6892c700-72c9-40c4-95b2-fa7f8afcf09c"}),
            json!({"id":"6892c700-72c9-40c4-95b2-fa7f8afcf09c","limit":21,"offset":0}),
        ] {
            let request = json!({"kind":"tool_request","tool":"explain_belief","detail":args});
            let rejection = json!({"kind":"tool_rejection","tool":"explain_belief",
                "detail":"invalid explain limit"});
            assert!(restored_transcript(&json!({"events":[request,rejection]})));
            for invalid in [json!(0), json!(-1), json!("all"), json!(null)] {
                let mut changed = request.clone();
                changed["detail"]["limit"] = invalid;
                assert!(!restored_transcript(&json!({"events":[changed,rejection]})));
            }
        }
    }
}

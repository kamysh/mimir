use super::state::Report;
use anyhow::Result;
use mimir_core::{config::DatabaseConfig, db, learning::ExperienceState};
use serde_json::{json, Value};
use tokio_postgres::Client;
use uuid::Uuid;

pub(super) struct Attempt {
    key: String,
    experience: Uuid,
    revision: i64,
    prior_review: i64,
    pending_readback: bool,
    events: Vec<Value>,
}

impl Attempt {
    pub(super) fn new(selected: &ExperienceState) -> Self {
        Self {
            key: Uuid::new_v4().simple().to_string(),
            experience: selected.experience.id,
            revision: selected.revision,
            prior_review: selected.review_revision,
            pending_readback: false,
            events: Vec::new(),
        }
    }

    pub(super) fn event(&mut self, kind: &str, tool: Option<&str>, detail: Value) {
        self.events
            .push(json!({"kind":kind,"tool":tool,"detail":detail}));
    }

    pub(super) fn pending(&mut self) {
        self.pending_readback = true;
    }

    async fn save(&self, client: &Client) -> Result<Option<Uuid>> {
        if let Some(row) = client
            .query_opt(
                "SELECT id FROM mimir_failed_review_transcripts WHERE attempt_key = $1",
                &[&self.key],
            )
            .await?
        {
            return Ok(Some(row.get(0)));
        }
        // Serialize the decision with concurrent changes to this experience.
        // A known failure remains useful after a subsequent repair. An
        // inconclusive readback needs fresh evidence that the pin is pending.
        let transcript = json!({
            "readback": if self.pending_readback { "pending" } else { "unavailable" },
            "events": self.events,
        });
        let row = client
            .query_opt(
                "INSERT INTO mimir_failed_review_transcripts
                    (attempt_key, experience_id, source_revision, transcript)
                 SELECT $1, v.experience_id, v.revision, $6
                 FROM mimir_experience_versions v JOIN mimir_experiences e
                    ON e.id = v.experience_id
                 WHERE v.experience_id = $2 AND v.revision = $3 AND
                    ($4 OR (e.revision = $3 AND
                    (e.reviewed_revision <> $3 OR e.review_revision <= $5)))
                 FOR SHARE OF e, v
                 ON CONFLICT (attempt_key) DO UPDATE SET attempt_key = EXCLUDED.attempt_key
                 RETURNING id",
                &[
                    &self.key,
                    &self.experience,
                    &self.revision,
                    &self.pending_readback,
                    &self.prior_review,
                    &transcript,
                ],
            )
            .await?;
        Ok(row.map(|row| row.get(0)))
    }
}

struct Waiting {
    database: DatabaseConfig,
    attempt: Attempt,
}

#[derive(Default)]
pub(super) struct Pending(Vec<Waiting>);

impl Pending {
    pub(super) fn extend(
        &mut self,
        database: &DatabaseConfig,
        attempts: impl IntoIterator<Item = Attempt>,
    ) {
        self.0.extend(attempts.into_iter().map(|attempt| Waiting {
            database: database.clone(),
            attempt,
        }));
    }

    fn is_target(old: &DatabaseConfig, new: &DatabaseConfig) -> bool {
        old.host == new.host && old.port == new.port && old.dbname == new.dbname
    }

    /// Called after each batch, including the first check after reconnect.
    pub(super) async fn flush(&mut self, database: &DatabaseConfig, report: &mut Report) {
        if self
            .0
            .iter()
            .any(|entry| Self::is_target(&entry.database, database))
        {
            if let Ok(client) = db::connect(database).await {
                let mut remaining = Vec::new();
                for entry in self.0.drain(..) {
                    if !Self::is_target(&entry.database, database) {
                        remaining.push(entry);
                        continue;
                    }
                    match entry.attempt.save(&client).await {
                        Ok(Some(id)) => {
                            if report.selected_ids.contains(&entry.attempt.experience) {
                                report.diagnostics_id.get_or_insert(id);
                            }
                            if let Some(case) = report
                                .deferred_reviews
                                .iter_mut()
                                .find(|pin| {
                                    pin.id == entry.attempt.experience
                                        && pin.revision == entry.attempt.revision
                                })
                                .and_then(|pin| pin.repair.as_mut())
                            {
                                case.diagnostic_id = Some(id);
                                case.transcript_pending = false;
                            }
                        }
                        Ok(None) => {}
                        Err(_) => remaining.push(entry),
                    }
                }
                self.0 = remaining;
            }
        }
        report.transcripts_pending = self.0.len();
        for pin in &mut report.deferred_reviews {
            if let Some(case) = &mut pin.repair {
                case.transcript_pending = self.0.iter().any(|entry| {
                    Self::is_target(&entry.database, database)
                        && entry.attempt.experience == pin.id
                        && entry.attempt.revision == pin.revision
                });
            }
        }
    }
}

pub(super) async fn lookup(
    database: &DatabaseConfig,
    id: Option<Uuid>,
    list: bool,
) -> Result<Option<Value>> {
    let client = db::connect(database).await?;
    if list {
        let rows = client
            .query(
                "SELECT id, experience_id, source_revision, created_at
             FROM mimir_failed_review_transcripts ORDER BY created_at DESC",
                &[],
            )
            .await?;
        let attempts: Vec<_> = rows
            .iter()
            .map(|row| {
                json!({
                    "id":row.get::<_, Uuid>(0), "experience_id":row.get::<_, Uuid>(1),
                    "source_revision":row.get::<_, i64>(2),
                    "created_at":row.get::<_, chrono::DateTime<chrono::Utc>>(3),
                })
            })
            .collect();
        return Ok(Some(json!({"status":"available","attempts":attempts})));
    }
    let row = client
        .query_opt(
            "SELECT id, experience_id, source_revision, created_at, transcript
         FROM mimir_failed_review_transcripts WHERE $1::uuid IS NULL OR id = $1
         ORDER BY created_at DESC FETCH FIRST 1 ROW ONLY",
            &[&id],
        )
        .await?;
    Ok(row.map(|row| {
        json!({"status":"available","trace":{
            "id":row.get::<_, Uuid>(0), "experience_id":row.get::<_, Uuid>(1),
            "source_revision":row.get::<_, i64>(2),
            "created_at":row.get::<_, chrono::DateTime<chrono::Utc>>(3),
            "transcript":row.get::<_, Value>(4)
        }})
    }))
}

pub(super) async fn for_revision(
    database: &DatabaseConfig,
    experience: Uuid,
    revision: i64,
) -> Result<Vec<Uuid>> {
    let client = db::connect(database).await?;
    let rows = client
        .query(
            "SELECT id FROM mimir_failed_review_transcripts
         WHERE experience_id = $1 AND source_revision = $2 ORDER BY created_at DESC",
            &[&experience, &revision],
        )
        .await?;
    Ok(rows.iter().map(|row| row.get(0)).collect())
}

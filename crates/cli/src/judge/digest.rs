use super::{config, state, RunOutcome};
use anyhow::{anyhow, Result};
use chrono::{DateTime, Local, NaiveDate, TimeZone, Timelike, Utc};
use mimir_notifications::{Digest, Notifier, Outcome};
use std::{fmt::Write, path::Path};
use tokio_postgres::Client;

#[derive(Clone, Copy, Default)]
struct Counts {
    new_experiences: i64,
    source_revisions: i64,
    judge_reviews: i64,
}

impl std::ops::AddAssign for Counts {
    fn add_assign(&mut self, other: Self) {
        self.new_experiences += other.new_experiences;
        self.source_revisions += other.source_revisions;
        self.judge_reviews += other.judge_reviews;
    }
}

fn midnight(day: NaiveDate) -> Result<DateTime<Utc>> {
    Local
        .from_local_datetime(
            &day.and_hms_opt(0, 0, 0)
                .ok_or_else(|| anyhow!("invalid day"))?,
        )
        .earliest()
        .map(|instant| instant.with_timezone(&Utc))
        .ok_or_else(|| anyhow!("local midnight is unavailable"))
}

fn reporting_day(now: DateTime<Local>) -> Option<NaiveDate> {
    if now.hour() < 9 {
        return None;
    }
    now.date_naive().pred_opt()
}

fn first_day(last: Option<&str>, through: NaiveDate) -> Result<Option<NaiveDate>> {
    let first = match last {
        Some(value) => NaiveDate::parse_from_str(value, "%Y-%m-%d")?
            .succ_opt()
            .ok_or_else(|| anyhow!("digest date overflow"))?,
        None => through,
    };
    Ok((first <= through).then_some(first))
}

fn latest_status(run: &RunOutcome) -> &'static str {
    if run.degraded {
        "needs attention"
    } else if run.idle {
        "idle"
    } else if run.code == 0 {
        "batch complete"
    } else {
        "unavailable"
    }
}

async fn counts(client: &Client, start: DateTime<Utc>, end: DateTime<Utc>) -> Result<Counts> {
    let row = client
        .query_one(
            "SELECT \
             (SELECT count(*) FROM mimir_experience_versions WHERE revision=1 AND created_at >= $1 AND created_at < $2), \
             (SELECT count(*) FROM mimir_experience_versions WHERE revision>1 AND created_at >= $1 AND created_at < $2), \
             (SELECT count(*) FROM mimir_review_versions WHERE payload->>'reviewer'='mimir-judge' AND created_at >= $1 AND created_at < $2)",
            &[&start, &end],
        )
        .await?;
    Ok(Counts {
        new_experiences: row.get(0),
        source_revisions: row.get(1),
        judge_reviews: row.get(2),
    })
}

fn render(
    rows: &[(NaiveDate, Counts)],
    mut cumulative: Counts,
    backlog: i64,
    status: &str,
    timezone: &str,
) -> Result<String> {
    let mut body = format!(
        "Mimir judge daily statistics\nCalendar days use this computer's local time ({timezone}).\nCounts come from the configured Mimir database.\n\n"
    );
    body.push_str("Date         New experiences  Source revisions  Judge reviews  Running totals (new / revisions / reviews)\n");
    for (day, daily) in rows {
        cumulative += *daily;
        writeln!(
            body,
            "{day}   {:>15}  {:>16}  {:>13}  {} / {} / {}",
            daily.new_experiences,
            daily.source_revisions,
            daily.judge_reviews,
            cumulative.new_experiences,
            cumulative.source_revisions,
            cumulative.judge_reviews
        )?;
    }
    writeln!(body, "\nCurrent review backlog: {backlog}")?;
    writeln!(body, "Latest watcher status: {status}")?;
    body.push_str("\nSource revisions count stored updates to experiences. They are distinct from the per-run 'corrected' status counter.\n");
    Ok(body)
}

async fn content(
    client: &Client,
    first: NaiveDate,
    through: NaiveDate,
    status: &str,
    timezone: &str,
) -> Result<String> {
    client
        .batch_execute("BEGIN TRANSACTION ISOLATION LEVEL REPEATABLE READ READ ONLY")
        .await?;
    let baseline = counts(
        client,
        DateTime::<Utc>::from_timestamp(0, 0).ok_or_else(|| anyhow!("invalid epoch"))?,
        midnight(first)?,
    )
    .await?;
    let mut rows = Vec::new();
    let mut day = first;
    loop {
        let next = day
            .succ_opt()
            .ok_or_else(|| anyhow!("digest date overflow"))?;
        let daily = counts(client, midnight(day)?, midnight(next)?).await?;
        rows.push((day, daily));
        if day == through {
            break;
        }
        day = next;
    }
    let backlog: i64 = client
        .query_one(
            "SELECT count(*) FROM mimir_experiences WHERE reviewed_revision < revision",
            &[],
        )
        .await?
        .get(0);
    client.batch_execute("COMMIT").await?;
    render(&rows, baseline, backlog, status, timezone)
}

pub async fn tick(
    config_path: Option<&Path>,
    state_dir: Option<&Path>,
    run: &RunOutcome,
) -> Result<bool> {
    let now = Local::now();
    let Some(through) = reporting_day(now) else {
        return Ok(false);
    };
    let settings = config::load(config_path)?;
    if !settings.email.enabled {
        return Ok(false);
    }
    let path = state::resolve(state_dir)?;
    let notifier = Notifier::new(&settings.email, path)?;
    let cursor = notifier.digest_state()?;
    let Some(first) = first_day(cursor.through_day.as_deref(), through)? else {
        return Ok(false);
    };
    if (now.timestamp().max(0) as u64) < cursor.next_due {
        return Ok(cursor.last_attempt_failed);
    }
    let client = mimir_core::db::connect(&settings.core.database).await?;
    let body = content(
        &client,
        first,
        through,
        latest_status(run),
        &now.format("%Z").to_string(),
    )
    .await?;
    let digest = Digest {
        through_day: through.to_string(),
        body,
    };
    match notifier.send_digest(&digest).await? {
        Outcome::Sent | Outcome::NotNeeded | Outcome::Disabled => Ok(false),
        Outcome::RetryPending => Ok(true),
        _ => Err(anyhow!("daily email unavailable")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nine_am_boundary_and_catch_up_start() {
        let day = NaiveDate::from_ymd_opt(2026, 10, 11).unwrap();
        let early = Local
            .from_local_datetime(&day.and_hms_opt(8, 59, 0).unwrap())
            .single()
            .unwrap();
        let due = Local
            .from_local_datetime(&day.and_hms_opt(9, 0, 0).unwrap())
            .single()
            .unwrap();
        assert_eq!(reporting_day(early), None);
        assert_eq!(reporting_day(due), day.pred_opt());
        assert_eq!(first_day(None, day).unwrap(), Some(day));
        assert_eq!(
            first_day(Some("2026-10-08"), day).unwrap(),
            NaiveDate::from_ymd_opt(2026, 10, 9)
        );
        assert_eq!(first_day(Some("2026-10-11"), day).unwrap(), None);
    }

    #[test]
    fn missed_days_share_one_digest_with_daily_and_running_counts() {
        let first = NaiveDate::from_ymd_opt(2026, 10, 10).unwrap();
        let second = first.succ_opt().unwrap();
        let body = render(
            &[
                (
                    first,
                    Counts {
                        new_experiences: 2,
                        source_revisions: 0,
                        judge_reviews: 1,
                    },
                ),
                (
                    second,
                    Counts {
                        new_experiences: 1,
                        source_revisions: 1,
                        judge_reviews: 2,
                    },
                ),
            ],
            Counts {
                new_experiences: 4,
                source_revisions: 1,
                judge_reviews: 3,
            },
            5,
            "idle",
            "PDT",
        )
        .unwrap();
        assert!(body.contains("2026-10-10") && body.contains("6 / 1 / 4"));
        assert!(body.contains("2026-10-11") && body.contains("7 / 2 / 6"));
        assert!(body.contains("Current review backlog: 5"));
        assert!(body.contains("Latest watcher status: idle"));
    }

    #[test]
    fn completed_batch_is_reported_as_complete() {
        assert_eq!(
            latest_status(&RunOutcome {
                code: 0,
                degraded: false,
                idle: false
            }),
            "batch complete"
        );
    }
}

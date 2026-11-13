use super::{config, state};
use anyhow::{anyhow, Result};
use chrono::{DateTime, Local, LocalResult, NaiveDate, NaiveTime, TimeZone, Timelike, Utc};
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

fn reporting_day(now: DateTime<Local>, configured: NaiveTime) -> Option<NaiveDate> {
    if now.time() < configured {
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

fn latest_status(report: Option<&state::Report>) -> &'static str {
    match report.map(|report| report.status.as_str()) {
        Some("blocked" | "partial") => "needs attention",
        Some("idle") => "idle",
        Some("complete") => "batch complete",
        _ => "unavailable",
    }
}

fn delivery_on(day: NaiveDate, configured: NaiveTime) -> Result<DateTime<Local>> {
    let mut clock = day.and_time(configured);
    loop {
        match Local.from_local_datetime(&clock) {
            LocalResult::Single(instant) => return Ok(instant),
            LocalResult::Ambiguous(first, second) => return Ok(first.min(second)),
            LocalResult::None => {
                clock = clock
                    .with_second(0)
                    .and_then(|value| value.with_nanosecond(0))
                    .ok_or_else(|| anyhow!("configured local delivery time cannot be represented"))?
                    .checked_add_signed(chrono::Duration::minutes(1))
                    .ok_or_else(|| {
                        anyhow!("configured local delivery time cannot be represented")
                    })?
            }
        }
    }
}

fn next_delivery(now: DateTime<Local>, configured: NaiveTime) -> Result<DateTime<Local>> {
    let today = delivery_on(now.date_naive(), configured)?;
    if today > now {
        Ok(today)
    } else {
        delivery_on(
            now.date_naive()
                .succ_opt()
                .ok_or_else(|| anyhow!("daily delivery date overflow"))?,
            configured,
        )
    }
}

pub async fn wait_for_delivery(configured: Option<NaiveTime>) -> Result<()> {
    let Some(configured) = configured else {
        return std::future::pending().await;
    };
    let wake = next_delivery(Local::now(), configured)?;
    let duration = wake
        .signed_duration_since(Local::now())
        .to_std()
        .unwrap_or_default();
    // This wake is derived only from the user's calendar setting. It is not
    // a review polling interval, work deadline or retry delay.
    tokio::time::sleep(duration).await;
    Ok(())
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
    configured: NaiveTime,
) -> Result<bool> {
    let now = Local::now();
    let Some(through) = reporting_day(now, configured) else {
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
    let client = mimir_core::db::connect(&settings.core.database).await?;
    let report = state::read(&state::resolve(state_dir)?).ok().flatten();
    let mut body = content(
        &client,
        first,
        through,
        latest_status(report.as_ref()),
        &now.format("%Z").to_string(),
    )
    .await?;
    body.push_str(&super::diagnose::summary(report.as_ref()));
    body.push_str("A failed attempt is cleaned up. Correct the reported prerequisite and edit configuration or send SIGHUP to restart the original work. A retry is not confirmation that the problem is resolved.\nHelp: https://github.com/kamysh/mimir/blob/v3.0.0/docs/operations.md\n");
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
    fn calendar_skips_missing_time_and_delivers_once_on_repeated_time() {
        // Run this focused check with TZ=America/Los_Angeles. Other hosts keep
        // their local calendar unchanged and run the general scheduling tests.
        if std::env::var("TZ").as_deref() != Ok("America/Los_Angeles") {
            return;
        }
        let spring = NaiveDate::from_ymd_opt(2026, 3, 8).unwrap();
        let skipped = delivery_on(spring, NaiveTime::from_hms_opt(2, 30, 30).unwrap()).unwrap();
        assert_eq!(skipped.time(), NaiveTime::from_hms_opt(3, 0, 0).unwrap());
        let fall = NaiveDate::from_ymd_opt(2026, 11, 1).unwrap();
        let clock = NaiveTime::from_hms_opt(1, 30, 0).unwrap();
        let LocalResult::Ambiguous(first, second) =
            Local.from_local_datetime(&fall.and_time(clock))
        else {
            panic!("fixture must use a repeated local time");
        };
        assert_eq!(delivery_on(fall, clock).unwrap(), first.min(second));
        let next = next_delivery(first.max(second), clock).unwrap();
        assert_eq!(next.date_naive(), fall.succ_opt().unwrap());
    }

    #[test]
    fn user_chosen_delivery_time_and_catch_up_start() {
        let day = NaiveDate::from_ymd_opt(2026, 10, 11).unwrap();
        let early = Local
            .from_local_datetime(&day.and_hms_opt(14, 14, 0).unwrap())
            .single()
            .unwrap();
        let due = Local
            .from_local_datetime(&day.and_hms_opt(14, 15, 0).unwrap())
            .single()
            .unwrap();
        let configured = NaiveTime::from_hms_opt(14, 15, 0).unwrap();
        assert_eq!(reporting_day(early, configured), None);
        assert_eq!(reporting_day(due, configured), day.pred_opt());
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
            latest_status(Some(&state::Report::new("complete", 1, 1, 0, 0, 0))),
            "batch complete"
        );
    }
}

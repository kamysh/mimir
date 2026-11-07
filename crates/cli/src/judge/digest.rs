use super::{state, RunOutcome};
use anyhow::{anyhow, Result};
use chrono::{DateTime, Local, NaiveDate, NaiveDateTime, TimeZone, Utc};
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

fn reporting_day<T: TimeZone>(
    now: &DateTime<T>,
    time: super::config::DailyTime,
) -> Result<Option<NaiveDate>> {
    let zone = now.timezone();
    let boundary = first_valid_time(now.date_naive().and_time(time.local_time()), |local| {
        zone.from_local_datetime(&local)
            .earliest()
            .map(|value| value.with_timezone(&Utc))
    })?;
    Ok((now.with_timezone(&Utc) >= boundary)
        .then(|| now.date_naive().pred_opt())
        .flatten())
}

/// Resolve a skipped local time by advancing to the first valid second.
/// The resolver chooses the first occurrence when a local time is repeated.
fn first_valid_time(
    mut local: NaiveDateTime,
    mut resolve: impl FnMut(NaiveDateTime) -> Option<DateTime<Utc>>,
) -> Result<DateTime<Utc>> {
    loop {
        if let Some(instant) = resolve(local) {
            return Ok(instant);
        }
        local = local
            .checked_add_signed(chrono::Duration::seconds(1))
            .ok_or_else(|| anyhow!("calendar date overflow; correct the computer clock"))?;
    }
}

fn next_wake<T: TimeZone>(
    now: DateTime<T>,
    time: super::config::DailyTime,
) -> Result<DateTime<Utc>> {
    let date = if reporting_day(&now, time)?.is_none() {
        now.date_naive()
    } else {
        now.date_naive()
            .succ_opt()
            .ok_or_else(|| anyhow!("calendar date overflow"))?
    };
    let zone = now.timezone();
    first_valid_time(date.and_time(time.local_time()), |local| {
        zone.from_local_datetime(&local)
            .earliest()
            .map(|value| value.with_timezone(&Utc))
    })
}

/// One owner remembers admission even when delivery is still pending.
/// Configuration/status updates do not re-admit that day's report.
pub(super) async fn calendar<C, S, F>(
    mut updates: tokio::sync::watch::Receiver<Option<super::notification::CalendarJob>>,
    pending: tokio::sync::mpsc::UnboundedSender<super::notification::Job>,
    clock: C,
    sleep_until: S,
) -> Result<()>
where
    C: Fn() -> DateTime<Local>,
    S: Fn(DateTime<Utc>) -> F,
    F: std::future::Future<Output = ()>,
{
    let mut admitted = None;
    loop {
        let current = updates.borrow_and_update().clone();
        let Some(job) = current else {
            if updates.changed().await.is_err() {
                return Ok(());
            }
            continue;
        };
        let now = clock();
        if reporting_day(&now, job.time)?.is_some() && admitted != Some(now.date_naive()) {
            pending
                .send(super::notification::Job::Digest(job.clone()))
                .map_err(|_| anyhow!("notification worker is unavailable; restart the watcher"))?;
            admitted = Some(now.date_naive());
        }
        let wake = next_wake(now, job.time)?;
        tokio::select! {
            changed = updates.changed() => if changed.is_err() { return Ok(()); },
            _ = sleep_until(wake) => (),
        }
    }
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
    email: &mimir_notifications::config::EmailConfig,
    database: &mimir_core::config::DatabaseConfig,
    state_dir: Option<&Path>,
    run: &RunOutcome,
    time: super::config::DailyTime,
) -> Result<bool> {
    let now = Local::now();
    let Some(through) = reporting_day(&now, time)? else {
        return Ok(false);
    };
    if !email.enabled {
        return Ok(false);
    }
    let path = state::resolve(state_dir)?;
    let notifier = Notifier::new(email, path)?;
    let cursor = notifier.digest_state()?;
    let Some(first) = first_day(cursor.through_day.as_deref(), through)? else {
        return Ok(false);
    };
    if (now.timestamp().max(0) as u64) < cursor.next_due {
        return Ok(cursor.last_attempt_failed);
    }
    let client = mimir_core::db::connect(database).await?;
    let mut body = content(
        &client,
        first,
        through,
        latest_status(run),
        &now.format("%Z").to_string(),
    )
    .await?;
    let report = state::read(&state::resolve(state_dir)?).ok().flatten();
    body.push_str(&super::diagnose::summary(report.as_ref()));
    body.push_str("After an unresolved prerequisite, the watcher waits for a configuration correction or explicit SIGHUP retry. The running watcher prints the retry command. A retry is not confirmation that the problem is resolved.\nHelp: https://github.com/kamysh/mimir/blob/main/docs/operations.md\n");
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
    fn configured_boundary_and_catch_up_start() {
        let time = super::super::config::DailyTime {
            hour: 9,
            minute: 17,
        };
        let day = NaiveDate::from_ymd_opt(2026, 10, 11).unwrap();
        let early = Local
            .from_local_datetime(&day.and_hms_opt(9, 16, 59).unwrap())
            .single()
            .unwrap();
        let due = Local
            .from_local_datetime(&day.and_hms_opt(9, 17, 0).unwrap())
            .single()
            .unwrap();
        assert_eq!(reporting_day(&early, time).unwrap(), None);
        assert_eq!(reporting_day(&due, time).unwrap(), day.pred_opt());
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

    #[test]
    fn skipped_time_uses_the_first_valid_second_and_repeats_use_the_first_instant() {
        let date = NaiveDate::from_ymd_opt(2026, 3, 8).unwrap();
        let missing = date.and_hms_opt(2, 30, 0).unwrap();
        let valid = date.and_hms_opt(3, 0, 27).unwrap();
        let instant =
            first_valid_time(missing, |local| (local >= valid).then(|| local.and_utc())).unwrap();
        assert_eq!(instant.naive_utc(), valid);
        let earlier = missing.and_utc();
        let later = earlier + chrono::Duration::hours(1);
        assert_eq!(
            first_valid_time(missing, |_| chrono::LocalResult::Ambiguous(earlier, later)
                .earliest())
            .unwrap(),
            earlier
        );
    }

    #[test]
    fn repeated_clock_hour_never_schedules_an_already_elapsed_first_occurrence() {
        #[derive(Clone, Copy)]
        struct RepeatedHour;
        impl TimeZone for RepeatedHour {
            type Offset = chrono::FixedOffset;
            fn from_offset(_: &Self::Offset) -> Self {
                Self
            }
            fn offset_from_local_date(
                &self,
                date: &NaiveDate,
            ) -> chrono::LocalResult<Self::Offset> {
                self.offset_from_local_datetime(&date.and_hms_opt(0, 0, 0).unwrap())
            }
            fn offset_from_local_datetime(
                &self,
                local: &NaiveDateTime,
            ) -> chrono::LocalResult<Self::Offset> {
                let day = NaiveDate::from_ymd_opt(2026, 11, 1).unwrap();
                let first = chrono::FixedOffset::west_opt(4 * 3600).unwrap();
                let second = chrono::FixedOffset::west_opt(5 * 3600).unwrap();
                if *local < day.and_hms_opt(1, 0, 0).unwrap() {
                    chrono::LocalResult::Single(first)
                } else if *local < day.and_hms_opt(2, 0, 0).unwrap() {
                    chrono::LocalResult::Ambiguous(first, second)
                } else {
                    chrono::LocalResult::Single(second)
                }
            }
            fn offset_from_utc_date(&self, date: &NaiveDate) -> Self::Offset {
                self.offset_from_utc_datetime(&date.and_hms_opt(0, 0, 0).unwrap())
            }
            fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> Self::Offset {
                let boundary = NaiveDate::from_ymd_opt(2026, 11, 1)
                    .unwrap()
                    .and_hms_opt(6, 0, 0)
                    .unwrap();
                chrono::FixedOffset::west_opt(if *utc < boundary { 4 * 3600 } else { 5 * 3600 })
                    .unwrap()
            }
        }
        let day = NaiveDate::from_ymd_opt(2026, 11, 1).unwrap();
        let time = super::super::config::DailyTime {
            hour: 1,
            minute: 30,
        };
        let before = day
            .and_hms_opt(5, 10, 0)
            .unwrap()
            .and_utc()
            .with_timezone(&RepeatedHour);
        let repeated = day
            .and_hms_opt(6, 10, 0)
            .unwrap()
            .and_utc()
            .with_timezone(&RepeatedHour);
        assert_eq!(reporting_day(&before, time).unwrap(), None);
        assert_eq!(reporting_day(&repeated, time).unwrap(), day.pred_opt());
        let wake = next_wake(repeated, time).unwrap();
        assert!(wake > repeated.with_timezone(&Utc));
        assert_eq!(
            wake.with_timezone(&RepeatedHour).date_naive(),
            day.succ_opt().unwrap()
        );
    }

    #[tokio::test]
    async fn idle_calendar_queues_once_without_delivery_or_review_events() {
        use std::{
            future::{poll_fn, Future},
            sync::{Arc, Mutex},
        };
        let day = NaiveDate::from_ymd_opt(2026, 11, 7).unwrap();
        let at = |hour, minute| {
            Local
                .from_local_datetime(&day.and_hms_opt(hour, minute, 0).unwrap())
                .single()
                .unwrap()
        };
        let now = Arc::new(Mutex::new(at(10, 16)));
        let wake = Arc::new(tokio::sync::Notify::new());
        let job = super::super::notification::CalendarJob {
            email: mimir_notifications::config::EmailConfig::default(),
            database: toml::from_str("host='unused'\nport=5432\ndbname='unused'\nuser='unused'\n")
                .unwrap(),
            path: std::env::temp_dir(),
            outcome: RunOutcome {
                code: 0,
                degraded: false,
                idle: true,
            },
            time: super::super::config::DailyTime {
                hour: 10,
                minute: 17,
            },
        };
        let (update, received) = tokio::sync::watch::channel(Some(job.clone()));
        let (pending, mut jobs) = tokio::sync::mpsc::unbounded_channel();
        let clock = now.clone();
        let notify = wake.clone();
        let task = calendar(
            received,
            pending,
            move || *clock.lock().unwrap(),
            move |_| {
                let notify = notify.clone();
                async move { notify.notified().await }
            },
        );
        tokio::pin!(task);
        assert!(poll_fn(|cx| std::task::Poll::Ready(task.as_mut().poll(cx).is_pending())).await);
        assert!(jobs.try_recv().is_err());
        *now.lock().unwrap() = at(10, 17);
        wake.notify_one();
        assert!(poll_fn(|cx| std::task::Poll::Ready(task.as_mut().poll(cx).is_pending())).await);
        assert!(matches!(
            jobs.try_recv().unwrap(),
            super::super::notification::Job::Digest(_)
        ));
        // The delivery consumer remains stalled. Status/configuration updates
        // cannot enqueue that day again or cause a ready-future busy loop.
        update.send(Some(job.clone())).unwrap();
        assert!(poll_fn(|cx| std::task::Poll::Ready(task.as_mut().poll(cx).is_pending())).await);
        assert!(jobs.try_recv().is_err());
        update.send(None).unwrap();
        assert!(poll_fn(|cx| std::task::Poll::Ready(task.as_mut().poll(cx).is_pending())).await);
        *now.lock().unwrap() = at(10, 17) + chrono::Duration::days(1);
        wake.notify_one();
        assert!(poll_fn(|cx| std::task::Poll::Ready(task.as_mut().poll(cx).is_pending())).await);
        assert!(
            jobs.try_recv().is_err(),
            "disabled scheduling must stay disabled"
        );
        update.send(Some(job)).unwrap();
        assert!(poll_fn(|cx| std::task::Poll::Ready(task.as_mut().poll(cx).is_pending())).await);
        assert!(matches!(
            jobs.try_recv().unwrap(),
            super::super::notification::Job::Digest(_)
        ));
        assert!(jobs.try_recv().is_err());
        drop(update);
        task.await.unwrap();
    }
}

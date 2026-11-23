use super::{
    api, config, harness,
    mcp::Client,
    notification,
    runner::{self, UnavailableBackend},
    state::{self, DeferredReview, State},
};
use anyhow::{anyhow, bail, ensure, Context, Result};
use mimir_core::learning::{ExperienceState, Review};
use serde_json::{json, Value};
use std::path::Path;
use uuid::Uuid;

pub(super) async fn run(
    config_path: Option<&Path>,
    state_path: Option<&Path>,
    id: Uuid,
    revision: i64,
    retry: bool,
    review: Option<&Path>,
) -> Result<i32> {
    ensure!(
        revision > 0,
        "Use the positive source revision shown in the alert."
    );
    let settings = config::load(config_path)?;
    let directory = state::resolve(state_path)?;
    let mut client = Client::start(
        &settings.judge.mcp_command,
        &settings.judge.mcp_args,
        &settings.path,
    )
    .await?;
    let value = client.tool("get_experience", json!({"id":id})).await?;
    ensure!(!value.is_null(), "The experience is unavailable. Check the configuration and the experience UUID in the alert.");
    let current: ExperienceState = serde_json::from_value(value)?;
    ensure!(
        current.experience.id == id && settings.judge.project.as_ref()
            .is_none_or(|project| *project == current.experience.project),
        "The experience is outside this judge's scope. Select the configuration that owns the review."
    );
    ensure!(
        current.revision == revision,
        "Source revision {revision} is no longer current. The current revision is {}. Review that source before applying a correction.",
        current.revision
    );

    let held = state::read(&directory)?.and_then(|report| {
        report
            .deferred_reviews
            .into_iter()
            .find(|held| held.id == id && held.revision == revision)
    });
    if current.reviewed_revision == revision && current.review_revision > 0 {
        let key = DeferredReview {
            id,
            revision,
            repair: None,
        };
        announce_confirmed(&settings, &directory, &key);
        return Ok(0);
    }
    let held = held.ok_or_else(|| anyhow!(
        "No deferred review for this revision. The watcher can select it normally. Use `mimir judge status` to inspect the latest attempt."
    ))?;
    let command = notification::repair_command(&settings, &directory, &held);

    if let Some(path) = review {
        let mut corrected: Review = serde_json::from_slice(&tokio::fs::read(path).await?).context(
            "Supply a complete corrected review JSON object using the review_experience schema",
        )?;
        ensure!(
            corrected.experience_id == id && corrected.experience_revision == revision,
            "The corrected review must name the experience UUID and source revision from this repair case."
        );
        corrected.reviewer = "mimir-operator".into();
        let result = client
            .tool(
                "review_experience",
                json!({
                    "review":corrected,
                    "expected_review_revision":current.review_revision
                }),
            )
            .await;
        // Even a failed response may follow a confirmed write. Use the same
        // readback contract as the watcher before honoring the response.
        match runner::observe(&mut client, &current).await {
            Ok("confirmed") => announce_confirmed(&settings, &directory, &held),
            Ok("corrected") => bail!("The source changed during repair. Read the current revision and prepare a fresh review."),
            Ok("pending") => match result {
                Ok(value) => bail!("The review remains pending. Correct the reported problem and submit the review again: {value}"),
                Err(error) => bail!("The review remains pending. Correct the review and submit it again: {error:#}"),
            },
            _ => bail!("PostgreSQL has not confirmed the repair. Run the repair command again to read the saved outcome before resubmitting."),
        }
        return Ok(0);
    }

    if retry {
        client.stop().await;
        // Use a separate lock for this explicit repair. The main
        // watcher can keep processing other work; PostgreSQL checks revisions.
        let path = directory.join("repair").join(format!("{id}-{revision}"));
        let state =
            State::lock(path.clone())?.ok_or_else(|| anyhow!("This repair is already running."))?;
        let report = match settings.llm.backend {
            config::Backend::Api => match api::ApiBackend::new(&settings.llm)? {
                Some(mut backend) => {
                    runner::run_selected(&settings, &state, &mut backend, Some(current)).await
                }
                None => {
                    runner::run_selected(&settings, &state, &mut UnavailableBackend, Some(current))
                        .await
                }
            },
            _ => {
                let mut backend = harness::Harness::new(&settings.llm)?;
                runner::run_selected(&settings, &state, &mut backend, Some(current)).await
            }
        };
        if report.confirmed == 1 {
            announce_confirmed(&settings, &directory, &held);
            return Ok(0);
        }
        if let Some(diagnostic) = report.diagnostic {
            println!("Repair attempt: {}", diagnostic.detail);
        } else if let Some(detail) = report.failure_detail {
            println!("Repair attempt: {detail}");
        }
        if let Some(id) = report.diagnostics_id {
            println!(
                "Transcript: {}",
                notification::diagnostic_command(&settings.path, &directory, id)
            );
        } else if report.transcripts_pending != 0 {
            eprintln!(
                "The transcript could not be saved to PostgreSQL before this command exited."
            );
        }
        if report.corrected > 0 {
            bail!("The source changed during repair. Read the current revision and prepare a fresh review.");
        }
        eprintln!("The review remains pending. Run {command} to inspect the case and submit a corrected review.");
        return Ok(super::INCOMPLETE);
    }

    println!(
        "Experience {id}, source revision {revision}, project '{}'.",
        current.experience.project
    );
    if let Some(case) = &held.repair {
        println!("Problem: {}\nDetails: {}", case.explanation, case.detail);
    }
    match super::transcript::for_revision(&settings.core.database, id, revision).await {
        Ok(attempts) => {
            for attempt in attempts {
                println!(
                    "Transcript: {}",
                    notification::diagnostic_command(&settings.path, &directory, attempt)
                );
            }
        }
        Err(_) => eprintln!(
            "Cannot read the failed-review transcripts; check PostgreSQL and retry inspection."
        ),
    }
    println!(
        "Retry from the stored source: {command} --retry\n\
         Apply a complete corrected review: {command} --review PATH\n\
         For an unresolved candidate, choose an eligible existing belief, supply a supported declaration, or explicitly remove the unsupported reference. Use the same experience UUID and source revision in the corrected review."
    );
    Ok(0)
}

fn announce_confirmed(settings: &config::RuntimeConfig, directory: &Path, review: &DeferredReview) {
    if let Err(error) = notification::review_recovered(settings, directory, review) {
        eprintln!("The review was confirmed. The recovery email could not be queued: {error:#}");
    }
    let result: Value = json!({"status":"confirmed","experience_id":review.id,"experience_revision":review.revision});
    println!("{result}");
}

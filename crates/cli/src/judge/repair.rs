use super::{
    api, config, harness,
    mcp::Client,
    notification,
    runner::{self, UnavailableBackend},
    state::{self, DeferredReview, State},
};
use anyhow::{anyhow, bail, ensure, Context, Result};
use mimir_core::{
    assessment::{Assessment, LearningItem},
    graph::MemoryType,
    learning::{BeliefTarget, Candidate, ExperienceState, Review},
    learning_sources::CoverageStatus,
};
use serde_json::json;
use std::io::{self, Write};
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
        announce_confirmed(&settings, &directory, &key, review.is_none() && !retry);
        return Ok(0);
    }
    let held = held.ok_or_else(|| anyhow!(
        "No deferred review for this revision. The watcher can select it normally. Use `mimir judge status` to inspect the latest attempt."
    ))?;
    let command = notification::repair_command(&settings, &directory, &held);

    if let Some(path) = review {
        let corrected: Review = serde_json::from_slice(&tokio::fs::read(path).await?).context(
            "Supply a complete corrected review JSON object using the review_experience schema",
        )?;
        ensure!(
            corrected.experience_id == id && corrected.experience_revision == revision,
            "The corrected review must name the experience UUID and source revision from this repair case."
        );
        submit(&mut client, &current, corrected).await?;
        announce_confirmed(&settings, &directory, &held, false);
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
            announce_confirmed(&settings, &directory, &held, false);
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

    let Some(draft) = rejected_draft(&settings, &held).await? else {
        bail!("This failed attempt contains no submitted review to edit. Start a fresh attempt with {command} --retry.");
    };
    println!("Repairing the failed review for source revision {revision}.");
    let corrected = interactive(&mut client, &current, draft).await?;
    let Some(corrected) = corrected else {
        println!("Repair cancelled. The review is still pending.");
        return Ok(super::INCOMPLETE);
    };
    submit(&mut client, &current, corrected).await?;
    announce_confirmed(&settings, &directory, &held, true);
    Ok(0)
}

async fn submit(client: &mut Client, current: &ExperienceState, mut review: Review) -> Result<()> {
    review.reviewer = "mimir-operator".into();
    review
        .validate()
        .context("The edited review is still invalid and has not been saved")?;
    let result = client
        .tool(
            "review_experience",
            json!({
                "review":review, "expected_review_revision":current.review_revision
            }),
        )
        .await;
    let submitted = result.as_ref().is_ok_and(|receipt| {
        receipt["experience"]["id"] == json!(current.experience.id)
            && receipt["revision"] == current.revision
            && receipt["reviewed_revision"] == current.revision
            && receipt["review_revision"]
                .as_i64()
                .is_some_and(|revision| revision > current.review_revision)
    });
    match runner::observe(client, current).await {
        Ok("confirmed") if submitted => Ok(()),
        Ok("confirmed") => bail!("A review is already saved for this revision. Inspect the saved review before applying your edits again."),
        Ok("corrected") => bail!("The source changed during repair. Open the current source revision before applying a correction."),
        Ok("pending") => match result {
            Ok(value) => bail!("The review is still pending. {}", value["reason"].as_str().unwrap_or("Mimir did not confirm a save.")),
            Err(error) => bail!("The review is still pending. {error}"),
        },
        _ => bail!("PostgreSQL has not confirmed the repair. Reopen the repair command to read the stored outcome before resubmitting."),
    }
}

async fn rejected_draft(
    settings: &config::RuntimeConfig,
    held: &DeferredReview,
) -> Result<Option<Review>> {
    let db = &settings.core.database;
    for id in super::transcript::for_revision(db, held.id, held.revision).await? {
        let Some(value) = super::transcript::lookup(db, Some(id), false).await? else {
            continue;
        };
        if value["trace"]["experience_id"] != json!(held.id)
            || value["trace"]["source_revision"] != held.revision
        {
            continue;
        }
        if let Some(events) = value["trace"]["transcript"]["events"].as_array() {
            for event in events.iter().rev().filter(|event| {
                event["kind"] == "tool_request" && event["tool"] == "review_experience"
            }) {
                if let Ok(review) =
                    serde_json::from_value::<Review>(event["detail"]["review"].clone())
                {
                    if review.experience_id == held.id
                        && review.experience_revision == held.revision
                    {
                        return Ok(Some(review));
                    }
                }
            }
        }
    }
    Ok(None)
}

fn prompt(label: &str) -> Result<Option<String>> {
    print!("{label}");
    io::stdout().flush()?;
    let mut answer = String::new();
    Ok((io::stdin().read_line(&mut answer)? != 0).then(|| answer.trim().to_owned()))
}

fn refers_to(assessment: &Assessment, item: &LearningItem) -> bool {
    item.id.is_some_and(|id| assessment.item_ids.contains(&id))
        || item
            .key
            .as_ref()
            .is_some_and(|key| assessment.item_keys.contains(key))
}

fn remove_assessment(review: &mut Review, index: usize) -> Vec<String> {
    let removed = review.assessments.remove(index);
    let mut changed = Vec::new();
    for coverage in &mut review.source_coverage {
        if coverage.status == CoverageStatus::Complete
            && review.extracted_items.iter().any(|item| {
                item.source_ref == coverage.source_ref
                    && refers_to(&removed, item)
                    && !review
                        .assessments
                        .iter()
                        .any(|other| refers_to(other, item))
            })
        {
            coverage.status = CoverageStatus::Unresolved;
            coverage.reason.push_str(" The operator removed an assessment with an invalid target. Extracted statements still need assessment.");
            changed.push(coverage.source_ref.clone());
        }
    }
    changed
}

async fn choose_belief(client: &mut Client, selected: &ExperienceState) -> Result<Option<Uuid>> {
    let Some(query) = prompt("Search this project's stored beliefs by text (blank to go back) > ")?
    else {
        return Ok(None);
    };
    if query.is_empty() {
        return Ok(None);
    }
    let project = &selected.experience.project;
    let response = client
        .tool("query_relevant", json!({"context":query,"project":project}))
        .await?;
    let matches = response
        .as_array()
        .or_else(|| response["beliefs"].as_array())
        .ok_or_else(|| {
            anyhow!(
                "Cannot search stored beliefs. {}",
                response["reason"]
                    .as_str()
                    .unwrap_or("Check the database connection.")
            )
        })?;
    for belief in matches {
        let (Some(id), Some(content)) = (belief["id"].as_str(), belief["content"].as_str()) else {
            continue;
        };
        if belief["project"] != *project
            || !matches!(
                serde_json::from_value(belief["memory_type"].clone()),
                Ok(MemoryType::Fact | MemoryType::Experiential)
            )
        {
            continue;
        }
        println!("Stored belief: {content}");
        match prompt("Use this belief? [y]es, [n]ext, [b]ack > ")?.as_deref() {
            Some("y" | "yes") => return Ok(Some(id.parse()?)),
            Some("n" | "next") => {}
            _ => return Ok(None),
        }
    }
    println!("No further matching beliefs are eligible for assessment in this project.");
    Ok(None)
}

async fn interactive(
    client: &mut Client,
    current: &ExperienceState,
    mut draft: Review,
) -> Result<Option<Review>> {
    let mut changes = 0;
    while let Some((index, key)) =
        draft
            .assessments
            .iter()
            .enumerate()
            .find_map(|(index, assessment)| {
                let BeliefTarget::Candidate { candidate_key } = &assessment.target else {
                    return None;
                };
                (!draft.candidates.iter().any(|candidate| {
                    matches!(candidate,
            Candidate::Belief {key, ..} if key == candidate_key)
                }))
                .then(|| (index, candidate_key.clone()))
            })
    {
        let assessment = &draft.assessments[index];
        println!("\nAssessment: {}", assessment.rationale);
        if let Some(Candidate::Pattern {
            situation,
            approach,
            ..
        }) = draft
            .candidates
            .iter()
            .find(|candidate| candidate.key() == key)
        {
            println!("It points to a proposed procedure, but an assessment needs a belief.\nSituation: {situation}\nApproach: {approach}");
        } else {
            println!("It points to {key:?}, which the judge never defined as a belief.");
        }
        for item in draft
            .extracted_items
            .iter()
            .chain(&current.experience.learning_items)
            .filter(|item| refers_to(assessment, item))
        {
            println!("Cited statement by {}: {}", item.actor, item.statement);
        }
        for index in &assessment.evidence_indices {
            if let Some(evidence) = current.experience.evidence.get(*index) {
                println!("Evidence: {evidence}");
            }
        }
        match prompt("[r]emove assessment, [b]elief search, [q]uit > ")?.as_deref() {
            Some("r" | "remove") => {
                let mut edited = draft.clone();
                let sources = remove_assessment(&mut edited, index);
                println!("This removes only the assessment. The extracted statements and proposed procedures are kept.");
                if !sources.is_empty() {
                    println!(
                        "These sources will be marked as still needing assessment: {}",
                        sources.join(", ")
                    );
                }
                if matches!(
                    prompt("Keep this edit? [y]es / [n]o > ")?.as_deref(),
                    Some("y" | "yes")
                ) {
                    draft = edited;
                    changes += 1;
                }
            }
            Some("b" | "belief") => {
                if let Some(belief_id) = choose_belief(client, current).await? {
                    draft.assessments[index].target = BeliefTarget::Existing { belief_id };
                    changes += 1;
                }
            }
            Some("q" | "quit") | None => return Ok(None),
            _ => println!("Choose r, b, or q."),
        }
    }
    ensure!(changes > 0, "This draft has no invalid assessment target the guided repair can edit. Use diagnostics to see why the attempt ended.");
    println!("Ready to submit {changes} confirmed assessment edits. Other review entries will be preserved.");
    let unresolved = draft
        .source_coverage
        .iter()
        .filter(|source| source.status == CoverageStatus::Unresolved)
        .count();
    if unresolved > 0 {
        println!("{unresolved} source records will still be marked as needing assessment after the save.");
    }
    Ok(matches!(
        prompt("Save the corrected review? Type yes to save > ")?.as_deref(),
        Some("yes")
    )
    .then_some(draft))
}

fn announce_confirmed(
    settings: &config::RuntimeConfig,
    directory: &Path,
    review: &DeferredReview,
    human: bool,
) {
    if let Err(error) = notification::review_recovered(settings, directory, review) {
        eprintln!("The review was confirmed. The recovery email could not be queued: {error:#}");
    }
    if human {
        println!(
            "PostgreSQL confirmed the review for source revision {}.",
            review.revision
        );
    } else {
        let result = json!({"status":"confirmed","experience_id":review.id,"experience_revision":review.revision});
        println!("{result}");
    }
}

//! Registered review preparation owners and one atomic review publication.
use super::{
    AgeStore, OperationBindingRequest, OperationOutcome, OperationPlan, RegisteredStep,
    StepDecision, StepReceipt,
};
use crate::{
    graph::{prior_from, Belief, Probability},
    interaction::Location,
    learning::{Candidate, Review},
    operation_catalogue::CommitSite,
    preparation::{PreparationRequired, PreparedBelief},
    validation::{Code, Segment},
};
use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use std::collections::HashMap;
use uuid::Uuid;

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Arguments {
    review: Review,
    expected_review_revision: i64,
}

fn original(request: &OperationBindingRequest) -> Result<Arguments> {
    decode_original(request).map_err(|error| PreparationRequired::bound_request(Code::MalformedInput,
        format!("The saved review request cannot be prepared: {error:#}. Read this token's original binding and open the user dialog before changing it. No review was published.")).into())
}

pub(crate) fn admit_request(request: &OperationBindingRequest) -> Result<()> {
    // This request is not bound yet. Keep typed pure-validation faults rather
    // than converting them into a saved-request repair message.
    decode_original(request).map(|_| ())
}

fn decode_original(request: &OperationBindingRequest) -> Result<Arguments> {
    anyhow::ensure!(
        request.operation() == "review_experience",
        "Read the original review_experience token and binding; this token names another operation"
    );
    crate::preparation::validate_operation_settings(request.settings())?;
    let args: Arguments = mimir_json::decode_ref(request.arguments())
        .context("Read the saved review and expected_review_revision; do not replace candidate declarations or their keys")?;
    args.review
        .validate()
        .map_err(crate::validation::Refusal::validation)?;
    anyhow::ensure!((0..i64::MAX).contains(&args.expected_review_revision),
        "expected_review_revision must be nonnegative and leave one representable revision increment");
    Ok(args)
}

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Allocation {
    id: Uuid,
    created_at: DateTime<Utc>,
    project: String,
}

pub(crate) enum ReviewPublicationState {
    Resolved(StepDecision),
    Preparing {
        review: Review,
        expected: i64,
        owners: HashMap<String, Belief>,
        final_step: RegisteredStep,
    },
}

impl AgeStore {
    /// Saved completion is authoritative before current settings or providers.
    pub(crate) async fn resume_review_operation(
        &self,
        plan: &OperationPlan,
        current_settings: &serde_json::Value,
    ) -> Result<ReviewPublicationState> {
        let request = plan.original_request();
        anyhow::ensure!(
            request.operation() == "review_experience",
            "Use the original review_experience operation token"
        );
        let steps = plan.steps();
        let final_step = steps
            .last()
            .filter(|s| s.description().site == CommitSite::ReviewPublication.name())
            .context("Read the original plan: its final step must publish the prepared review")?
            .clone();
        match self.read_operation_outcome(plan.operation_token(), Some(request)).await? {
            OperationOutcome::Completed { outcome, .. } => return Ok(ReviewPublicationState::Resolved(
                StepDecision::Done(StepReceipt { operation_token:plan.operation_token(), step:final_step.id().to_owned(),
                    reply:mimir_json::Document::new(mimir_json::clone_value(outcome.reply())) }))),
            OperationOutcome::Cancelled { cancellation, .. } => return Ok(ReviewPublicationState::Resolved(StepDecision::Cancelled(cancellation))),
            OperationOutcome::ChangedRequest(binding) => return Ok(ReviewPublicationState::Resolved(StepDecision::ChangedRequest(binding))),
            OperationOutcome::NeedsRecovery { reason, .. } => return Ok(ReviewPublicationState::Resolved(StepDecision::NeedsRecovery(reason))),
            OperationOutcome::Pending { .. } => {},
            _ => return Ok(ReviewPublicationState::Resolved(StepDecision::NeedsRecovery(
                "Read the original review binding, plan and saved answers before resuming; no new review was published.".into()))),
        }
        let args = original(request)?;
        let keys = args
            .review
            .candidates
            .iter()
            .filter_map(|c| match c {
                Candidate::Belief { key, .. } => Some(key.as_str()),
                _ => None,
            })
            .collect::<Vec<_>>();
        let owner_steps = &steps[..steps.len() - 1];
        anyhow::ensure!(owner_steps.len() == keys.len() && owner_steps.iter().zip(&keys).all(|(step,key)|
            step.description().site == CommitSite::EmbeddingOwnerReservation.name() && step.description().key.as_deref() == Some(*key)),
            "The original review plan must reserve each declared belief key in declaration order, then publish once; read the saved plan rather than inventing new candidate keys");
        let exact_replay = self
            .review_preparation_candidates(&args.review, args.expected_review_revision)
            .await?
            .is_none();
        if !exact_replay && request.settings() != current_settings {
            return Err(PreparationRequired::new(Location::Configuration, vec![], Code::WrongIdentity,
                "The current embedding model differs from this unfinished review's saved settings. Read the original binding and open a user dialog; do not switch models or invent a replacement token.".into()).into());
        }
        let mut owners = HashMap::new();
        for (step, key) in owner_steps.iter().zip(keys) {
            let token = plan.operation_token();
            let allocation = match self.commit_operation_step(step, move |tx, request| Box::pin(async move {
                let args = original(request)?;
                tx.query("SELECT pg_advisory_xact_lock(671942183)", &[]).await?;
                let source = tx.query_opt("SELECT project FROM mimir_experiences WHERE id=$1 AND revision=$2",
                    &[&args.review.experience_id, &args.review.experience_revision]).await?
                    .ok_or_else(|| PreparationRequired::bound_request(Code::StaleRevision,
                        "The original source revision is no longer current. Read the experience and saved review and open a user dialog; no review was published".into()))?;
                let project:String = source.try_get(0)?;
                let row = tx.query_one("INSERT INTO mimir_embedding_owners(project,operation_token) VALUES($1,$2) RETURNING owner_token,reserved_at", &[&project,&token]).await?;
                Ok(mimir_json::to_value(Allocation { id:row.try_get(0)?,created_at:row.try_get(1)?,project })?)
            })).await? {
                StepDecision::Done(answer) => mimir_json::decode_ref::<Allocation>(&answer.reply)
                    .map_err(|error| PreparationRequired::bound_request(Code::MalformedInput,
                        format!("The saved preparation answer for candidate {key:?} cannot be read: {error:#}. Keep token {} and read its original plan, this step's saved answer and diagnostics. Open the user dialog to resolve the stored answer; do not allocate a replacement owner or repeat publication. No review was published.", plan.operation_token())))?,
                other => return Ok(ReviewPublicationState::Resolved(other)),
            };
            let candidate = args
                .review
                .candidates
                .iter()
                .find(|c| c.key() == key)
                .context("Missing original candidate declaration")?;
            let Candidate::Belief {
                content,
                memory_type,
                ..
            } = candidate
            else {
                unreachable!()
            };
            let (alpha, beta) = prior_from(0.5, 0.0);
            owners.insert(
                key.to_owned(),
                Belief {
                    id: allocation.id,
                    content: content.clone(),
                    probability: Probability::new(0.5)?,
                    confidence: Probability::new(0.0)?,
                    alpha,
                    beta,
                    alpha0: alpha,
                    beta0: beta,
                    created_at: allocation.created_at,
                    last_activated_at: allocation.created_at,
                    decay_accounted_at: allocation.created_at,
                    memory_type: *memory_type,
                    project: Some(allocation.project),
                },
            );
        }
        Ok(ReviewPublicationState::Preparing {
            review: args.review,
            expected: args.expected_review_revision,
            owners,
            final_step,
        })
    }

    pub(crate) async fn publish_review_operation(
        &self,
        step: &RegisteredStep,
        prepared: &HashMap<String, PreparedBelief>,
    ) -> Result<StepDecision> {
        original(step.expected())?;
        anyhow::ensure!(
            step.description().site == CommitSite::ReviewPublication.name(),
            "Use the original final prepared-review step"
        );
        let token = step.token();
        let owner_steps = step
            .plan()
            .steps()
            .into_iter()
            .filter(|entry| {
                entry.description().site == CommitSite::EmbeddingOwnerReservation.name()
            })
            .filter_map(|entry| {
                entry
                    .description()
                    .key
                    .clone()
                    .map(|key| (key, entry.id().to_owned()))
            })
            .collect::<HashMap<_, _>>();
        let owner = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        let prepared = prepared.clone();
        self.commit_final_operation_step(step, move |tx, request| Box::pin(async move {
            let args = original(request)?;
            // Reservation is already held. Reject foreign owners without
            // acquiring another reservation in an inverted lock order.
            for (key,value) in &prepared {
                let saved_step = owner_steps.get(key).context("Read the original prepared candidate key; it has no owner step in this review plan")?;
                let saved = tx.query_opt("SELECT reply::text FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2", &[&token,saved_step]).await?
                    .context("Read this candidate's original preparation answer before publishing a review")?;
                let allocation:Allocation = mimir_json::from_str(saved.get(0))?;
                anyhow::ensure!(value.belief.id == allocation.id && value.belief.created_at == allocation.created_at
                    && value.belief.project.as_deref() == Some(&allocation.project),
                    "The prepared candidate does not match its original PostgreSQL allocation; no review was published");
                let linked = tx.query_opt("SELECT operation_token FROM mimir_embedding_owners WHERE owner_token=$1", &[&value.belief.id]).await?
                    .and_then(|row| row.get::<_,Option<Uuid>>(0));
                if linked != Some(token) {
                    return Err(PreparationRequired::new(Location::Arguments,
                        vec![Segment::Key("review".into()),Segment::Key("candidates".into())], Code::WrongIdentity,
                        format!("Prepared candidate {key:?} does not belong to this operation's original owner. Read its saved preparation answer; no review was published.")).into());
                }
            }
            tx.query("SELECT pg_advisory_xact_lock(671942183)", &[]).await?;
            let result = owner.review_experience_in(tx, &args.review, args.expected_review_revision, &prepared).await?;
            // A concurrent exact review can make our own preparation unused.
            // Preserve its result and every other token's owner/receipt.
            tx.execute("DELETE FROM mimir_embedding_owners WHERE operation_token=$1", &[&token]).await?;
            let reply = mimir_json::to_value(result)?;
            Ok((reply.clone(),reply))
        })).await
    }
}

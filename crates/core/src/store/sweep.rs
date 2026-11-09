//! An entire selected deletion set and its original answer share one commit.
//! Selection is admitted under the writer lock; no partially durable set exists.
use super::{age_query_rows, AgeStore, OperationBindingRequest, RegisteredStep, StepDecision};
use crate::{
    config::RetirementPolicy,
    interaction::{CorrectionItem, Location, NeedsInput},
    operation_catalogue::CommitSite,
    validation::{Code, Fault, Segment},
};
use anyhow::{ensure, Context, Result};
use serde::Deserialize;
use serde_json::Value;
use std::collections::{HashMap, HashSet};
use tokio_postgres::Transaction;
use uuid::Uuid;

#[derive(Debug)]
pub struct SweepPolicyIssue(NeedsInput);
impl SweepPolicyIssue {
    pub fn correction(&self) -> &NeedsInput {
        &self.0
    }
}
impl std::fmt::Display for SweepPolicyIssue {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.write_str(&self.0.issues()[0].fault().message)
    }
}
impl std::error::Error for SweepPolicyIssue {}

pub(crate) fn policy_issue(message: String) -> anyhow::Error {
    SweepPolicyIssue(NeedsInput::new(CorrectionItem::new(Location::Configuration,
        Fault { path: vec![Segment::Key("retirement".into()), Segment::Key("grace_hours".into())],
            code: Code::StaleRevision, message },
        "The same user-configured retirement policy that this unfinished operation originally bound.".into(),
        "Read the original binding and current [retirement].grace_hours. Open the user dialog to restore the original policy or explicitly cancel pending work before starting a separate operation. Do not rewrite the binding, invent a period, send a per-call override or cancel automatically.".into())
        .expect("sweep policy correction describes its source and repair"), vec![])
        .expect("sweep policy correction has one concrete issue")).into()
}

pub(crate) fn settings(policy: &RetirementPolicy) -> Value {
    serde_json::json!({"retirement":{"grace_hours":policy.grace_hours()}})
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Arguments {
    #[serde(default = "default_threshold")]
    pub prob_threshold: f64,
    pub project: Option<String>,
}
fn default_threshold() -> f64 {
    0.3
}

pub(crate) fn validate_threshold(threshold: f64) -> Result<()> {
    if !threshold.is_finite() || !(0.0..=1.0).contains(&threshold) {
        return Err(crate::validation::Refusal::invalid(Code::InvalidNumber,
            vec![Segment::Key("prob_threshold".into())],
            "Supply a finite probability between 0 and 1 inclusive; no beliefs were read or deleted.").into());
    }
    Ok(())
}

pub(crate) fn check_policy(
    request: &OperationBindingRequest,
    current: &RetirementPolicy,
) -> Result<Arguments> {
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Settings {
        retirement: Policy,
    }
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Policy {
        grace_hours: f64,
    }
    ensure!(
        request.operation() == "sweep_expired_defeated",
        "Read the original sweep binding before deleting beliefs"
    );
    let arguments: Arguments = mimir_json::decode_ref(request.arguments()).context(
        "Read the original sweep scope and probability threshold; do not replace its arguments",
    )?;
    validate_threshold(arguments.prob_threshold)?;
    let original: Settings = mimir_json::decode_ref(request.settings()).map_err(|_| policy_issue(
        "This unfinished sweep has no valid original user-owned retention policy. No selection was made and nothing was deleted.".into()))?;
    if original.retirement.grace_hours != current.grace_hours() {
        return Err(policy_issue(format!("This unfinished sweep originally used {} hours, while the currently configured policy is {} hours. It is paused without selecting or deleting beliefs.",
            original.retirement.grace_hours, current.grace_hours())));
    }
    Ok(arguments)
}

impl AgeStore {
    async fn sweep_locked_in(
        &self,
        tx: &Transaction<'_>,
        threshold: f64,
        project: Option<&str>,
        policy: &RetirementPolicy,
    ) -> Result<Vec<Uuid>> {
        validate_threshold(threshold)?;
        let observed = Self::posterior_time_on(tx.client()).await?;
        let edges = self.defeat_clocks_on(tx.client(), project).await?;
        let beliefs = match project {
            Some(project) => {
                self.list_beliefs_by_project_on(tx.client(), project)
                    .await?
            }
            None => self.list_beliefs_on(tx.client()).await?,
        };
        let beliefs: HashMap<_, _> = beliefs
            .into_iter()
            .map(|belief| (belief.id, belief))
            .collect();
        let mut selected = crate::inference::InferenceEngine::new().find_expired_defeated(
            &edges,
            &beliefs,
            observed,
            threshold,
            policy.duration(),
        );
        selected.sort_unstable();
        if selected.is_empty() {
            return Ok(selected);
        }
        let graph = &self.graph_name;
        let parameters = mimir_json::to_string(&serde_json::json!({"ids":selected}))?;
        let children = format!("PREPARE age_sweep_children(agtype) AS SELECT id::text FROM ag_catalog.cypher('{graph}', $$ MATCH (a:Belief)-[r]->(b:Belief) WHERE a.id IN $ids RETURN b.id $$, $1) AS (id ag_catalog.agtype)");
        let affected: HashSet<Uuid> =
            age_query_rows(tx.client(), "age_sweep_children", &children, &parameters)
                .await?
                .iter()
                .map(|row| -> Result<Uuid> {
                    Ok(Uuid::parse_str(
                        row.get(0)
                            .context("A selected belief child has no stored UUID")?,
                    )?)
                })
                .collect::<Result<_>>()?;
        tx.execute(
            "UPDATE mimir_review_candidates SET retired=true WHERE node_id=ANY($1)",
            &[&selected],
        )
        .await?;
        let remove = format!("PREPARE age_sweep_delete(agtype) AS SELECT * FROM ag_catalog.cypher('{graph}', $$ MATCH (n:Belief) WHERE n.id IN $ids DETACH DELETE n RETURN 1 $$, $1) AS (deleted ag_catalog.agtype)");
        let removed = age_query_rows(tx.client(), "age_sweep_delete", &remove, &parameters).await?;
        ensure!(removed.len() == selected.len(), "A selected target changed while the sweep owned its publication transaction. Read the original operation and stored beliefs before retrying; no final count was published");
        tx.execute(
            "DELETE FROM public.belief_embeddings WHERE belief_id=ANY($1)",
            &[&selected],
        )
        .await?;
        let publication_time = Self::posterior_time_on(tx.client()).await?;
        self.recompute_learning_at(tx, None, affected, publication_time)
            .await?;
        tx.query(
            "SELECT pg_notify('mimir_embedding_owners_changed', '')",
            &[],
        )
        .await?;
        Ok(selected)
    }

    /// Existing callers also get the complete transaction; operation-token
    /// routing supplies the original saved answer through the registered path.
    pub async fn sweep_expired_defeated(
        &self,
        threshold: f64,
        project: Option<&str>,
        policy: &RetirementPolicy,
    ) -> Result<usize> {
        let mut client = self.client.lock().await;
        let tx = super::learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        match self.sweep_locked_in(&tx, threshold, project, policy).await {
            Ok(selected) => {
                tx.commit().await?;
                Ok(selected.len())
            }
            Err(original) => {
                if let Err(rollback) = tx.rollback().await {
                    return Err(anyhow::anyhow!("Sweep did not finish and rollback was not acknowledged: {rollback:#}. Read the stored beliefs before deciding whether to retry. Original cause: {original:#}"));
                }
                Err(original)
            }
        }
    }

    /// Selection, dependent cleanup, posteriors and both original answers are
    /// one publication. Readback is handled before current policy validation.
    pub async fn sweep_operation(
        &self,
        step: &RegisteredStep,
        policy: &RetirementPolicy,
    ) -> Result<StepDecision> {
        ensure!(step.description().site == CommitSite::BeliefDeletion.name() && step.description().key.is_none()
            && step.plan().steps().len() == 1, "Use the current single-publication sweep plan; do not reinterpret a historical selection");
        let owner = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        let current = policy.clone();
        self.commit_final_operation_step(step, move |tx, original| {
            Box::pin(async move {
                // Current policy is checked under the writer lock, after journal
                // replay and before any business read or deletion.
                tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
                    .await?;
                let args = check_policy(original, &current)?;
                let selected = owner
                    .sweep_locked_in(tx, args.prob_threshold, args.project.as_deref(), &current)
                    .await?;
                let reply = serde_json::json!({"deleted":selected.len(),"selected":selected});
                Ok((reply.clone(), reply))
            })
        })
        .await
    }
}

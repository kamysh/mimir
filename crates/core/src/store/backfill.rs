//! Server-captured source selection. This module does not run a provider or
//! decide what to do when another writer changes a captured source/vector.
use super::{
    operation_plans::CapturedSelection, AgeStore, OperationBindingRequest, OperationPlan,
    PlanDecision, RegisteredStep, StepDecision,
};
use crate::operation_catalogue::CommitSite;
use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::BTreeSet;
use uuid::Uuid;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct BackfillSource {
    pub(crate) id: Uuid,
    pub(crate) content: String,
    // Value deliberately requires the field, including an explicit null.
    pub(crate) project: Value,
    pub(crate) already_embedded: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Capture {
    beliefs: Vec<BackfillSource>,
}

pub(super) fn pending_keys(value: &Value) -> Result<Vec<String>> {
    let captured: Capture = mimir_json::decode_ref(value)?;
    let mut previous = None;
    let mut pending = Vec::new();
    for source in &captured.beliefs {
        ensure!(
            source.project.is_null() || source.project.is_string(),
            "A captured belief project must be its original string or null"
        );
        ensure!(
            previous.is_none_or(|id| id < source.id),
            "Captured belief IDs must be unique and in their original UUID order"
        );
        previous = Some(source.id);
        if !source.already_embedded {
            pending.push(source.id.to_string());
        }
    }
    // UUID parsing also accepts alternate spellings; persisted snapshots use
    // the one canonical representation produced by the server.
    ensure!(
        mimir_json::to_value(&captured)? == *value,
        "The captured source selection does not use its canonical stored representation"
    );
    Ok(pending)
}

impl AgeStore {
    pub(crate) async fn prepare_reembed_plan(
        &self,
        token: Uuid,
        expected: &OperationBindingRequest,
    ) -> Result<PlanDecision> {
        ensure!(
            expected.operation() == "reembed" && expected.arguments() == &serde_json::json!({}),
            "Backfill must retain its original reembed request with no per-call overrides"
        );
        crate::preparation::validate_operation_settings(expected.settings())?;
        let source = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        self.prepare_operation_captured(token, expected, move |tx, _| {
            Box::pin(async move {
                let mut beliefs = source.list_beliefs_on(tx).await?;
                let embedded: BTreeSet<Uuid> = tx
                    .query("SELECT belief_id FROM belief_embeddings", &[])
                    .await?
                    .iter()
                    .map(|row| row.try_get(0))
                    .collect::<std::result::Result<_, _>>()?;
                beliefs.sort_by_key(|belief| belief.id);
                let capture = Capture {
                    beliefs: beliefs
                        .into_iter()
                        .map(|belief| BackfillSource {
                            id: belief.id,
                            content: belief.content,
                            project: mimir_json::to_value(belief.project)
                                .expect("optional string is JSON"),
                            already_embedded: embedded.contains(&belief.id),
                        })
                        .collect(),
                };
                let value = mimir_json::to_value(capture)?;
                let pending = pending_keys(&value)?;
                Ok(CapturedSelection {
                    selections: vec![(CommitSite::BeliefVectorPublication, pending)],
                    capture: Some(value),
                })
            })
        })
        .await
    }
}

pub(crate) enum BackfillState {
    Existing,
    Pending,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum Status {
    Embedded,
    Skipped,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Answer {
    status: Status,
}

fn dialogue(message: String) -> anyhow::Error {
    crate::preparation::PreparationRequired::backfill(crate::validation::Code::MissingReference,
        format!("{message} No stale vector or saved completion was published. Open a dialog with the user; keep the original token and saved item answers rather than changing its selection.")).into()
}

impl AgeStore {
    pub(crate) fn reembed_sources(plan: &OperationPlan) -> Result<Vec<BackfillSource>> {
        ensure!(
            plan.original_request().operation() == "reembed",
            "Read the original reembed binding before selecting its sources"
        );
        let captured = plan
            .captured()
            .ok_or_else(|| dialogue("This operation has no saved source capture.".into()))?;
        pending_keys(captured)?;
        Ok(mimir_json::decode_ref::<Capture>(captured)?.beliefs)
    }

    async fn backfill_state_on(
        &self,
        client: &tokio_postgres::Client,
        source: &BackfillSource,
    ) -> Result<BackfillState> {
        let belief = self
            .get_belief_on(client, source.id)
            .await?
            .ok_or_else(|| {
                dialogue(format!("Belief {} was deleted after selection.", source.id))
            })?;
        if belief.content != source.content || belief.project.as_deref() != source.project.as_str()
        {
            return Err(dialogue(format!(
                "Belief {} has different source content or project than its original selection.",
                source.id
            )));
        }
        Ok(
            if client
                .query_opt(
                    "SELECT 1 FROM belief_embeddings WHERE belief_id=$1",
                    &[&source.id],
                )
                .await?
                .is_some()
            {
                BackfillState::Existing
            } else {
                BackfillState::Pending
            },
        )
    }

    pub(crate) async fn backfill_state(&self, source: &BackfillSource) -> Result<BackfillState> {
        let mut client = self.client.lock().await;
        let tx = super::snapshot_transaction(&mut client).await?;
        let state = self.backfill_state_on(tx.client(), source).await;
        tx.rollback().await?;
        state
    }

    pub(crate) async fn validate_reembed_prefix(&self, plan: &OperationPlan) -> Result<()> {
        let sources = Self::reembed_sources(plan)?;
        let mut client = self.client.lock().await;
        let tx = super::snapshot_transaction(&mut client).await?;
        let result=async {
            for source in &sources {
                let step=plan.steps().into_iter().find(|step|step.description().key.as_deref()==Some(source.id.to_string().as_str()));
                let saved=match step {Some(step)=>tx.query_opt("SELECT reply::text FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",&[&plan.operation_token(),&step.id()]).await?,None=>None};
                if let Some(row)=&saved {let raw:String=row.get(0);let _:Answer=mimir_json::from_str(&raw)?;}
                let current=self.backfill_state_on(tx.client(),source).await?;
                if source.already_embedded || saved.is_some() {
                    if matches!(current,BackfillState::Pending) {
                        return Err(dialogue(format!("Belief {} was already counted but its vector is no longer present. Its original receipt cannot authorize repeating old work.",source.id)));
                    }
                }
            }
            Ok(())
        }.await;
        tx.rollback().await?;
        result
    }

    pub(crate) async fn complete_reembed_empty(
        &self,
        plan: &OperationPlan,
    ) -> Result<super::CompletionDecision> {
        let sources = Self::reembed_sources(plan)?;
        ensure!(
            plan.steps().is_empty(),
            "Complete pending items with their registered final step"
        );
        let owner = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        self.complete_operation_checked(plan,move|tx|Box::pin(async move {
            tx.query("SELECT pg_advisory_xact_lock(671942183)",&[]).await?;
            for source in &sources {
                if matches!(owner.backfill_state_on(tx.client(),source).await?,BackfillState::Pending) {
                    return Err(dialogue(format!("Belief {} no longer has its originally skipped vector; ask the user before claiming completion.",source.id)));
                }
            }
            Ok(serde_json::json!({"embedded":0,"skipped":sources.len()}))
        })).await
    }

    pub(crate) async fn commit_reembed_item(
        &self,
        step: &RegisteredStep,
        vector: Option<Vec<f32>>,
    ) -> Result<StepDecision> {
        ensure!(
            step.description().site == CommitSite::BeliefVectorPublication.name(),
            "Use this operation's registered belief-vector step"
        );
        let plan = step.plan();
        let sources = Self::reembed_sources(&plan)?;
        let source = sources
            .iter()
            .find(|source| {
                !source.already_embedded
                    && step.description().key.as_deref() == Some(source.id.to_string().as_str())
            })
            .cloned()
            .ok_or_else(|| {
                dialogue("This step is absent from the original pending selection.".into())
            })?;
        let final_step = step.is_final();
        let token = step.token();
        let prior = plan
            .steps()
            .into_iter()
            .take_while(|prior| prior.id() != step.id())
            .map(|prior| prior.id().to_owned())
            .collect::<Vec<_>>();
        let initially_skipped = sources
            .iter()
            .filter(|source| source.already_embedded)
            .count();
        let owner = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        self.publish_operation_step(step,final_step,move|tx,_|Box::pin(async move {
            tx.query("SELECT pg_advisory_xact_lock(671942183)",&[]).await?;
            let status=match owner.backfill_state_on(tx.client(),&source).await? {
                BackfillState::Existing=>Status::Skipped,
                BackfillState::Pending=>{
                    let vector=vector.ok_or_else(|| dialogue("The original source still needs an actual embedding result.".into()))?;
                    ensure!(crate::preparation::usable_vector(&vector),"The actual preparation returned an empty, nonfinite or zero vector; repair the backend before retrying");
                    let vector=pgvector::Vector::from(vector);
                    let inserted=tx.execute("INSERT INTO belief_embeddings(belief_id,embedding) VALUES($1,$2) ON CONFLICT(belief_id) DO NOTHING",&[&source.id,&vector]).await?;
                    if inserted==1 {Status::Embedded} else {Status::Skipped}
                }
            };
            let answer=mimir_json::to_value(Answer{status})?;
            let final_reply=if final_step {
                for expected in &sources {
                    if matches!(owner.backfill_state_on(tx.client(),expected).await?,BackfillState::Pending) {
                        return Err(dialogue(format!("Originally selected belief {} no longer has its vector; resolve the old operation before claiming completion.",expected.id)));
                    }
                }
                let mut embedded=0usize;let mut skipped=initially_skipped;
                for key in prior {
                    let raw:String=tx.query_one("SELECT reply::text FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",&[&token,&key]).await?.get(0);
                    match mimir_json::from_str::<Answer>(&raw)?.status {Status::Embedded=>embedded+=1,Status::Skipped=>skipped+=1}
                }
                match status {Status::Embedded=>embedded+=1,Status::Skipped=>skipped+=1}
                Some(serde_json::json!({"embedded":embedded,"skipped":skipped}))
            } else {None};
            Ok((answer,final_reply))
        })).await
    }
}

#[cfg(test)]
#[path = "backfill_tests.rs"]
mod tests;

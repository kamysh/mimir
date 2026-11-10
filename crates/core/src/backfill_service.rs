//! Registered reembedding uses the immutable original selection and saved
//! answers. Provider jobs are owned and event-driven; no polling or deadline.
use crate::{
    db,
    preparation::{self, PreparationRequired},
    store::{
        AgeStore, BackfillSource, BackfillState, OperationOutcome, PlanDecision, StepDecision,
    },
    validation::Code,
    MimirService,
};
use anyhow::{anyhow, Result};
use uuid::Uuid;

impl MimirService {
    pub async fn reembed_operation(&self, token: Uuid) -> Result<OperationOutcome> {
        self.own_operation(token, self.reembed_operation_inner(token))
            .await
    }

    async fn reembed_operation_inner(&self, token: Uuid) -> Result<OperationOutcome> {
        let plan = match self.prepare_reembed_operation(token).await? {
            PlanDecision::Ready(plan) => plan,
            PlanDecision::NeedsRecovery(reason) => return Err(anyhow!(reason)),
            _ => return self.read_operation_outcome(token, None).await,
        };
        let original = self.read_operation_outcome(token, None).await?;
        if !matches!(
            original,
            OperationOutcome::Pending { .. } | OperationOutcome::AwaitingCompletion(_)
        ) {
            return Ok(original);
        }
        let sources = AgeStore::reembed_sources(&plan)?;
        let steps = plan.steps();
        if steps.is_empty() {
            self.store.complete_reembed_empty(&plan).await?;
            return self.read_operation_outcome(token, None).await;
        }
        for step in steps {
            self.store.validate_reembed_prefix(&plan).await?;
            // Replay precedes source/configuration/provider checks. These
            // immutable answers are facts about already committed work.
            if self.read_operation_step(token, step.id()).await?.is_some() {
                continue;
            }
            let source=sources.iter().find(|source|!source.already_embedded && step.description().key.as_deref()==Some(source.id.to_string().as_str()))
                .ok_or_else(||anyhow!("Read the original plan: this pending step has no captured source. Do not select replacement work."))?;
            let vector = self.prepare_reembed_source(&plan, source).await?;
            if !matches!(
                self.store.commit_reembed_item(&step, vector).await?,
                StepDecision::Done(_)
            ) {
                return self.read_operation_outcome(token, None).await;
            }
        }
        self.read_operation_outcome(token, None).await
    }

    async fn prepare_reembed_source(
        &self,
        plan: &crate::store::OperationPlan,
        source: &BackfillSource,
    ) -> Result<Option<Vec<f32>>> {
        let token = plan.operation_token();
        let original_settings = plan.original_request().settings();
        let problem =
            |code, message| anyhow::Error::from(PreparationRequired::backfill(code, message));
        let mut events = db::EmbeddingOwnerSubscription::connect(&self.database).await?;
        self.check_backfill_cancellation(Some(token)).await?;
        self.store.validate_reembed_prefix(plan).await?;
        if matches!(
            self.store.backfill_state(source).await?,
            BackfillState::Existing
        ) {
            return Ok(None);
        }
        if original_settings != &self.embedding_operation_settings() {
            return Err(problem(Code::MissingEvidence,"The configured embedding identity differs from this unfinished operation's original model/settings. No provider was started. Open a dialog to restore its original settings or explicitly cancel; do not silently replace its model.".into()));
        }
        let backend=self.embeddings.as_ref().ok_or_else(||problem(Code::MissingEvidence,"The original pending source requires a configured embedding backend before writing; open a user dialog to repair it or cancel.".into()))?;
        let texts = [source.content.clone()];
        let job = backend.embed(&texts);
        tokio::pin!(job);
        loop {
            tokio::select! {
                biased;
                event=events.changed()=>{
                    event?;
                    self.check_backfill_cancellation(Some(token)).await?;
                    self.store.validate_reembed_prefix(plan).await?;
                    if matches!(self.store.backfill_state(source).await?,BackfillState::Existing) {
                        // Dropping the owned future stops/reaps its provider
                        // before the saved skipped answer is published.
                        return Ok(None);
                    }
                }
                result=&mut job=>{
                    self.check_backfill_cancellation(Some(token)).await?;
                    self.store.validate_reembed_prefix(plan).await?;
                    if matches!(self.store.backfill_state(source).await?,BackfillState::Existing) {return Ok(None);}
                    let vectors=result.map_err(|cause|problem(Code::MissingEvidence,format!("Embedding preparation failed: {cause:#}. No vector from this job was stored; open a user dialog to repair the backend or cancel.")))?;
                    let [vector]=vectors.as_slice() else {
                        return Err(problem(Code::MalformedInput,format!("The provider returned {} vectors for one selected source. No vector was stored; repair the backend before retrying.",vectors.len())));
                    };
                    if !preparation::usable_vector(vector) {
                        return Err(problem(Code::InvalidNumber,"The provider returned an empty, nonfinite or zero vector. No vector was stored; repair the backend before retrying.".into()));
                    }
                    return Ok(Some(vector.clone()));
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "backfill_service_tests.rs"]
mod tests;

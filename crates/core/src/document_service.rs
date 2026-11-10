//! Registered document loading retains its original file preparation and
//! publishes a complete replacement with its original answer.
use crate::{
    db,
    embed::OwnedEmbeddingBackend,
    interaction::Location,
    operation_catalogue::CommitSite,
    preparation::PreparationRequired,
    store::{
        document_arguments, DocumentDraft, DocumentPreparation, OperationBindingRequest,
        OperationOutcome, PlanDecision, StepDecision,
    },
    validation::{Code, Segment},
    MimirService,
};
use anyhow::Result;
use uuid::Uuid;

fn problem(code: Code, message: impl Into<String>) -> anyhow::Error {
    PreparationRequired::document(
        Location::Request,
        vec![Segment::Key("operation_token".into())],
        code,
        message.into(),
    )
    .into()
}

fn backend_problem(code: Code, message: impl Into<String>) -> anyhow::Error {
    PreparationRequired::document(
        Location::Configuration,
        vec![Segment::Key("embeddings".into())],
        code,
        message.into(),
    )
    .into()
}

#[cfg(test)]
#[path = "document_service_tests.rs"]
mod tests;

enum Work {
    Embedded(Vec<Vec<f32>>),
    Stopped,
}

impl MimirService {
    pub fn load_document_request(
        &self,
        path: &str,
        project: Option<&str>,
    ) -> Result<OperationBindingRequest> {
        let request = OperationBindingRequest::new(
            "load_document".into(),
            serde_json::json!({"path":path,"project":project}),
            self.embedding_operation_settings(),
        )?;
        document_arguments(&request)?;
        Ok(request)
    }

    pub async fn load_document_operation(&self, token: Uuid) -> Result<OperationOutcome> {
        let Some(binding) = self.read_operation_binding(token).await? else {
            return self.read_operation_outcome(token, None).await;
        };
        if binding.request.operation() != "load_document" {
            return Err(problem(Code::WrongIdentity, "This token belongs to a different operation. Read its original binding and outcome; do not reinterpret its saved result as a document load."));
        }
        let original = self
            .read_operation_outcome(token, Some(&binding.request))
            .await?;
        if matches!(
            original,
            OperationOutcome::Completed { .. }
                | OperationOutcome::Cancelled { .. }
                | OperationOutcome::NeedsRecovery { .. }
        ) {
            return Ok(original);
        }
        let arguments = document_arguments(&binding.request)?;
        let plan = match self
            .prepare_operation(token, &binding.request, |_, _| {
                Box::pin(async { Ok(vec![]) })
            })
            .await?
        {
            PlanDecision::Ready(plan) => plan,
            PlanDecision::NeedsRecovery(reason) => {
                return Err(problem(Code::MissingReference, reason))
            }
            _ => {
                return self
                    .read_operation_outcome(token, Some(&binding.request))
                    .await
            }
        };
        let steps = plan.steps();
        let [first, final_step] = steps.as_slice() else {
            return Err(problem(Code::MissingReference, "This unfinished token has an older document plan. Read its saved answers and ask the user whether to cancel it before reserving corrected work. Its original plan was not changed."));
        };
        if first.description().site != CommitSite::DocumentPreparation.name()
            || final_step.description().site != CommitSite::DocumentReplacement.name()
        {
            return Err(problem(Code::MissingReference, "This unfinished token does not have the original complete-document plan. Read its saved answers and resolve it with the user; no replacement was published."));
        }
        // Completed history was returned before inspecting present settings.
        if binding.request.settings() != &self.embedding_operation_settings() {
            return Err(backend_problem(Code::WrongIdentity, "The configured embedding identity differs from this unfinished operation's original settings. Restore that configuration or ask the user whether to cancel and reserve corrected work; do not silently select a different model."));
        }
        let backend = self.embeddings.as_ref().ok_or_else(|| PreparationRequired::document(
            Location::Configuration, vec![Segment::Key("embeddings".into())], Code::MissingField,
            "Document loading requires a configured embedding backend. Open the user dialog to choose or repair it; do not infer a model or replace the existing document index.".into()))?;
        let allocation = match self.read_operation_step(token, first.id()).await? {
            Some(saved) => saved,
            None => match self
                .store
                .reserve_document_operation(first, DocumentDraft::read(&arguments)?)
                .await?
            {
                StepDecision::Done(saved) => saved,
                StepDecision::NeedsRecovery(reason) => {
                    return Err(problem(Code::MissingReference, reason))
                }
                _ => {
                    return self
                        .read_operation_outcome(token, Some(&binding.request))
                        .await
                }
            },
        };
        let prepared: DocumentPreparation = mimir_json::decode_ref(&allocation.reply).map_err(|_| problem(
            Code::MalformedInput, "The saved original document preparation cannot be decoded. Read this token's saved answer and resolve it with the user; do not replace its file snapshot or generated identities."))?;
        let vectors = match self
            .embed_original_document(token, backend, &prepared)
            .await?
        {
            Work::Stopped => return self.document_stopped(token).await,
            Work::Embedded(vectors) => vectors,
        };
        if let StepDecision::NeedsRecovery(reason) = self
            .store
            .publish_document_operation(first, final_step, &prepared, &vectors)
            .await?
        {
            return Err(problem(Code::MissingReference, reason));
        }
        self.read_operation_outcome(token, Some(&binding.request))
            .await
    }

    async fn document_stopped(&self, token: Uuid) -> Result<OperationOutcome> {
        let outcome = self.read_operation_outcome(token, None).await?;
        if matches!(
            outcome,
            OperationOutcome::Completed { .. } | OperationOutcome::Cancelled { .. }
        ) {
            return Ok(outcome);
        }
        Err(problem(Code::MissingReference,
            "Document preparation was revoked or its original index changed. The owned embedding stopped and no replacement from this job was published. Read the original token's outcome and discuss resuming or explicitly cancelling with the user."))
    }

    async fn embed_original_document(
        &self,
        token: Uuid,
        backend: &OwnedEmbeddingBackend,
        prepared: &DocumentPreparation,
    ) -> Result<Work> {
        // Subscribe before readback so revocation between read and wait cannot
        // be lost. The provider future is owned, cancelled and reaped on drop.
        let mut changes = db::EmbeddingOwnerSubscription::connect(&self.database).await?;
        if !self
            .store
            .document_preparation_is_current(token, prepared)
            .await?
        {
            return Ok(Work::Stopped);
        }
        if prepared.chunks.is_empty() {
            return Ok(Work::Embedded(vec![]));
        }
        let texts: Vec<String> = prepared
            .chunks
            .iter()
            .map(|chunk| chunk.content.clone())
            .collect();
        let job = backend.embed(&texts);
        tokio::pin!(job);
        loop {
            tokio::select! {
                biased;
                changed = changes.changed() => {
                    changed?;
                    if !self.store.document_preparation_is_current(token, prepared).await? {
                        // Finish this owned scope before any outcome readback.
                        // A blocked database read must not keep the revoked
                        // native/HTTP embedding job alive.
                        return Ok(Work::Stopped);
                    }
                }
                result = &mut job => {
                    if !self.store.document_preparation_is_current(token, prepared).await? {
                        return Ok(Work::Stopped);
                    }
                    let vectors = result.map_err(|cause| backend_problem(Code::MissingEvidence,
                        format!("Embedding the original saved document failed: {cause:#}. No replacement was published. Repair its original configured backend or explicitly cancel before changing the saved input.")))?;
                    if vectors.len() != prepared.chunks.len()
                        || vectors.iter().any(|vector|
                            prepared.declared_dimensions.is_some_and(|dimension| vector.len() != dimension)
                            || vectors.first().is_some_and(|first| vector.len() != first.len())
                            || !crate::preparation::usable_vector(vector)) {
                        return Err(backend_problem(Code::MalformedInput,
                            "The provider did not return one complete, finite, nonzero vector of a consistent dimension for each original chunk, within any dimension required by the actual database column. The existing index was not changed. Repair the backend and retry the same token; do not omit chunks or publish partial results."));
                    }
                    return Ok(Work::Embedded(vectors));
                }
            }
        }
    }
}

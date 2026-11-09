//! Publish one prepared belief, its vector and indexed grounding together.
use super::{
    learning_transaction, snapshot_transaction, AgeStore, OperationBindingRequest,
    OperationOutcome, OperationPlan, RegisteredStep, StepDecision, StepReceipt,
};
use crate::{
    graph::Belief,
    interaction::Location,
    preparation::{
        compatible_projects, IndexedSupport, PreparationRequired, PreparedBelief, ValidatedSupport,
    },
    validation::{Code, Segment},
};
use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use uuid::Uuid;

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct BeliefArguments {
    content: String,
    probability: f64,
    confidence: f64,
    project: Option<String>,
    memory_type: Option<String>,
    provenance: crate::learning::IndependentProvenance,
    // Older completed operations keep their saved result. This default is
    // decoding compatibility only; preparation refuses missing citations.
    #[serde(default)]
    grounding: Vec<IndexedSupport>,
}

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct OwnerAllocation {
    id: Uuid,
    created_at: DateTime<Utc>,
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct ProviderSettings {
    embeddings: mimir_json::Document,
}

#[derive(serde::Deserialize)]
#[serde(tag = "backend", rename_all = "lowercase", deny_unknown_fields)]
enum ProviderIdentity {
    Local {
        model: String,
    },
    Voyage {
        model: String,
        input_type: String,
        truncation: bool,
    },
    #[serde(rename = "openai")]
    OpenAi {
        model: String,
    },
}

fn original_arguments(request: &OperationBindingRequest) -> Result<BeliefArguments> {
    decode_original_arguments(request).map_err(|error| PreparationRequired::bound_request(
        Code::MalformedInput,
        format!("The original bound belief request cannot be prepared: {error:#}. No belief was stored.")
    ).into())
}

pub(crate) fn admit_request(request: &OperationBindingRequest) -> Result<()> {
    original_arguments(request).map(|_| ())
}

fn decode_original_arguments(request: &OperationBindingRequest) -> Result<BeliefArguments> {
    anyhow::ensure!(request.operation() == "insert_belief",
        "Use the original insert_belief operation; read its saved binding and outcome before continuing");
    let settings: ProviderSettings = mimir_json::decode_ref(request.settings())
        .context("Read the original server-selected embedding settings; do not invent a model or supply credentials in this binding")?;
    if !settings.embeddings.is_null() {
        let provider: ProviderIdentity = mimir_json::from_value(settings.embeddings)
            .context("The original embedding identity has unknown or missing fields; read its binding and ask the user before choosing a model")?;
        match provider {
            ProviderIdentity::Local { model } => anyhow::ensure!(model == crate::embed::HF_MODEL_ID,
                "The local operation must retain its actual BGE model; do not replace the saved model"),
            ProviderIdentity::Voyage { model, input_type, truncation } => {
                anyhow::ensure!(input_type == "document" && !truncation,
                    "Retain Voyage document input without truncation; read the original embedding settings");
                let _ = model;
            }
            ProviderIdentity::OpenAi { model } => { let _ = model; }
        }
    }
    let arguments: BeliefArguments = mimir_json::decode_ref(request.arguments())
        .context("Read the original insert_belief content, probability, confidence, provenance and grounding citations, retaining only its declared optional project and memory_type fields")?;
    crate::graph::Probability::new(arguments.probability)?;
    crate::graph::Probability::new(arguments.confidence)?;
    arguments.provenance.validate()?;
    let _: crate::graph::MemoryType = arguments
        .memory_type
        .as_deref()
        .map(str::parse)
        .transpose()?
        .unwrap_or_default();
    anyhow::ensure!(
        !arguments.content.trim().is_empty(),
        "Supply the complete nonempty belief content; do not publish an empty belief"
    );
    Ok(arguments)
}

impl BeliefArguments {
    fn belief(&self, owner: &OwnerAllocation) -> Result<Belief> {
        let (alpha, beta) = crate::graph::prior_from(self.probability, self.confidence);
        Ok(Belief {
            id: owner.id,
            content: self.content.clone(),
            probability: crate::graph::Probability::new(self.probability)?,
            confidence: crate::graph::Probability::new(self.confidence)?,
            alpha,
            beta,
            alpha0: alpha,
            beta0: beta,
            created_at: owner.created_at,
            last_activated_at: owner.created_at,
            decay_accounted_at: owner.created_at,
            memory_type: self
                .memory_type
                .as_deref()
                .map(str::parse)
                .transpose()?
                .unwrap_or_default(),
            project: self.project.clone(),
        })
    }
}

#[derive(Debug)]
pub(crate) enum BeliefPublicationState {
    Resolved(StepDecision),
    Preparing {
        final_step: RegisteredStep,
        belief: Belief,
        provenance: crate::learning::IndependentProvenance,
        grounding: Vec<IndexedSupport>,
    },
}

impl AgeStore {
    /// Validate the submitting agent's exact citations against one indexed
    /// document view. No similarity score can accept or reject these claims.
    pub(crate) async fn validate_indexed_support(
        &self,
        project: Option<&str>,
        citations: &[IndexedSupport],
    ) -> Result<Vec<ValidatedSupport>> {
        if citations.is_empty() {
            return Err(PreparationRequired::new(Location::Arguments,
                vec![Segment::Key("grounding".into())], Code::MissingEvidence,
                "Supply at least one citation to an indexed document, with chunk_id, document_path, an exact quotation and an explanation of why it supports the belief. If no clear support is available, open the user dialog before publication. No belief was stored.".into()).into());
        }
        for (index, citation) in citations.iter().enumerate() {
            citation.validate_fields(index)?;
        }
        let mut client = self.client.lock().await;
        let tx = snapshot_transaction(&mut client).await?;
        let mut validated = Vec::with_capacity(citations.len());
        for (index, citation) in citations.iter().enumerate() {
            let issue = |field: &str, code: Code, message: String| {
                PreparationRequired::new(
                    Location::Arguments,
                    vec![
                        Segment::Key("grounding".into()),
                        Segment::Index(index),
                        Segment::Key(field.into()),
                    ],
                    code,
                    message,
                )
            };
            let chunk = self.get_chunk_by_id_on(tx.client(), citation.chunk_id).await?
                .ok_or_else(|| issue("chunk_id", Code::MissingReference,
                    format!("Cited chunk {} is not stored. Query the indexed document and copy its actual chunk ID; do not invent a replacement ID. No belief was stored.", citation.chunk_id)))?;
            if citation.document_path != chunk.document_path {
                return Err(issue("document_path", Code::WrongIdentity,
                    format!("Cited chunk {} belongs to indexed document {:?}, not {:?}. Copy the document_path returned with that passage. No belief was stored.", chunk.id, chunk.document_path, citation.document_path)).into());
            }
            if !compatible_projects(project, chunk.project.as_deref()) {
                return Err(issue("chunk_id", Code::MissingReference,
                    "The cited indexed document is not compatible with the belief's project. Find support in the intended project or an unscoped document; do not move the belief or change its project automatically. No belief was stored.".into()).into());
            }
            if !chunk.content.contains(&citation.quotation) {
                return Err(issue("quotation", Code::QuotationMismatch,
                    format!("The quotation is not an exact contiguous passage in indexed chunk {}. Query that document and copy the original text without rewriting it; put the support explanation in explanation. No belief was stored.", chunk.id)).into());
            }
            let indexed: bool = tx
                .query_one(
                    "SELECT EXISTS(SELECT 1 FROM public.chunk_embeddings WHERE chunk_id=$1)",
                    &[&chunk.id],
                )
                .await?
                .get(0);
            if !indexed {
                return Err(issue("chunk_id", Code::MissingReference,
                    format!("Chunk {} has no indexed document vector. Ask the user to repair or index the supporting document before publication; do not treat an unindexed source as indexed support. No belief was stored.", chunk.id)).into());
            }
            validated.push(ValidatedSupport {
                chunk,
                citation: citation.clone(),
            });
        }
        tx.commit().await?;
        Ok(validated)
    }

    /// The actual PostgreSQL allocation and its original answer share a commit.
    /// Retrying this phase never reserves a replacement owner identity.
    pub(crate) async fn reserve_belief_operation(
        &self,
        step: &RegisteredStep,
    ) -> Result<StepDecision> {
        original_arguments(step.expected())?;
        anyhow::ensure!(
            step.description().site
                == crate::operation_catalogue::CommitSite::EmbeddingOwnerReservation.name(),
            "Use the original preparation-owner step; no belief was stored"
        );
        let token = step.token();
        self.commit_operation_step(step, move |tx, request| Box::pin(async move {
            let arguments = original_arguments(request)?;
            tx.query("SELECT pg_advisory_xact_lock(671942183)", &[]).await?;
            let row=tx.query_one(
                "INSERT INTO mimir_embedding_owners(project,operation_token) VALUES($1,$2) RETURNING owner_token,reserved_at",
                &[&arguments.project,&token],
            ).await?;
            Ok(mimir_json::to_value(OwnerAllocation { id:row.try_get(0)?, created_at:row.try_get(1)? })?)
        })).await
    }

    /// Resolve completion before inspecting current model settings or starting
    /// another provider. This method itself never embeds or publishes a belief.
    pub(crate) async fn resume_belief_operation(
        &self,
        plan: &OperationPlan,
        current_settings: &serde_json::Value,
    ) -> Result<BeliefPublicationState> {
        let steps = plan.steps();
        let [first, final_step] = steps.as_slice() else {
            anyhow::bail!("Use the original two-step belief plan; read its saved plan and outcome before continuing");
        };
        let arguments = original_arguments(first.expected())?;
        anyhow::ensure!(
            final_step.description().site
                == crate::operation_catalogue::CommitSite::BeliefPublication.name(),
            "The final step must publish the complete prepared belief; no belief was stored"
        );
        let allocation = match self.reserve_belief_operation(first).await? {
            StepDecision::Done(saved) => saved,
            decision => return Ok(BeliefPublicationState::Resolved(decision)),
        };
        let token = plan.operation_token();
        match self.read_operation_outcome(token,Some(first.expected())).await? {
            OperationOutcome::Completed { outcome,.. }=>return Ok(BeliefPublicationState::Resolved(
                StepDecision::Done(StepReceipt { operation_token:token,step:final_step.id().to_owned(),reply:mimir_json::Document::new(mimir_json::clone_value(outcome.reply())) }))),
            OperationOutcome::Cancelled { cancellation,.. }=>return Ok(BeliefPublicationState::Resolved(StepDecision::Cancelled(cancellation))),
            OperationOutcome::ChangedRequest(binding)=>return Ok(BeliefPublicationState::Resolved(StepDecision::ChangedRequest(binding))),
            OperationOutcome::NeedsRecovery { reason,.. }=>return Ok(BeliefPublicationState::Resolved(StepDecision::NeedsRecovery(reason))),
            OperationOutcome::Pending { next_step,.. } if next_step != *final_step.description()=>
                return Ok(BeliefPublicationState::Resolved(StepDecision::OutOfOrder(next_step))),
            OperationOutcome::Pending { .. }=>{},
            _=>return Ok(BeliefPublicationState::Resolved(StepDecision::NeedsRecovery(
                "The original preparation step has an answer but its plan cannot be resumed. Read this token's original binding, plan and saved outcome; do not reserve a replacement identity.".into()))),
        }
        if first.expected().settings() != current_settings {
            return Err(PreparationRequired::new(Location::Configuration,vec![],Code::WrongIdentity,
                "The configured embedding backend or model differs from this unfinished operation's original settings. Read its saved binding and open a dialog with the user; do not switch models, repeat publication or replace the original token automatically. No belief was stored.".into()).into());
        }
        let owner:OwnerAllocation=mimir_json::decode_ref(&allocation.reply)
            .context("The original preparation allocation cannot be read; inspect its saved answer rather than reserving a replacement identity")?;
        Ok(BeliefPublicationState::Preparing {
            final_step: final_step.clone(),
            belief: arguments.belief(&owner)?,
            provenance: arguments.provenance,
            grounding: arguments.grounding,
        })
    }
    /// Linked operation identities never change after owner allocation. Read
    /// them before taking learning/owner locks, then lock reservations in one
    /// order so cancellation and publication cannot invert their locks.
    pub(super) async fn lock_preparation_operations(
        &self,
        tx: &tokio_postgres::Transaction<'_>,
        identities: &[Uuid],
    ) -> Result<()> {
        let rows = tx.query(
            "SELECT DISTINCT operation_token FROM mimir_embedding_owners WHERE owner_token=ANY($1) AND operation_token IS NOT NULL ORDER BY operation_token",
            &[&identities],
        ).await?;
        for row in rows {
            let token: Uuid = row.get(0);
            if !super::cancellations::lock_token(tx, token).await? {
                return Err(PreparationRequired::new(Location::Request, vec![], Code::MissingReference,
                    format!("Preparation refers to unknown operation {token}. Read its original reservation and ask the user before starting different work. No belief was stored.")).into());
            }
            if let Some(cancelled) = super::cancellations::lookup(tx, token).await? {
                return Err(PreparationRequired::new(Location::Request, vec![], Code::MissingReference,
                    format!("Operation {token} was explicitly cancelled at {}. Read its saved answers and cancellation record, then ask the user before starting different work. No belief was stored.", cancelled.cancelled_at)).into());
            }
        }
        Ok(())
    }

    pub(crate) async fn preparation_is_current(
        &self,
        belief: &Belief,
        support: &[ValidatedSupport],
    ) -> Result<bool> {
        let mut client = self.client.lock().await;
        let tx = snapshot_transaction(&mut client).await?;
        let owner:bool = tx.query_one(
            "SELECT EXISTS(SELECT 1 FROM mimir_embedding_owners WHERE owner_token=$1 AND project IS NOT DISTINCT FROM $2)",
            &[&belief.id, &belief.project],
        ).await?.get(0);
        if !owner || support.is_empty() {
            return Ok(false);
        }
        for passage in support {
            if self
                .get_chunk_by_id_on(tx.client(), passage.chunk.id)
                .await?
                .as_ref()
                != Some(&passage.chunk)
            {
                return Ok(false);
            }
            let indexed: bool = tx
                .query_one(
                    "SELECT EXISTS(SELECT 1 FROM public.chunk_embeddings WHERE chunk_id=$1)",
                    &[&passage.chunk.id],
                )
                .await?
                .get(0);
            if !indexed {
                return Ok(false);
            }
        }
        tx.commit().await?;
        Ok(true)
    }

    pub(crate) async fn reserve_belief_preparation(
        &self,
        project: Option<&str>,
    ) -> Result<(Uuid, DateTime<Utc>)> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let row = tx.query_one("INSERT INTO mimir_embedding_owners(project) VALUES($1) RETURNING owner_token,reserved_at", &[&project]).await?;
        let identity = (row.get(0), row.get(1));
        tx.commit().await?;
        Ok(identity)
    }

    pub(crate) async fn publish_prepared_belief(
        &self,
        prepared: &PreparedBelief,
    ) -> Result<Belief> {
        let belief = &prepared.belief;
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        self.lock_preparation_operations(&tx, &[belief.id]).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        self.insert_prepared_belief_on(&tx, prepared).await?;
        let published = self.get_belief_on(tx.client(), belief.id).await?.context(
            "Prepared publication did not retain its belief; the transaction was not committed",
        )?;
        tx.commit().await.with_context(|| format!("The publication outcome for belief {} must be read back before retrying. Read that belief and its indexed grounding; do not allocate a replacement identity.", belief.id))?;
        Ok(published)
    }

    pub(crate) async fn publish_belief_operation(
        &self,
        step: &RegisteredStep,
        prepared: &PreparedBelief,
    ) -> Result<StepDecision> {
        anyhow::ensure!(
            step.description().site
                == crate::operation_catalogue::CommitSite::BeliefPublication.name(),
            "Use the original registered belief publication step"
        );
        let owner = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        let prepared = prepared.clone();
        self.commit_final_operation_step(step, move |tx, binding| Box::pin(async move {
            let arguments = original_arguments(binding)?;
            anyhow::ensure!(arguments.content == prepared.belief.content && arguments.project == prepared.belief.project
                && arguments.probability == prepared.belief.probability.value() && arguments.confidence == prepared.belief.confidence.value()
                && Some(&arguments.provenance) == prepared.provenance.as_ref()
                && arguments.grounding == prepared.support.iter().map(|support|support.citation.clone()).collect::<Vec<_>>(),
                "Read this operation's original belief and citations; explicitly cancel it with the user's approval before reserving corrected work. No belief was stored");
            owner.lock_preparation_operations(tx, &[prepared.belief.id]).await?;
            tx.query("SELECT pg_advisory_xact_lock(671942183)", &[]).await?;
            owner.insert_prepared_belief_on(tx, &prepared).await?;
            let published = owner.get_belief_on(tx.client(), prepared.belief.id).await?
                .context("The complete published belief must be readable before saving its original answer")?;
            let reply = mimir_json::to_value(&published)?;
            Ok((reply.clone(), reply))
        })).await
    }

    pub(crate) async fn belief_sources_on(
        &self,
        client: &tokio_postgres::Client,
        id: Uuid,
    ) -> Result<Vec<IndexedSupport>> {
        match client
            .query_opt(
                "SELECT citations::text FROM public.mimir_belief_sources WHERE belief_id=$1",
                &[&id],
            )
            .await?
        {
            Some(row) => Ok(mimir_json::from_str(row.get(0))?),
            None => Ok(vec![]),
        }
    }

    pub(super) async fn insert_prepared_belief_on(
        &self,
        tx: &tokio_postgres::Transaction<'_>,
        prepared: &PreparedBelief,
    ) -> Result<()> {
        let belief = &prepared.belief;
        // Every refusal below precedes this candidate's writes. The caller
        // owns the transaction; returning an error rolls back any earlier
        // uncommitted candidates too. Never relabel transport/write errors.
        let owner_exists = tx.query_opt(
            "SELECT owner_token FROM mimir_embedding_owners WHERE owner_token=$1 AND project IS NOT DISTINCT FROM $2 FOR KEY SHARE",
            &[&belief.id, &belief.project],
        ).await?.is_some();
        if !owner_exists {
            return Err(PreparationRequired::new(Location::Request, vec![], Code::MissingReference,
                format!("Preparation {} no longer owns publication: its work was cancelled, its project was deleted, or publication already completed. Read the original operation outcome and get_belief for this ID, then ask the user before starting new work. No new belief was stored.", belief.id)).into());
        }
        if self.get_belief_on(tx.client(), belief.id).await?.is_some() {
            return Err(PreparationRequired::new(
                Location::Arguments,
                vec![Segment::Key("id".into())],
                Code::WrongIdentity,
                format!("Prepared belief {} already exists. Read its current state and the original operation outcome before retrying; do not allocate a replacement identity. No new belief was stored.", belief.id),
            ).into());
        }
        anyhow::ensure!(
            crate::preparation::usable_vector(&prepared.vector) && !prepared.support.is_empty(),
            "Only a complete validated preparation may enter publication"
        );
        for passage in &prepared.support {
            let current = self
                .get_chunk_by_id_on(tx.client(), passage.chunk.id)
                .await?;
            let indexed: bool = tx
                .query_one(
                    "SELECT EXISTS(SELECT 1 FROM public.chunk_embeddings WHERE chunk_id=$1)",
                    &[&passage.chunk.id],
                )
                .await?
                .get(0);
            if current.as_ref() != Some(&passage.chunk) || !indexed {
                return Err(PreparationRequired::new(
                    Location::Arguments,
                    vec![Segment::Key("content".into())],
                    Code::MissingReference,
                    format!("Supporting indexed passage {} changed or disappeared during preparation. Read the current document and ask the user how to proceed. No belief was stored.", passage.chunk.id),
                ).into());
            }
        }

        self.insert_belief_on(tx.client(), belief, prepared.provenance.as_ref())
            .await?;
        self.insert_belief_embedding_on(tx.client(), belief.id, &prepared.vector)
            .await?;
        let citations: Vec<_> = prepared
            .support
            .iter()
            .map(|support| &support.citation)
            .collect();
        let encoded = mimir_json::to_string(&citations)?;
        tx.execute(
            "INSERT INTO mimir_belief_sources(belief_id,citations) VALUES($1,$2::text::jsonb)",
            &[&belief.id, &encoded],
        )
        .await?;
        tx.execute(
            "DELETE FROM mimir_embedding_owners WHERE owner_token=$1",
            &[&belief.id],
        )
        .await?;
        Ok(())
    }
}

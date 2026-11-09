pub mod assessment;
mod backfill_service;
pub mod config;
pub mod db;
mod document_service;
pub mod documents;
pub mod embed;
pub mod graph;
pub mod inference;
pub mod interaction;
pub mod learning;
pub mod learning_sources;
pub mod operation_catalogue;
mod password;
pub mod retrieval;
pub mod store;
mod sweep_service;
mod tls;
pub mod validation;

use anyhow::Result;
use uuid::Uuid;

use config::Config;
use documents::{parse_markdown, QueryResult};
use embed::{make_backend, OwnedEmbeddingBackend};
use graph::{Belief, EdgeType, MemoryType, Pattern, Probability};
use inference::InferenceEngine;
use retrieval::{RetrievalCoverage, RetrievalReport, SemanticObservation};
use store::AgeStore;

/// Weighted Reciprocal Rank Fusion. Each ranked list contributes
/// `weight / (K + rank)` (0-based rank, K = 60) to every id it contains; the
/// per-id contributions sum. Score-agnostic (ranks only), so lists on
/// incompatible scales — cosine, token-overlap, probability — fuse cleanly, and
/// the weights set each signal's relative pull. Used by `query_relevant` to
/// combine the semantic, lexical, and probability-prior rankings.
fn weighted_rrf(lists: &[(&[Uuid], f32)]) -> std::collections::HashMap<Uuid, f32> {
    const K: f32 = 60.0;
    let mut scores: std::collections::HashMap<Uuid, f32> = std::collections::HashMap::new();
    for (list, weight) in lists {
        for (rank, id) in list.iter().enumerate() {
            *scores.entry(*id).or_insert(0.0) += weight / (K + rank as f32);
        }
    }
    scores
}

/// Drop the source-mean column from `get_incoming_edges` rows, yielding the
/// `(from, to, EdgeType, weight)` edge tuples the inference engine consumes.
fn strip_source_means(
    incoming: &[(Uuid, Uuid, EdgeType, Probability, f64)],
) -> Vec<(Uuid, Uuid, EdgeType, Probability)> {
    incoming
        .iter()
        .map(|&(from, to, et, w, _mean)| (from, to, et, w))
        .collect()
}

/// Build the external-source-mean map from `get_incoming_edges` rows: every edge
/// source NOT in the active set `ids` maps to its stored mean (carried inline by
/// the edge query, so no per-source follow-up query is needed).
fn external_means_from(
    incoming: &[(Uuid, Uuid, EdgeType, Probability, f64)],
    ids: &[Uuid],
) -> std::collections::HashMap<Uuid, f64> {
    let in_set: std::collections::HashSet<Uuid> = ids.iter().copied().collect();
    let mut ext = std::collections::HashMap::new();
    for &(from, _to, _et, _w, source_mean) in incoming {
        if !in_set.contains(&from) {
            ext.entry(from).or_insert(source_mean);
        }
    }
    ext
}

pub struct MimirStats {
    pub beliefs: usize,
    pub patterns: usize,
    pub supports: usize,
    pub defeats: usize,
    pub causes: usize,
    /// Raw directed-edge count.  CONTRADICTS is stored bidirectionally,
    /// so logical pairs = contradicts / 2.
    pub contradicts: usize,
}

/// A grounding passage: the document chunk backing a belief, with its strength.
#[derive(Debug, Clone)]
pub struct EvidenceRef {
    pub chunk_id: Uuid,
    pub document_path: String,
    pub section_path: Vec<String>,
    /// The chunk's content, trimmed.
    pub snippet: String,
    pub weight: f64,
}

/// A belief together with the document passages that ground it (Phase 4 C-core).
#[derive(Debug, Clone)]
pub struct GroundedBelief {
    pub belief: Belief,
    pub evidence: Vec<EvidenceRef>,
    pub sources: Vec<preparation::IndexedSupport>,
}

/// Omission requests all matches; a supplied count cannot be zero.
pub type Selection = Option<std::num::NonZeroUsize>;

#[cfg(test)]
extern crate self as mimir_core;

pub struct MimirService {
    store: AgeStore,
    database: config::DatabaseConfig,
    inference: InferenceEngine,
    embeddings: Option<OwnedEmbeddingBackend>,
    embedding_operation_settings: serde_json::Value,
    retirement: Option<toml::Value>,
}

impl MimirService {
    pub async fn connect(cfg: &Config) -> Result<Self> {
        let embeddings = cfg.embeddings.as_ref().map(make_backend).transpose()?;
        Self::connect_with_embeddings(cfg, embeddings).await
    }

    /// SDK hosts without a private worker entry point select the executable explicitly.
    pub async fn connect_with_worker(cfg: &Config, executable: std::path::PathBuf) -> Result<Self> {
        let embeddings = cfg
            .embeddings
            .as_ref()
            .map(|settings| embed::make_backend_with_worker(settings, executable.clone()))
            .transpose()?;
        Self::connect_with_embeddings(cfg, embeddings).await
    }

    async fn connect_with_embeddings(
        cfg: &Config,
        embeddings: Option<OwnedEmbeddingBackend>,
    ) -> Result<Self> {
        db::migrate(&cfg.database).await?;
        let client = db::connect(&cfg.database).await?;
        Ok(Self {
            store: AgeStore::new(client, cfg.database.dbname.clone())?,
            database: cfg.database.clone(),
            inference: InferenceEngine::new(),
            embeddings,
            embedding_operation_settings: preparation::operation_settings(cfg.embeddings.as_ref()),
            retirement: cfg.retirement.clone(),
        })
    }

    /// Capture the actual provider identity for a new operation binding.
    /// This does not expose credentials or select another provider.
    pub fn embedding_operation_settings(&self) -> serde_json::Value {
        self.embedding_operation_settings.clone()
    }

    /// Read the captured user policy without accessing business records.
    pub fn retirement_policy(
        &self,
    ) -> std::result::Result<config::RetirementPolicy, config::RetirementIssue> {
        config::retirement_policy(self.retirement.as_ref())
    }

    /// Publish a new belief only with an embedding and explicit indexed sources.
    pub async fn add_belief(
        &self,
        content: &str,
        probability: f64,
        confidence: f64,
        memory_type: MemoryType,
        grounding: &[preparation::IndexedSupport],
    ) -> Result<Belief> {
        self.add_prepared_belief(
            content,
            probability,
            confidence,
            None,
            memory_type,
            None,
            grounding,
        )
        .await
    }

    pub async fn add_belief_in_project(
        &self,
        content: &str,
        probability: f64,
        confidence: f64,
        project: &str,
        memory_type: MemoryType,
        grounding: &[preparation::IndexedSupport],
    ) -> Result<Belief> {
        self.add_prepared_belief(
            content,
            probability,
            confidence,
            Some(project),
            memory_type,
            None,
            grounding,
        )
        .await
    }

    pub async fn add_independent_belief(
        &self,
        content: &str,
        probability: f64,
        confidence: f64,
        project: Option<&str>,
        memory_type: MemoryType,
        provenance: &crate::learning::IndependentProvenance,
        grounding: &[preparation::IndexedSupport],
    ) -> Result<Belief> {
        self.add_prepared_belief(
            content,
            probability,
            confidence,
            project,
            memory_type,
            Some(provenance),
            grounding,
        )
        .await
    }

    async fn add_prepared_belief(
        &self,
        content: &str,
        probability: f64,
        confidence: f64,
        project: Option<&str>,
        memory_type: MemoryType,
        provenance: Option<&crate::learning::IndependentProvenance>,
        grounding: &[preparation::IndexedSupport],
    ) -> Result<Belief> {
        let prepared = self
            .prepare_belief(
                content,
                probability,
                confidence,
                project,
                memory_type,
                provenance,
                grounding,
            )
            .await?;
        self.publish_prepared_belief(&prepared).await
    }

    pub async fn prepare_belief(
        &self,
        content: &str,
        probability: f64,
        confidence: f64,
        project: Option<&str>,
        memory_type: MemoryType,
        provenance: Option<&crate::learning::IndependentProvenance>,
        grounding: &[preparation::IndexedSupport],
    ) -> Result<preparation::PreparedBelief> {
        if content.trim().is_empty() {
            return Err(preparation::PreparationRequired::new(interaction::Location::Arguments,
                vec![validation::Segment::Key("content".into())], validation::Code::EmptyText,
                "Supply the nonblank belief claim supported by the cited indexed passage. If the claim is unclear, open the user dialog; no belief was stored.".into()).into());
        }
        Probability::new(probability)?;
        Probability::new(confidence)?;
        if let Some(origin) = provenance {
            origin.validate()?;
        }
        let support = self
            .store
            .validate_indexed_support(project, grounding)
            .await?;
        let (id, created_at) = self.store.reserve_belief_preparation(project).await?;
        let (alpha, beta) = graph::prior_from(probability, confidence);
        let belief = Belief {
            id,
            content: content.into(),
            probability: Probability::new(probability)?,
            confidence: Probability::new(confidence)?,
            alpha,
            beta,
            alpha0: alpha,
            beta0: beta,
            created_at,
            last_activated_at: created_at,
            decay_accounted_at: created_at,
            memory_type,
            project: project.map(str::to_owned),
        };
        self.prepare_owned_belief(belief, provenance.cloned(), support)
            .await
    }

    async fn prepare_owned_belief(
        &self,
        belief: Belief,
        provenance: Option<crate::learning::IndependentProvenance>,
        support: Vec<preparation::ValidatedSupport>,
    ) -> Result<preparation::PreparedBelief> {
        use interaction::Location;
        use preparation::{PreparationRequired, PreparedBelief};
        use validation::{Code, Segment};
        let embedder = self.embeddings.as_ref().ok_or_else(|| {
            PreparationRequired::new(
                Location::Configuration,
                vec![Segment::Key("embeddings".into())],
                Code::MissingEvidence,
                "Embedding is not configured; no belief was stored.".into(),
            )
        })?;
        let vectors = self.embed_prepared_belief(embedder, &belief, &support).await.map_err(|error| {
            if error.is::<PreparationRequired>() || error.is::<embed::EmbeddingCancelled>() { return error; }
            PreparationRequired::new(Location::Configuration, vec![Segment::Key("embeddings".into())], Code::MissingEvidence,
                format!("Embedding preparation failed before publication: {error:#}. No belief was stored.")).into()
        })?;
        let vector = match vectors.as_slice() {
            [vector] if preparation::usable_vector(vector) => vector.clone(),
            _ => return Err(PreparationRequired::new(Location::Configuration, vec![Segment::Key("embeddings".into())], Code::MissingEvidence,
                "The backend must return exactly one complete, finite, nonzero vector for this belief; no belief was stored.".into()).into()),
        };
        Ok(PreparedBelief {
            belief,
            provenance,
            vector,
            support,
        })
    }

    /// Resume the same PostgreSQL owner; successful readback precedes all new
    /// source checks or provider work. Publication and original answer commit together.
    pub async fn publish_belief_operation(
        &self,
        plan: &store::OperationPlan,
    ) -> Result<store::StepDecision> {
        match self
            .store
            .resume_belief_operation(plan, &self.embedding_operation_settings())
            .await?
        {
            store::BeliefPublicationState::Resolved(result) => Ok(result),
            store::BeliefPublicationState::Preparing {
                final_step,
                belief,
                provenance,
                grounding,
            } => {
                let support = self
                    .store
                    .validate_indexed_support(belief.project.as_deref(), &grounding)
                    .await?;
                let prepared = self
                    .prepare_owned_belief(belief, Some(provenance), support)
                    .await?;
                self.store
                    .publish_belief_operation(&final_step, &prepared)
                    .await
            }
        }
    }

    async fn embed_prepared_belief(
        &self,
        embedder: &OwnedEmbeddingBackend,
        belief: &Belief,
        support: &[preparation::ValidatedSupport],
    ) -> Result<Vec<Vec<f32>>> {
        use interaction::Location;
        use preparation::PreparationRequired;
        use validation::Code;
        let stopped = |cause: String| {
            PreparationRequired::new(
            Location::Request, vec![], Code::MissingReference,
            format!("Preparation {} stopped before publication: {cause}. No belief was stored. Read its original state and ask the user before starting new work.", belief.id))
        };
        // Subscribe first: revocation before the first read is seen in that
        // read, and revocation afterward leaves an event for this wait.
        let mut changes = db::EmbeddingOwnerSubscription::connect(&self.database)
            .await
            .map_err(|error| stopped(format!("cannot observe ownership changes: {error:#}")))?;
        if !self.store.preparation_is_current(belief, support).await? {
            return Err(stopped(
                "publication ownership was revoked or a cited indexed passage changed".into(),
            )
            .into());
        }
        let job = embedder.embed(std::slice::from_ref(&belief.content));
        tokio::pin!(job);
        loop {
            tokio::select! {
                biased;
                change = changes.changed() => {
                    change.map_err(|error| stopped(format!("ownership monitoring disconnected: {error:#}")))?;
                    if !self.store.preparation_is_current(belief, support).await? {
                        // Returning drops the owned provider future. A local
                        // worker is killed and reaped before this returns.
                        return Err(stopped("publication ownership was revoked or a cited indexed passage changed".into()).into());
                    }
                }
                result = &mut job => return result,
            }
        }
    }

    pub async fn publish_prepared_belief(
        &self,
        prepared: &preparation::PreparedBelief,
    ) -> Result<Belief> {
        self.store.publish_prepared_belief(prepared).await
    }

    /// Embed a belief's content and upsert the vector into `belief_embeddings`
    /// when an embedding backend is configured. Missing configuration or an
    /// incomplete/unusable backend result requests a user decision before writing.
    /// Backfills existing beliefs. New belief insertion instead requires both
    /// embedding and indexed grounding before one atomic publication.
    pub async fn embed_and_store_belief(&self, belief: &Belief) -> Result<()> {
        let Some(embedder) = &self.embeddings else {
            return Err(preparation::PreparationRequired::backfill(
                validation::Code::MissingEvidence,
                "Embedding is not configured; this belief's vector was not written.".into(),
            )
            .into());
        };
        let vectors = self.embed_existing_belief(embedder, belief, None).await?;
        let [vector] = vectors.as_slice() else {
            return Err(preparation::PreparationRequired::backfill(validation::Code::MalformedInput,
                format!("The backend must return exactly one vector for this belief, but returned {}; its vector was not written.",vectors.len())).into());
        };
        if !preparation::usable_vector(vector) {
            return Err(preparation::PreparationRequired::backfill(validation::Code::InvalidNumber,
                "The backend returned an empty, nonfinite, or zero vector; this belief's vector was not written.".into()).into());
        }
        self.store
            .insert_belief_embedding(belief.id, vector)
            .await?;
        Ok(())
    }

    async fn embed_existing_belief(
        &self,
        embedder: &OwnedEmbeddingBackend,
        belief: &Belief,
        operation_token: Option<Uuid>,
    ) -> Result<Vec<Vec<f32>>> {
        // The subscription precedes the first target read: deletion either
        // appears in that read or leaves a notification for this exact job.
        let mut changes = db::EmbeddingOwnerSubscription::connect(&self.database).await?;
        self.check_backfill_cancellation(operation_token).await?;
        if self.store.get_belief(belief.id).await?.is_none() {
            return Err(store::BeliefEmbeddingTargetMissing {
                belief_id: belief.id,
            }
            .into());
        }
        let job = embedder.embed(std::slice::from_ref(&belief.content));
        tokio::pin!(job);
        loop {
            tokio::select! {
                biased;
                change = changes.changed() => {
                    // A disconnected monitor cannot establish continued
                    // ownership; returning drops this call's provider future.
                    change?;
                    self.check_backfill_cancellation(operation_token).await?;
                    if self.store.get_belief(belief.id).await?.is_none() {
                        return Err(store::BeliefEmbeddingTargetMissing { belief_id: belief.id }.into());
                    }
                }
                result = &mut job => return result,
            }
        }
    }

    async fn check_backfill_cancellation(&self, token: Option<Uuid>) -> Result<()> {
        if let Some(token) = token {
            if self
                .store
                .read_operation_cancellation(token)
                .await?
                .is_some()
            {
                return Err(preparation::PreparationRequired::backfill(
                    validation::Code::MissingReference,
                    format!("Backfill operation {token} was explicitly cancelled. Its owned embedding stopped; no result from this job may be published. Read the original saved answers and discuss any new work with the user."),
                ).into());
            }
        }
        Ok(())
    }

    /// Belief IDs that already have a vector stored in `belief_embeddings`.
    /// Used by the `reembed` CLI to skip beliefs whose vectors are already
    /// populated (idempotent backfill).
    pub async fn list_embedded_belief_ids(&self) -> Result<Vec<Uuid>> {
        self.store.list_embedded_belief_ids().await
    }

    /// Delete a belief and all its edges by ID. Returns true if found.
    pub async fn delete_belief(&self, id: Uuid) -> Result<bool> {
        self.store.delete_belief(id).await
    }

    pub async fn delete_belief_operation(
        &self,
        step: &store::RegisteredStep,
    ) -> Result<store::StepDecision> {
        self.store.delete_belief_operation(step).await
    }

    /// Delete all beliefs and DocumentChunks tagged with the given project.
    /// Returns the combined count of vertices removed.
    pub async fn delete_project(&self, project: &str) -> Result<usize> {
        self.store.delete_project(project).await
    }

    pub async fn delete_project_operation(
        &self,
        step: &store::RegisteredStep,
    ) -> Result<store::StepDecision> {
        self.store.delete_project_operation(step).await
    }

    /// Get a pattern by ID.
    pub async fn get_pattern(&self, id: Uuid) -> Result<Option<Pattern>> {
        self.store.get_pattern(id).await
    }

    /// Delete a pattern and all its edges by ID. Returns true if found.
    pub async fn delete_pattern(&self, id: Uuid) -> Result<bool> {
        self.store.delete_pattern(id).await
    }

    pub async fn delete_pattern_operation(
        &self,
        step: &store::RegisteredStep,
    ) -> Result<store::StepDecision> {
        self.store.delete_pattern_operation(step).await
    }

    /// Publish the original registered pattern and save its complete answer.
    pub async fn create_pattern_operation(
        &self,
        step: &store::RegisteredStep,
    ) -> Result<store::StepDecision> {
        self.store.create_pattern_operation(step).await
    }

    /// Publish a registered support, cause or bidirectional contradiction.
    pub async fn direct_relationship_operation(
        &self,
        step: &store::RegisteredStep,
    ) -> Result<store::StepDecision> {
        self.store.direct_relationship_operation(step).await
    }

    /// Add a new pattern.
    pub async fn add_pattern(
        &self,
        situation: &str,
        approach: &str,
        success_rate: f64,
    ) -> Result<Pattern> {
        self.store
            .create_pattern(situation, approach, success_rate, None)
            .await
    }

    /// Add an edge between two beliefs. Validates both exist.
    /// For CONTRADICTS, inserts bidirectionally.
    /// For DEFEATS, inserts the edge then triggers defeat propagation from from_id.
    pub async fn add_edge(
        &self,
        from_id: Uuid,
        to_id: Uuid,
        edge_type: EdgeType,
        weight: f64,
    ) -> Result<()> {
        let w = Probability::new(weight)?;
        if edge_type == EdgeType::Contradicts {
            self.store.insert_contradicts(from_id, to_id, w).await?;
        } else {
            let edge = graph::Edge::new(from_id, to_id, edge_type, weight)?;
            self.store.insert_edge(&edge).await?;
            if edge_type == EdgeType::Defeats {
                if let Err(error) = self.propagate_from(from_id).await {
                    if let Some(decision) = error.downcast_ref::<inference::NumericalDecision>() {
                        return Err(inference::EdgeCommittedDecision::new(
                            from_id, to_id, weight, decision,
                        )
                        .into());
                    }
                    return Err(error);
                }
            }
        }
        Ok(())
    }

    /// Get a belief by ID.
    pub async fn get_belief(&self, id: Uuid) -> Result<Option<Belief>> {
        self.store.get_belief(id).await
    }

    /// List beliefs. When `project` is given, restricts to beliefs tagged with
    /// that project plus untagged (global) beliefs; `None` lists everything.
    pub async fn list_beliefs(&self, project: Option<&str>) -> Result<Vec<Belief>> {
        self.list_beliefs_filtered(project, None).await
    }

    /// Like `list_beliefs`, with an optional `memory_type` filter. Used by the
    /// consolidation workflow to find orphaned Working beliefs (e.g. left behind
    /// by an interrupted prior session) without pulling the whole scope through
    /// context. NOTE: this filters by type only — it has no session-identity
    /// concept, so on a shared DB with concurrent sessions it cannot distinguish
    /// "my session's" Working beliefs from another session's in-flight ones.
    /// A session should track the IDs of the Working beliefs it itself wrote
    /// (already known from its own insert_belief calls) as the primary
    /// consolidation mechanism; this filter is for orphan cleanup only.
    pub async fn list_beliefs_filtered(
        &self,
        project: Option<&str>,
        memory_type: Option<graph::MemoryType>,
    ) -> Result<Vec<Belief>> {
        let all = match project {
            Some(p) => self.store.list_beliefs_by_project(p).await?,
            None => self.store.list_beliefs().await?,
        };
        Ok(match memory_type {
            Some(mt) => all.into_iter().filter(|b| b.memory_type == mt).collect(),
            None => all,
        })
    }

    pub async fn list_beliefs_page(
        &self,
        project: Option<&str>,
        memory_type: Option<MemoryType>,
        limit: usize,
        offset: usize,
    ) -> Result<serde_json::Value> {
        let (beliefs, total) = self
            .store
            .list_beliefs_page(project, memory_type, limit, offset)
            .await?;
        let end = offset.saturating_add(beliefs.len());
        Ok(
            serde_json::json!({"beliefs":beliefs,"total":total,"offset":offset,"next_offset":(end<total).then_some(end)}),
        )
    }

    /// List patterns. Same project-scoping semantics as `list_beliefs`.
    pub async fn list_patterns(&self, project: Option<&str>) -> Result<Vec<Pattern>> {
        match project {
            Some(p) => self.store.list_patterns_by_project(p).await,
            None => self.store.list_patterns().await,
        }
    }

    /// Run defeat propagation from a seed belief ID.
    /// Loads the downstream subgraph and all edges among it, applies attenuate/boost,
    /// and writes updated probabilities back to the store.
    pub async fn propagate_from(&self, seed_id: Uuid) -> Result<Vec<(Uuid, Probability)>> {
        self.store.propagate_locked(seed_id).await
    }

    /// Resume the original propagation and save its complete answer atomically.
    pub async fn propagate_operation(
        &self,
        step: &store::RegisteredStep,
    ) -> Result<store::StepDecision> {
        self.store.propagate_operation(step).await
    }

    /// Resume a defeat plan without writing its committed edge again.
    pub async fn record_defeat_operation(
        &self,
        plan: &store::OperationPlan,
    ) -> Result<store::StepDecision> {
        self.store.record_defeat_operation(plan).await
    }

    /// Counterfactual projection P(· | do(target = value)). Read-only: computes
    /// and returns projected probabilities for the causal descendants of
    /// `target`; does NOT write to the store. Contrast `propagate_from`, which
    /// mutates. The do-operator severs `target`'s incoming edges and propagates
    /// along CAUSES edges only (see `InferenceEngine::intervene`).
    pub async fn query_intervention(
        &self,
        target_id: Uuid,
        value: f64,
    ) -> Result<Vec<(Uuid, Probability)>> {
        self.intervention_after_target(target_id, value, || async { Ok(()) })
            .await
    }

    pub(crate) async fn intervention_after_target<F, W>(
        &self,
        target_id: Uuid,
        value: f64,
        after_target: F,
    ) -> Result<Vec<(Uuid, Probability)>>
    where
        F: FnOnce() -> W,
        W: std::future::Future<Output = Result<()>>,
    {
        self.intervention_snapshot_after_target(target_id, value, false, after_target)
            .await
            .map(|(updates, _)| updates)
    }

    /// The CLI's projected values and displayed belief text share one view.
    /// Existing public query responses still contain only projected values.
    pub async fn query_intervention_with_beliefs(
        &self,
        target_id: Uuid,
        value: f64,
    ) -> Result<(Vec<(Uuid, Probability)>, Vec<Belief>)> {
        self.intervention_snapshot_after_target(target_id, value, true, || async { Ok(()) })
            .await
    }

    pub(crate) async fn intervention_snapshot_after_target<F, W>(
        &self,
        target_id: Uuid,
        value: f64,
        include_beliefs: bool,
        after_target: F,
    ) -> Result<(Vec<(Uuid, Probability)>, Vec<Belief>)>
    where
        F: FnOnce() -> W,
        W: std::future::Future<Output = Result<()>>,
    {
        let value = Probability::new(value)?;
        let mut client = self.store.snapshot_connection().await;
        let tx = store::snapshot_transaction(&mut client).await?;
        if self
            .store
            .get_belief_on(tx.client(), target_id)
            .await?
            .is_none()
        {
            return Err(interaction::RequestCorrection::missing_reference(
                "id", format!("The requested belief {target_id} was not found in Mimir."),
                "Use list_beliefs or query_relevant_beliefs to find the intended stored belief, then retry with its ID. If the intended record is unknown, ask the user. Do not invent an identifier.",
            ).into());
        }
        after_target().await?;
        let mut downstream = self
            .store
            .downstream_on(tx.client(), target_id, true)
            .await?;
        // Keep physical belief values before adding the temporary numerical
        // overlay. They are the same records a lookup in this view returns.
        let beliefs = if include_beliefs {
            downstream.clone()
        } else {
            Vec::new()
        };
        let (learning_mass, _) = self.store.learning_overlay_on(tx.client()).await?;
        let grounding_mass = self.store.get_grounding_mass_all_on(tx.client()).await?;
        for belief in &mut downstream {
            belief.alpha0 += grounding_mass.get(&belief.id).copied().unwrap_or(0.0);
            if let Some((a, b)) = learning_mass.get(&belief.id) {
                belief.alpha0 += a;
                belief.beta0 += b;
            }
        }
        let mut ids: Vec<Uuid> = downstream.iter().map(|b| b.id).collect();
        ids.push(target_id);
        // Complete incoming edges of every descendant, with source means — so a
        // genuine CO-CAUSE outside the descendant set still counts (spec
        // Mimir.Inference keep-causes-into-nontarget). Surgery (in `intervene`)
        // then cuts only edges INTO the target.
        let incoming = self.store.get_incoming_edges_on(tx.client(), &ids).await?;
        let edges = strip_source_means(&incoming);
        let external_means = external_means_from(&incoming, &ids);
        // No writeback — this is a hypothetical projection.
        let result =
            self.inference
                .intervene(target_id, value, &downstream, &edges, &external_means)?;
        tx.commit().await?;
        Ok((result, beliefs))
    }

    /// Get active contradictions in the graph. Project-scoped the same way as
    /// `list_beliefs`: a pair is included only if both endpoints are visible
    /// in scope (tagged with `project` or untagged).
    pub async fn get_contradictions(&self, project: Option<&str>) -> Result<Vec<(Uuid, Uuid)>> {
        self.get_contradictions_with_beliefs(project)
            .await
            .map(|(pairs, _)| pairs)
    }

    /// Return active pairs and their original-view records for CLI display.
    pub async fn get_contradictions_with_beliefs(
        &self,
        project: Option<&str>,
    ) -> Result<(Vec<(Uuid, Uuid)>, Vec<Belief>)> {
        let (pairs, beliefs) = self.store.contradictions_snapshot(project).await?;
        Ok(self.active_contradiction_details(pairs, beliefs))
    }

    #[cfg(test)]
    pub(crate) async fn contradictions_with_beliefs_after_pairs<F, W>(
        &self,
        project: Option<&str>,
        after_pairs: F,
    ) -> Result<(Vec<(Uuid, Uuid)>, Vec<Belief>)>
    where
        F: FnOnce() -> W,
        W: std::future::Future<Output = Result<()>>,
    {
        let (pairs, beliefs) = self
            .store
            .contradictions_after_pairs(project, after_pairs)
            .await?;
        Ok(self.active_contradiction_details(pairs, beliefs))
    }

    fn active_contradiction_details(
        &self,
        pairs: Vec<(Uuid, Uuid)>,
        beliefs: Vec<Belief>,
    ) -> (Vec<(Uuid, Uuid)>, Vec<Belief>) {
        let belief_map: std::collections::HashMap<Uuid, &Belief> =
            beliefs.iter().map(|b| (b.id, b)).collect();

        let active = self
            .inference
            .detect_active_contradictions(&belief_map, &pairs);
        (active, beliefs)
    }

    /// Apply time decay to beliefs, write updates. `project`, when given,
    /// restricts the sweep to that project's beliefs plus untagged (global)
    /// beliefs (same semantics as `list_beliefs`) — a caller working in one
    /// project should not silently perturb another project's beliefs.
    /// decay_factor defaults to 0.99 (~1% per day) if not provided.
    /// Grounded beliefs resist decay in proportion to their total grounding mass
    /// (spec Mimir.Beta CCoupling.coupling-increases-strength).
    pub async fn decay_beliefs(
        &self,
        decay_factor: Option<f64>,
        project: Option<&str>,
    ) -> Result<usize> {
        self.store
            .decay_locked(decay_factor.unwrap_or(0.99), project)
            .await
    }

    pub async fn decay_operation(
        &self,
        step: &store::RegisteredStep,
    ) -> Result<store::StepDecision> {
        self.store.decay_operation(step).await
    }

    /// Delete defeated beliefs whose grace period has elapsed (attenuated
    /// deletion, not immediate hard deletion at record_defeat time). A
    /// defeated belief is deleted only once its probability has
    /// decayed below `prob_threshold` AND `grace_period` has passed since it
    /// was first defeated, with no intervening reversal — this gives a wrong
    /// `record_defeat` call time to be caught and reversed before its target
    /// is permanently removed. `project`, when given, restricts the sweep to
    /// that project's beliefs plus untagged (global) ones, same semantics as
    /// `decay_beliefs` — a caller working in one project should not silently
    /// delete another project's beliefs. Returns the number of beliefs deleted.
    pub async fn sweep_expired_defeated(
        &self,
        prob_threshold: f64,
        project: Option<&str>,
    ) -> Result<usize> {
        if !prob_threshold.is_finite() || !(0.0..=1.0).contains(&prob_threshold) {
            return Err(validation::Refusal::invalid(
                validation::Code::InvalidNumber,
                vec![validation::Segment::Key("prob_threshold".into())],
                "Supply a finite probability between 0 and 1 inclusive; no beliefs were read or deleted.",
            ).into());
        }
        let policy = self.retirement_policy()?;
        self.store
            .sweep_expired_defeated(prob_threshold, project, &policy)
            .await
    }

    /// Hybrid retrieval ranked by weighted Reciprocal Rank Fusion.
    ///
    /// Candidate selection: the union of (a) token/keyword matches (beliefs whose
    /// lowercased content contains a query term, ranked by distinct-term match
    /// count) and (b) vector cosine top-k over `belief_embeddings` (when an
    /// embedding backend is configured; empty otherwise), expanded along
    /// SUPPORTS/CAUSES edges.
    ///
    /// Final order: weighted RRF over THREE ranked lists — semantic (vector),
    /// lexical (token), and the belief-probability PRIOR (candidates by
    /// probability desc). RRF fuses ranks (scale-agnostic); the weights let the
    /// reliable semantic leg lead while probability remains a real ranking signal
    /// rather than a tiebreaker or a naked multiply. Spec: `Mimir.Graph`
    /// (query_relevant section). Omitted selection means all matches.
    /// `project`, when given, restricts the candidate pool (token, vector,
    /// probability-prior, and graph-expansion legs) to beliefs tagged with
    /// that project plus untagged (global) beliefs — see `list_beliefs`.
    pub async fn query_relevant(
        &self,
        query: &str,
        limit: Selection,
        project: Option<&str>,
        prefer_type: Option<MemoryType>,
    ) -> Result<RetrievalReport<Belief>> {
        self.relevant_after_overlay(query, limit, project, prefer_type, || async { Ok(()) })
            .await
    }

    pub(crate) async fn relevant_after_overlay<F, W>(
        &self,
        query: &str,
        limit: Selection,
        project: Option<&str>,
        prefer_type: Option<MemoryType>,
        after_overlay: F,
    ) -> Result<RetrievalReport<Belief>>
    where
        F: FnOnce() -> W,
        W: std::future::Future<Output = Result<()>>,
    {
        let mut client = self.store.snapshot_connection().await;
        let tx = store::snapshot_transaction(&mut client).await?;
        let result = self
            .relevant_on(
                tx.client(),
                query,
                limit,
                project,
                prefer_type,
                after_overlay,
            )
            .await?;
        tx.commit().await?;
        Ok(result)
    }

    async fn relevant_on<F, W>(
        &self,
        client: &tokio_postgres::Client,
        query: &str,
        limit: Selection,
        project: Option<&str>,
        prefer_type: Option<MemoryType>,
        after_overlay: F,
    ) -> Result<RetrievalReport<Belief>>
    where
        F: FnOnce() -> W,
        W: std::future::Future<Output = Result<()>>,
    {
        let (_, superseded) = self.store.learning_overlay_on(client).await?;
        after_overlay().await?;
        let all: Vec<Belief> = match project {
            Some(p) => self.store.list_beliefs_by_project_on(client, p).await?,
            None => self.store.list_beliefs_on(client).await?,
        }
        .into_iter()
        // Working memory is task-local scratch, excluded from cross-session
        // retrieval entirely (see the `MemoryType` doc comment).
        .filter(|b| b.memory_type != MemoryType::Working && !superseded.contains(&b.id))
        .collect();
        if all.is_empty() {
            return Ok(RetrievalReport {
                beliefs: vec![],
                retrieval: RetrievalCoverage::observed(
                    query,
                    SemanticObservation::NoEligibleBeliefs,
                ),
            });
        }

        // ── Token list: beliefs whose lowercased content contains at least one
        //    query term, ranked by distinct-term match count desc (tiebreak:
        //    probability desc).
        let q_lower = query.to_lowercase();
        let terms: Vec<String> = q_lower
            .split_whitespace()
            .filter(|s| !s.is_empty())
            .map(|s| s.to_string())
            .collect();
        let token_ranked: Vec<Uuid> = if terms.is_empty() {
            Vec::new()
        } else {
            let mut scored: Vec<(usize, &Belief)> = all
                .iter()
                .filter_map(|b| {
                    let content_lower = b.content.to_lowercase();
                    let hits = terms
                        .iter()
                        .filter(|t| content_lower.contains(t.as_str()))
                        .count();
                    if hits > 0 {
                        Some((hits, b))
                    } else {
                        None
                    }
                })
                .collect();
            scored.sort_by(|a, b| {
                b.0.cmp(&a.0)
                    .then_with(|| {
                        b.1.probability
                            .value()
                            .partial_cmp(&a.1.probability.value())
                            .unwrap_or(std::cmp::Ordering::Equal)
                    })
                    .then_with(|| a.1.id.cmp(&b.1.id))
            });
            scored.into_iter().map(|(_, b)| b.id).collect()
        };

        // ── Vector list: all eligible vectors participate in fusion.
        // Only the caller's final selection cuts the returned ranking. Every
        // unavailable semantic leg remains visible in the returned report.
        let (vector_ranked, semantic): (Vec<Uuid>, SemanticObservation) =
            if let Some(embedder) = &self.embeddings {
                match embedder.embed(&[query.to_string()]).await {
                    Ok(mut vecs)
                        if vecs.len() == 1
                            && !vecs[0].is_empty()
                            && vecs[0].iter().all(|value| value.is_finite())
                            && vecs[0].iter().any(|value| *value != 0.0) =>
                    {
                        let qv = vecs
                            .pop()
                            .expect("the exact one-query response was checked");
                        let ranked = match project {
                            Some(_) => {
                                let ids: Vec<Uuid> = all.iter().map(|b| b.id).collect();
                                self.store
                                    .query_beliefs_by_vector_filtered_on(client, &qv, None, &ids)
                                    .await?
                            }
                            None => {
                                self.store
                                    .query_beliefs_by_vector_on(client, &qv, None)
                                    .await?
                            }
                        };
                        (ranked, SemanticObservation::Evaluated)
                    }
                    Ok(vecs) => {
                        let cause = if vecs.is_empty() {
                            "The backend returned no query embedding."
                        } else if vecs.len() != 1 {
                            "The backend returned multiple embeddings for one submitted context."
                        } else if vecs[0].is_empty() {
                            "The query embedding is empty."
                        } else if !vecs[0].iter().all(|value| value.is_finite()) {
                            "The query embedding contains a non-finite value."
                        } else {
                            "The query embedding has zero norm, so cosine similarity is undefined."
                        };
                        (
                            Vec::new(),
                            SemanticObservation::UnusableQueryVector(cause.into()),
                        )
                    }
                    Err(error) => (
                        Vec::new(),
                        SemanticObservation::EmbeddingFailed(format!("{error:#}")),
                    ),
                }
            } else {
                (Vec::new(), SemanticObservation::Unconfigured)
            };

        // ── Candidate seed set: the deduplicated union of the token and vector
        //    lists (final order is decided later by weighted RRF, so only
        //    membership matters here). token_ranked / vector_ranked stay owned for
        //    that fusion.
        let mut seen = std::collections::HashSet::new();
        let seed_ids: Vec<Uuid> = token_ranked
            .iter()
            .chain(vector_ranked.iter())
            .copied()
            .filter(|id| seen.insert(*id))
            .collect();
        if seed_ids.is_empty() {
            return Ok(RetrievalReport {
                beliefs: vec![],
                retrieval: RetrievalCoverage::observed(query, semantic),
            });
        }

        // ── Materialise the candidate beliefs from the already-loaded list.
        let by_id: std::collections::HashMap<Uuid, &Belief> =
            all.iter().map(|b| (b.id, b)).collect();
        let mut matched: Vec<Belief> = seed_ids
            .iter()
            .filter_map(|id| by_id.get(id).map(|&b| b.clone()))
            .collect();

        // ── Graph expansion: SUPPORTS/CAUSES reachable beliefs (unchanged).
        let matched_ids: Vec<Uuid> = matched.iter().map(|b| b.id).collect();
        for id in matched_ids {
            match project {
                Some(p) => {
                    // Hop-by-hop BFS through in-scope nodes only, so a node
                    // reached solely via an out-of-scope intermediate is
                    // correctly excluded — AGE can't express per-hop-node
                    // filtering inside one variable-length-path query (see
                    // get_direct_downstream_by_project's doc comment), so the
                    // unbounded closure `get_downstream_beliefs` + an
                    // endpoint-only filter would admit that bridging case.
                    let mut visited: std::collections::HashSet<Uuid> =
                        matched.iter().map(|m| m.id).collect();
                    visited.insert(id);
                    let mut frontier = vec![id];
                    while !frontier.is_empty() {
                        let mut next_frontier = Vec::new();
                        for fid in frontier {
                            let mut neighbors = self
                                .store
                                .direct_downstream_by_project_on(client, fid, p)
                                .await?;
                            neighbors.sort_by_key(|belief| belief.id);
                            for b in neighbors {
                                if b.memory_type == MemoryType::Working
                                    || superseded.contains(&b.id)
                                {
                                    continue;
                                }
                                if visited.insert(b.id) {
                                    next_frontier.push(b.id);
                                    matched.push(b);
                                }
                            }
                        }
                        frontier = next_frontier;
                    }
                }
                None => {
                    let downstream = self.store.downstream_on(client, id, false).await?;
                    for b in downstream {
                        if b.memory_type == MemoryType::Working || superseded.contains(&b.id) {
                            continue;
                        }
                        if !matched.iter().any(|m| m.id == b.id) {
                            matched.push(b);
                        }
                    }
                }
            }
        }

        // ── Final ranking: weighted Reciprocal Rank Fusion of THREE ranked lists
        //    — semantic (vector), lexical (token), and the belief-probability
        //    PRIOR. RRF is score-agnostic: it fuses RANKS, sidestepping the
        //    mutually-incompatible cosine / token-count / probability scales
        //    (Cormack 2009; the standard hybrid-search fusion). Per-list weights
        //    let the reliable semantic leg lead while the probability prior stays a
        //    GENUINE ranking signal — a full ranked list, not a tiebreaker and not
        //    the old unprincipled `rrf_score × probability` (which multiplied a
        //    rank-reciprocal by a probability and so let a slightly-higher-p but
        //    irrelevant belief bury a strong semantic match). Folding a static
        //    quality/prior signal in as a weighted retriever is the documented
        //    Elastic weighted-RRF approach.
        // Weights reflect each signal's reliability: the semantic (vector) leg is
        // the trustworthy relevance signal and leads; the substring token leg is
        // noisy (it matches common words) so it only supplements; the probability
        // prior is a gentle nudge — enough to reorder similarly-relevant beliefs,
        // never enough to lift an irrelevant-but-confident belief over a strong
        // semantic match (the exact failure of the old `rrf × probability`).
        const W_VECTOR: f32 = 1.0;
        const W_TOKEN: f32 = 0.3;
        const W_PRIOR: f32 = 0.1;
        // Type-preference leg: only present when the caller passes prefer_type.
        // Deliberately higher than W_TOKEN+W_PRIOR combined (0.4), not just
        // W_PRIOR alone: token and prior are both derived from the same
        // underlying candidate order, so near-duplicate/tied beliefs (the
        // common case this feature targets — see the DEFEATS/redundancy work
        // in section 1/2 of the same doc) inherit a correlated tie-break bias
        // from BOTH legs at once. A weight matching only W_PRIOR (0.1) is
        // invisible against that combined ~0.0001 bias — verified by a failing
        // test at 0.1 before this was raised. 0.5 clears the combined bias
        // with margin while staying far below W_VECTOR (1.0), so a real
        // semantic match still always wins over type preference alone.
        const W_TYPE: f32 = 0.5;
        // Prior list: the candidate set ranked by probability descending.
        let prob_of: std::collections::HashMap<Uuid, f64> = matched
            .iter()
            .map(|b| (b.id, b.probability.value()))
            .collect();
        let mut prior_ranked: Vec<Uuid> = matched.iter().map(|b| b.id).collect();
        prior_ranked.sort_by(|a, b| {
            prob_of[b]
                .partial_cmp(&prob_of[a])
                .unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| a.cmp(b))
        });
        // Type-preference list: matching-type beliefs first (stable order
        // preserved within each half), so they occupy the low-rank/high-weight
        // slots of this list without affecting the other two legs at all.
        let type_ranked: Vec<Uuid> = match prefer_type {
            Some(pt) => {
                let (mut preferred, mut rest): (Vec<Uuid>, Vec<Uuid>) = (Vec::new(), Vec::new());
                for b in &matched {
                    if b.memory_type == pt {
                        preferred.push(b.id);
                    } else {
                        rest.push(b.id);
                    }
                }
                preferred.append(&mut rest);
                preferred
            }
            None => Vec::new(),
        };
        let fused = weighted_rrf(&[
            (vector_ranked.as_slice(), W_VECTOR),
            (token_ranked.as_slice(), W_TOKEN),
            (prior_ranked.as_slice(), W_PRIOR),
            (type_ranked.as_slice(), W_TYPE),
        ]);
        matched.sort_by(|a, b| {
            let sa = fused.get(&a.id).copied().unwrap_or(0.0);
            let sb = fused.get(&b.id).copied().unwrap_or(0.0);
            sb.partial_cmp(&sa)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| a.id.cmp(&b.id))
        });

        if let Some(count) = limit {
            matched.truncate(count.get());
        }
        Ok(RetrievalReport {
            beliefs: matched,
            retrieval: RetrievalCoverage::observed(query, semantic),
        })
    }

    // -----------------------------------------------------------------------
    // Document RAG
    // -----------------------------------------------------------------------

    /// Parse a markdown file into chunks, embed each one, and store in AGE +
    /// chunk_embeddings.  Replaces any existing chunks for the same path.
    /// Returns the number of chunks loaded.
    ///
    /// `path` is canonicalized before use as the document identity key (both
    /// for the replace-on-reload lookup and for the stored `documentPath`).
    /// Document identity in the store is an exact string match on
    /// `documentPath` (`AgeStore::get_chunk_ids_for_document`) with no
    /// normalization of its own — without canonicalizing here, loading the
    /// same file via a relative path and later via an absolute path (or any
    /// two distinct spellings of the same file) creates two independent
    /// chunk sets instead of replacing one, since neither string matches the
    /// other. Canonicalizing collapses that to one identity per real file.
    pub async fn load_document(&self, path: &str, project: Option<&str>) -> Result<usize> {
        let embedder = self.embeddings.as_ref().ok_or_else(|| {
            anyhow::anyhow!("embeddings not configured — add [embeddings] to config.toml")
        })?;

        let canonical = std::fs::canonicalize(path)
            .map_err(|e| anyhow::anyhow!("cannot resolve {}: {}", path, e))?;
        let path = canonical.to_string_lossy().into_owned();
        let path = path.as_str();

        let text = std::fs::read_to_string(path)
            .map_err(|e| anyhow::anyhow!("cannot read {}: {}", path, e))?;

        let chunks = parse_markdown(&text, path, project);
        let count = chunks.len();

        // Embed all chunks in one batch call where possible.
        let texts: Vec<String> = chunks.iter().map(|c| c.content.clone()).collect();
        let embeddings = embedder.embed(&texts).await?;

        // DocumentLoading: preparation precedes one paired publication.
        self.store
            .replace_document(path, &chunks, &embeddings)
            .await?;

        // Indexing makes passages available for explicit citations. Similarity
        // alone does not assert that a passage supports any existing belief.

        Ok(count)
    }

    /// Remove all chunks (and their embeddings) for the given document path.
    /// Returns the number of chunks cleared. Returns 0 if never loaded.
    ///
    /// Attempts the same canonicalization `load_document` applies, so
    /// `clear_document` can be called with any path spelling that resolves
    /// to the same file `load_document` stored it under. Falls back to the
    /// raw path string if canonicalization fails (e.g. the file was deleted
    /// after loading) — that only matches a chunk set stored under that
    /// exact raw path, same limitation clear_document always had.
    pub async fn clear_document(&self, path: &str) -> Result<usize> {
        let canonical_owned;
        let path: &str = match std::fs::canonicalize(path) {
            Ok(p) => {
                canonical_owned = p.to_string_lossy().into_owned();
                canonical_owned.as_str()
            }
            Err(_) => path,
        };
        self.store.clear_document(path).await
    }

    /// Capture the existing path-resolution result once, retaining the caller's
    /// original argument separately. This server-owned preparation precedes
    /// binding; no later retry resolves the path again.
    pub fn clear_document_request(&self, path: &str) -> Result<store::OperationBindingRequest> {
        let resolved = std::fs::canonicalize(path)
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|_| path.to_owned());
        store::OperationBindingRequest::new(
            "clear_document".into(),
            serde_json::json!({"path":path}),
            serde_json::json!({"resolved_path":resolved}),
        )
    }

    pub async fn clear_document_operation(
        &self,
        step: &store::RegisteredStep,
    ) -> Result<store::StepDecision> {
        self.store.clear_document_operation(step).await
    }

    /// Semantic search over loaded document chunks.
    /// Embeds `context`, queries chunk_embeddings by cosine distance, fetches
    /// matching DocumentChunk vertices from AGE, enriches with parent content.
    /// Omitted selection means all matches.
    pub async fn query_document(
        &self,
        context: &str,
        project: Option<&str>,
        limit: Selection,
    ) -> Result<Vec<QueryResult>> {
        use interaction::RequestCorrection;
        use validation::Code;
        let embedder = self.embeddings.as_ref().ok_or_else(|| {
            RequestCorrection::document_query_embedding(
                Code::MissingField,
                "Document queries require a configured embedding backend.".into(),
            )
        })?;

        let mut vecs =
            embedder
                .embed(&[context.to_string()])
                .await
                .map_err(|error| {
                    RequestCorrection::document_query_embedding(Code::UnsupportedCombination,
                format!("The embedding backend could not prepare this document query: {error:#}"))
                })?;
        let message = match vecs.as_slice() {
            [] => Some("The embedding backend returned no vector for this document query."),
            [vector] if !preparation::usable_vector(vector) => {
                Some("The embedding backend returned an empty, nonfinite or all-zero query vector.")
            }
            [_] => None,
            _ => Some(
                "The embedding backend returned more than one vector for a single document query.",
            ),
        };
        if let Some(message) = message {
            return Err(RequestCorrection::document_query_embedding(
                Code::UnsupportedCombination,
                message.into(),
            )
            .into());
        }
        let query_vec = vecs.swap_remove(0);

        self.store
            .document_query_snapshot(&query_vec, project, limit)
            .await
    }

    // -----------------------------------------------------------------------
    // Evidence edges (Phase 4 C-core): documents grounding beliefs
    // -----------------------------------------------------------------------

    /// Attach a document chunk to a belief as grounding evidence (GROUNDS edge).
    /// Purely additive provenance — does not touch belief↔belief inference.
    pub async fn add_evidence(&self, belief_id: Uuid, chunk_id: Uuid, weight: f64) -> Result<()> {
        self.store
            .insert_evidence(chunk_id, belief_id, Probability::new(weight)?)
            .await
    }

    /// Remove a specific grounding edge.
    pub async fn delete_evidence(&self, belief_id: Uuid, chunk_id: Uuid) -> Result<()> {
        self.store.delete_evidence(chunk_id, belief_id).await
    }

    /// Complete the evidence change captured by this checked operation plan.
    pub async fn change_evidence_operation(
        &self,
        step: &store::RegisteredStep,
    ) -> Result<store::StepDecision> {
        self.store.change_evidence_operation(step).await
    }

    /// The grounding passages for a single belief, strongest first.
    /// Omit passage selection for all support; a supplied count is positive.
    pub async fn evidence_for_belief(
        &self,
        belief_id: Uuid,
        limit: Selection,
    ) -> Result<Vec<EvidenceRef>> {
        self.store
            .evidence_for_belief_snapshot(belief_id, limit)
            .await
    }

    /// `query_relevant`, enriched with the top-k grounding passages per belief.
    /// The same retrieval report accompanies the supporting passages.
    /// Omitted passage selection returns all supporting passages.
    pub async fn query_relevant_grounded(
        &self,
        query: &str,
        limit: Selection,
        evidence_per_belief: Selection,
        project: Option<&str>,
    ) -> Result<RetrievalReport<GroundedBelief>> {
        self.query_relevant_grounded_preferred(query, limit, evidence_per_belief, project, None)
            .await
    }

    /// Enrich the requested search without changing its memory preference.
    pub async fn query_relevant_grounded_preferred(
        &self,
        query: &str,
        limit: Selection,
        evidence_per_belief: Selection,
        project: Option<&str>,
        prefer_type: Option<MemoryType>,
    ) -> Result<RetrievalReport<GroundedBelief>> {
        self.grounded_after_overlay(
            query,
            limit,
            evidence_per_belief,
            project,
            prefer_type,
            || async { Ok(()) },
        )
        .await
    }

    pub(crate) async fn grounded_after_overlay<F, W>(
        &self,
        query: &str,
        limit: Selection,
        evidence_per_belief: Selection,
        project: Option<&str>,
        prefer_type: Option<MemoryType>,
        after_overlay: F,
    ) -> Result<RetrievalReport<GroundedBelief>>
    where
        F: FnOnce() -> W,
        W: std::future::Future<Output = Result<()>>,
    {
        let mut client = self.store.snapshot_connection().await;
        let tx = store::snapshot_transaction(&mut client).await?;
        let result = self
            .grounded_on(
                tx.client(),
                query,
                limit,
                evidence_per_belief,
                project,
                prefer_type,
                after_overlay,
            )
            .await?;
        tx.commit().await?;
        Ok(result)
    }

    async fn grounded_on<F, W>(
        &self,
        client: &tokio_postgres::Client,
        query: &str,
        limit: Selection,
        evidence_per_belief: Selection,
        project: Option<&str>,
        prefer_type: Option<MemoryType>,
        after_overlay: F,
    ) -> Result<RetrievalReport<GroundedBelief>>
    where
        F: FnOnce() -> W,
        W: std::future::Future<Output = Result<()>>,
    {
        let report = self
            .relevant_on(client, query, limit, project, prefer_type, after_overlay)
            .await?;
        let beliefs = report.beliefs;
        if beliefs.is_empty() {
            return Ok(RetrievalReport {
                beliefs: vec![],
                retrieval: report.retrieval,
            });
        }
        let ids: Vec<Uuid> = beliefs.iter().map(|b| b.id).collect();
        let ev = self.store.get_evidence_for_beliefs_on(client, &ids).await?;

        // Group (chunk_id, weight) by belief_id.
        let mut by_belief: std::collections::HashMap<Uuid, Vec<(Uuid, f64)>> =
            std::collections::HashMap::new();
        for (belief_id, chunk_id, weight) in ev {
            by_belief
                .entry(belief_id)
                .or_default()
                .push((chunk_id, weight));
        }

        // Cache chunk lookups so a chunk grounding several beliefs is fetched once.
        let mut chunk_cache: std::collections::HashMap<Uuid, Option<EvidenceRef>> =
            std::collections::HashMap::new();

        let mut out = Vec::with_capacity(beliefs.len());
        for belief in beliefs {
            let mut refs: Vec<EvidenceRef> = Vec::new();
            if let Some(entries) = by_belief.get(&belief.id) {
                let mut entries = entries.clone();
                // Strongest grounding first.
                entries.sort_by(|a, b| {
                    b.1.partial_cmp(&a.1)
                        .unwrap_or(std::cmp::Ordering::Equal)
                        .then_with(|| a.0.cmp(&b.0))
                });
                if let Some(count) = evidence_per_belief {
                    entries.truncate(count.get());
                }
                for (chunk_id, weight) in entries {
                    if let std::collections::hash_map::Entry::Vacant(e) =
                        chunk_cache.entry(chunk_id)
                    {
                        let r = self
                            .store
                            .get_chunk_by_id_on(client, chunk_id)
                            .await?
                            .map(|c| EvidenceRef {
                                chunk_id,
                                document_path: c.document_path,
                                section_path: c.section_path,
                                snippet: c.content.trim().to_string(),
                                weight,
                            });
                        e.insert(r);
                    }
                    if let Some(base) = chunk_cache.get(&chunk_id).and_then(|o| o.clone()) {
                        // Reuse the cached chunk metadata but keep this edge's weight.
                        refs.push(EvidenceRef { weight, ..base });
                    }
                }
            }
            let sources = self.store.belief_sources_on(client, belief.id).await?;
            out.push(GroundedBelief {
                belief,
                evidence: refs,
                sources,
            });
        }
        Ok(RetrievalReport {
            beliefs: out,
            retrieval: report.retrieval,
        })
    }

    /// Reserve operation metadata without executing a business handler.
    pub async fn reserve_operation(
        &self,
        request_key: &str,
    ) -> Result<store::OperationReservation> {
        self.store.reserve_operation(request_key).await
    }

    pub async fn read_operation_reservation(
        &self,
        token: Uuid,
    ) -> Result<Option<store::OperationReservation>> {
        self.store.read_operation_reservation(token).await
    }

    pub async fn bind_operation_request(
        &self,
        token: Uuid,
        request: &store::OperationBindingRequest,
    ) -> Result<store::OperationBindingDecision> {
        self.store.bind_operation_request(token, request).await
    }

    pub async fn read_operation_binding(
        &self,
        token: Uuid,
    ) -> Result<Option<store::OperationBinding>> {
        self.store.read_operation_binding(token).await
    }

    pub async fn commit_operation_step<F>(
        &self,
        step: &store::RegisteredStep,
        apply: F,
    ) -> Result<store::StepDecision>
    where
        F: for<'a, 'client> FnOnce(
            &'a tokio_postgres::Transaction<'client>,
            &'a store::OperationBindingRequest,
        ) -> store::StepWork<'a>,
    {
        self.store.commit_operation_step(step, apply).await
    }

    pub async fn commit_final_operation_step<F>(
        &self,
        step: &store::RegisteredStep,
        apply: F,
    ) -> Result<store::StepDecision>
    where
        F: for<'a, 'client> FnOnce(
            &'a tokio_postgres::Transaction<'client>,
            &'a store::OperationBindingRequest,
        ) -> store::FinalStepWork<'a>,
    {
        self.store.commit_final_operation_step(step, apply).await
    }

    pub async fn read_operation_step(
        &self,
        token: Uuid,
        step: &str,
    ) -> Result<Option<store::StepReceipt>> {
        self.store.read_operation_step(token, step).await
    }

    pub async fn prepare_operation<F>(
        &self,
        token: Uuid,
        expected: &store::OperationBindingRequest,
        select: F,
    ) -> Result<store::PlanDecision>
    where
        F: for<'a, 'client> FnOnce(
            &'a tokio_postgres::Transaction<'client>,
            &'a store::OperationBinding,
        ) -> store::SelectionWork<'a>,
    {
        self.store.prepare_operation(token, expected, select).await
    }

    /// Freeze the server's original source selection and semantic model
    /// identity. Retrying this token reads that plan without selecting again.
    pub async fn prepare_reembed_operation(&self, token: Uuid) -> Result<store::PlanDecision> {
        let request = match self.store.read_operation_binding(token).await? {
            Some(original) => original.request,
            None => store::OperationBindingRequest::new(
                "reembed".into(),
                serde_json::json!({}),
                self.embedding_operation_settings(),
            )?,
        };
        if request.operation() != "reembed" || request.arguments() != &serde_json::json!({}) {
            return Ok(store::PlanDecision::NeedsRecovery(
                "This token belongs to a different original request. Read its binding and saved outcome; do not select new work under it.".into()));
        }
        if let Err(cause) = preparation::validate_operation_settings(request.settings()) {
            return Ok(store::PlanDecision::NeedsRecovery(format!(
                "The original embedding settings cannot be used: {cause:#}. Read this token's original binding and saved outcome, and open a dialog with the user to resolve the settings. Do not select new work, replace its model, or invent a completion answer."
            )));
        }
        match self.store.bind_operation_request(token, &request).await? {
            store::OperationBindingDecision::Bound(_) => {
                self.store.prepare_reembed_plan(token, &request).await
            }
            store::OperationBindingDecision::ChangedRequest(original) => {
                Ok(store::PlanDecision::ChangedRequest(original))
            }
            store::OperationBindingDecision::UnknownToken => {
                Ok(store::PlanDecision::UnknownBinding)
            }
            store::OperationBindingDecision::Cancelled(receipt) => {
                Ok(store::PlanDecision::Cancelled(receipt))
            }
        }
    }

    pub fn complete_operation<'a>(
        &'a self,
        plan: &'a store::OperationPlan,
        reply: serde_json::Value,
    ) -> impl std::future::Future<Output = Result<store::CompletionDecision>> + Send + 'a {
        self.store.complete_operation(plan, reply)
    }

    pub async fn read_operation_outcome(
        &self,
        token: Uuid,
        expected: Option<&store::OperationBindingRequest>,
    ) -> Result<store::OperationOutcome> {
        self.store.read_operation_outcome(token, expected).await
    }

    /// Record the explicit decision and revoke publication. Public callers
    /// must separately stop and join owned work before reporting cleanup done.
    pub async fn record_operation_cancellation(
        &self,
        token: Uuid,
    ) -> Result<store::CancellationDecision> {
        self.store.record_operation_cancellation(token).await
    }

    pub async fn read_operation_cancellation(
        &self,
        token: Uuid,
    ) -> Result<Option<store::CancellationReceipt>> {
        self.store.read_operation_cancellation(token).await
    }

    /// Collect graph statistics.
    pub async fn stats(&self) -> Result<MimirStats> {
        self.store.stats_snapshot().await
    }
}

pub mod operations;
pub mod preparation;

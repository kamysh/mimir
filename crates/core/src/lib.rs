pub mod config;
pub mod db;
pub mod documents;
pub mod embed;
pub mod graph;
pub mod inference;
pub mod store;

use anyhow::Result;
use uuid::Uuid;

use config::Config;
use documents::{parse_markdown, QueryResult};
use embed::{make_backend, EmbeddingProvider};
use graph::{Belief, EdgeType, Pattern, Probability};
use inference::InferenceEngine;
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

/// Cosine similarity threshold for automatic GROUNDS edge creation.
/// A chunk and belief are auto-grounded when their embedding cosine similarity
/// meets or exceeds this value. Corresponds to `similarEnough` in Evidence.agda.
const GROUND_THRESHOLD: f64 = 0.80;

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
}

pub struct MimirService {
    store: AgeStore,
    inference: InferenceEngine,
    embeddings: Option<Box<dyn EmbeddingProvider>>,
}

impl MimirService {
    pub async fn connect(cfg: &Config) -> Result<Self> {
        db::migrate(&cfg.database).await?;
        let client = db::connect(&cfg.database).await?;
        let embeddings = cfg.embeddings.as_ref().map(make_backend);
        Ok(Self {
            store: AgeStore::new(client, cfg.database.dbname.clone())?,
            inference: InferenceEngine::new(),
            embeddings,
        })
    }

    /// Add a new belief. Returns the created Belief.
    pub async fn add_belief(
        &self,
        content: &str,
        probability: f64,
        confidence: f64,
    ) -> Result<Belief> {
        let belief = Belief::new(content.to_string(), probability, confidence)?;
        self.store.insert_belief(&belief).await?;
        if let Some(embedder) = &self.embeddings {
            let mut vecs = embedder
                .embed(std::slice::from_ref(&belief.content))
                .await?;
            if let Some(v) = vecs.pop() {
                self.store.insert_belief_embedding(belief.id, &v).await?;
                self.auto_ground_belief(&belief, &v).await?;
            }
        }
        Ok(belief)
    }

    /// Add a new belief scoped to a project.
    pub async fn add_belief_in_project(
        &self,
        content: &str,
        probability: f64,
        confidence: f64,
        project: &str,
    ) -> Result<Belief> {
        let belief = Belief::new_in_project(
            content.to_string(),
            probability,
            confidence,
            project.to_string(),
        )?;
        self.store.insert_belief(&belief).await?;
        if let Some(embedder) = &self.embeddings {
            let mut vecs = embedder
                .embed(std::slice::from_ref(&belief.content))
                .await?;
            if let Some(v) = vecs.pop() {
                self.store.insert_belief_embedding(belief.id, &v).await?;
                self.auto_ground_belief(&belief, &v).await?;
            }
        }
        Ok(belief)
    }

    /// Embed a belief's content and upsert the vector into `belief_embeddings`
    /// when an embedding backend is configured. No-op when `[embeddings]` is
    /// absent (the vector half of `query_relevant` simply degrades to empty).
    /// Called by `add_belief` / `add_belief_in_project` and by the `reembed`
    /// CLI to backfill existing beliefs.
    pub async fn embed_and_store_belief(&self, belief: &Belief) -> Result<()> {
        if let Some(embedder) = &self.embeddings {
            let mut vecs = embedder
                .embed(std::slice::from_ref(&belief.content))
                .await?;
            if let Some(v) = vecs.pop() {
                self.store.insert_belief_embedding(belief.id, &v).await?;
            }
        }
        Ok(())
    }

    /// Auto-ground a newly inserted belief against existing document chunks.
    /// Finds chunks with cosine similarity ≥ GROUND_THRESHOLD that are
    /// project-compatible (same project, or either side is unscoped), then
    /// creates GROUNDS edges. No-op when embeddings are not configured.
    /// Formalised as Evidence.autoGroundBelief in the Agda spec.
    async fn auto_ground_belief(&self, belief: &Belief, embedding: &[f32]) -> Result<()> {
        // Find project-scoped chunk IDs to restrict the search, then search
        // all global (unscoped) chunks too. We do a single scored search over
        // all chunks, then filter by project compatibility in Rust.
        let candidates = self
            .store
            .query_chunks_by_vector_scored(embedding, 20, None)
            .await?;
        for (chunk_id, sim) in candidates {
            if sim < GROUND_THRESHOLD {
                break; // results are ordered by similarity desc
            }
            // Check project compatibility: fetch the chunk's project tag.
            if let Some(chunk) = self.store.get_chunk_by_id(chunk_id).await? {
                let compatible = match (&belief.project, &chunk.project) {
                    (None, _) | (_, None) => true,
                    (Some(bp), Some(cp)) => bp == cp,
                };
                if compatible {
                    self.store
                        .insert_evidence(chunk_id, belief.id, Probability::new(sim)?)
                        .await?;
                }
            }
        }
        Ok(())
    }

    /// Auto-ground newly loaded chunks against existing beliefs.
    /// For each chunk, finds beliefs with cosine similarity ≥ GROUND_THRESHOLD
    /// that are project-compatible, then creates GROUNDS edges.
    /// No-op when embeddings are not configured.
    /// Formalised as Evidence.autoGroundChunks in the Agda spec.
    async fn auto_ground_chunks(
        &self,
        chunks: &[documents::DocumentChunk],
        embeddings: &[Vec<f32>],
    ) -> Result<()> {
        for (chunk, embedding) in chunks.iter().zip(embeddings.iter()) {
            let candidates = self
                .store
                .query_beliefs_by_vector_scored(embedding, 20)
                .await?;
            for (belief_id, sim) in candidates {
                if sim < GROUND_THRESHOLD {
                    break;
                }
                // Fetch belief to check project compatibility.
                if let Some(belief) = self.store.get_belief(belief_id).await? {
                    let compatible = match (&chunk.project, &belief.project) {
                        (None, _) | (_, None) => true,
                        (Some(cp), Some(bp)) => cp == bp,
                    };
                    if compatible {
                        self.store
                            .insert_evidence(chunk.id, belief_id, Probability::new(sim)?)
                            .await?;
                    }
                }
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

    /// Delete all beliefs and DocumentChunks tagged with the given project.
    /// Returns the combined count of vertices removed.
    pub async fn delete_project(&self, project: &str) -> Result<usize> {
        let belief_count = self.store.delete_project(project).await?;
        // Also clear document chunks tagged with this project.
        let chunk_ids = self.store.get_chunk_ids_by_project(project).await?;
        let chunk_count = chunk_ids.len();
        self.store.delete_document_chunks(&chunk_ids).await?;
        self.store.delete_chunk_embeddings(&chunk_ids).await?;
        Ok(belief_count + chunk_count)
    }

    /// Get a pattern by ID.
    pub async fn get_pattern(&self, id: Uuid) -> Result<Option<Pattern>> {
        self.store.get_pattern(id).await
    }

    /// Delete a pattern and all its edges by ID. Returns true if found.
    pub async fn delete_pattern(&self, id: Uuid) -> Result<bool> {
        self.store.delete_pattern(id).await
    }

    /// Add a new pattern.
    pub async fn add_pattern(
        &self,
        situation: &str,
        approach: &str,
        success_rate: f64,
    ) -> Result<Pattern> {
        let pattern = Pattern::new(situation.to_string(), approach.to_string(), success_rate)?;
        self.store.insert_pattern(&pattern).await?;
        Ok(pattern)
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
                self.propagate_from(from_id).await?;
            }
        }
        Ok(())
    }

    /// Get a belief by ID.
    pub async fn get_belief(&self, id: Uuid) -> Result<Option<Belief>> {
        self.store.get_belief(id).await
    }

    /// List all beliefs.
    pub async fn list_beliefs(&self) -> Result<Vec<Belief>> {
        self.store.list_beliefs().await
    }

    /// List all patterns.
    pub async fn list_patterns(&self) -> Result<Vec<Pattern>> {
        self.store.list_patterns().await
    }

    /// Run defeat propagation from a seed belief ID.
    /// Loads the downstream subgraph and all edges among it, applies attenuate/boost,
    /// and writes updated probabilities back to the store.
    pub async fn propagate_from(&self, seed_id: Uuid) -> Result<Vec<(Uuid, Probability)>> {
        let seed = match self.store.get_belief(seed_id).await? {
            Some(b) => b,
            None => anyhow::bail!("belief {} not found", seed_id),
        };
        let downstream = self.store.get_downstream_beliefs(seed_id).await?;

        // Collect all IDs in the subgraph (seed + downstream)
        let mut ids: Vec<Uuid> = downstream.iter().map(|b| b.id).collect();
        ids.push(seed_id);

        // Load the COMPLETE incoming-edge set of every downstream node (spec:
        // Mimir.Beta evidence completeness) — sources may lie OUTSIDE the
        // subgraph; get_incoming_edges returns each edge WITH its source's stored
        // mean, so out-of-subgraph parents count with no per-source follow-up
        // query.
        let incoming = self.store.get_incoming_edges(&ids).await?;
        let edges = strip_source_means(&incoming);
        let external_means = external_means_from(&incoming, &ids);

        let updates =
            self.inference
                .propagate_defeat(&seed, &downstream, &edges, &external_means)?;
        // Persist the durable Beta posterior ATOMICALLY (all-or-nothing, so a
        // propagation never leaves the subgraph half-updated); probability/
        // confidence are refreshed from (α,β) by update_beliefs_beta.
        let writes: Vec<(Uuid, f64, f64)> =
            updates.iter().map(|&(id, (a, b))| (id, a, b)).collect();
        self.store.update_beliefs_beta(&writes).await?;
        let mut out = Vec::with_capacity(updates.len());
        for (id, (alpha, beta)) in updates {
            out.push((id, Probability::new(graph::beta_mean(alpha, beta))?));
        }
        Ok(out)
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
        let value = Probability::new(value)?;
        if self.store.get_belief(target_id).await?.is_none() {
            anyhow::bail!("belief {} not found", target_id);
        }
        let downstream = self.store.get_causal_downstream_beliefs(target_id).await?;
        let mut ids: Vec<Uuid> = downstream.iter().map(|b| b.id).collect();
        ids.push(target_id);
        // Complete incoming edges of every descendant, with source means — so a
        // genuine CO-CAUSE outside the descendant set still counts (spec
        // Mimir.Inference keep-causes-into-nontarget). Surgery (in `intervene`)
        // then cuts only edges INTO the target.
        let incoming = self.store.get_incoming_edges(&ids).await?;
        let edges = strip_source_means(&incoming);
        let external_means = external_means_from(&incoming, &ids);
        // No writeback — this is a hypothetical projection.
        self.inference
            .intervene(target_id, value, &downstream, &edges, &external_means)
    }

    /// Get active contradictions in the graph.
    pub async fn get_contradictions(&self) -> Result<Vec<(Uuid, Uuid)>> {
        let pairs = self.store.get_contradiction_pairs().await?;
        if pairs.is_empty() {
            return Ok(vec![]);
        }

        let beliefs = self.store.list_beliefs().await?;
        let belief_map: std::collections::HashMap<Uuid, &Belief> =
            beliefs.iter().map(|b| (b.id, b)).collect();

        Ok(self
            .inference
            .detect_active_contradictions(&belief_map, &pairs))
    }

    /// Apply time decay to all beliefs, write updates.
    /// decay_factor defaults to 0.99 (~1% per day) if not provided.
    /// Grounded beliefs resist decay in proportion to their total grounding mass
    /// (spec Mimir.Beta CCoupling.coupling-increases-strength).
    pub async fn decay_beliefs(&self, decay_factor: Option<f64>) -> Result<usize> {
        let factor = decay_factor.unwrap_or(0.99);
        let beliefs = self.store.get_all_beliefs_for_decay().await?;
        let grounding_masses = self.store.get_grounding_mass_all().await?;
        let now = chrono::Utc::now();
        let updates = self
            .inference
            .decay_all(&beliefs, now, factor, &grounding_masses)?;
        let count = updates.len();
        // Persist decayed Beta state (spec: betaDecay toward (1,1)) ATOMICALLY,
        // so a failed sweep cannot leave some beliefs decayed and others not
        // (decay is not idempotent in elapsed time — a half-sweep would
        // double-decay the committed prefix on the next run).
        let writes: Vec<(Uuid, f64, f64)> =
            updates.into_iter().map(|(id, (a, b))| (id, a, b)).collect();
        self.store.update_beliefs_beta(&writes).await?;
        Ok(count)
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
    /// (query_relevant section). `limit = 0` means no limit.
    pub async fn query_relevant(&self, query: &str, limit: usize) -> Result<Vec<Belief>> {
        let all = self.store.list_beliefs().await?;
        if all.is_empty() {
            return Ok(vec![]);
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
                b.0.cmp(&a.0).then_with(|| {
                    b.1.probability
                        .value()
                        .partial_cmp(&a.1.probability.value())
                        .unwrap_or(std::cmp::Ordering::Equal)
                })
            });
            scored.into_iter().map(|(_, b)| b.id).collect()
        };

        // ── Vector list: cosine top-k over belief_embeddings, when an
        //    embedding backend is configured. The pool is intentionally larger
        //    than `limit`; RRF + the probability sort + truncate decide the
        //    final cut. If the embedder itself fails (model unavailable,
        //    network error, etc.) we degrade to token-only with a warning
        //    rather than failing the whole query — partial recall beats none.
        let vector_ranked: Vec<Uuid> = if let Some(embedder) = &self.embeddings {
            let pool_size = if limit > 0 { (limit * 4).max(20) } else { 50 };
            match embedder.embed(&[query.to_string()]).await {
                Ok(mut vecs) => match vecs.pop() {
                    Some(qv) => self.store.query_beliefs_by_vector(&qv, pool_size).await?,
                    None => Vec::new(),
                },
                Err(e) => {
                    tracing::warn!(
                        error = %e,
                        "embedder failed for query — falling back to token-only retrieval. \
                         Verify [embeddings] config and that the model is reachable."
                    );
                    Vec::new()
                }
            }
        } else {
            Vec::new()
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
            return Ok(vec![]);
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
            let downstream = self.store.get_downstream_beliefs(id).await?;
            for b in downstream {
                if !matched.iter().any(|m| m.id == b.id) {
                    matched.push(b);
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
        });
        let fused = weighted_rrf(&[
            (vector_ranked.as_slice(), W_VECTOR),
            (token_ranked.as_slice(), W_TOKEN),
            (prior_ranked.as_slice(), W_PRIOR),
        ]);
        matched.sort_by(|a, b| {
            let sa = fused.get(&a.id).copied().unwrap_or(0.0);
            let sb = fused.get(&b.id).copied().unwrap_or(0.0);
            sb.partial_cmp(&sa).unwrap_or(std::cmp::Ordering::Equal)
        });

        if limit > 0 {
            matched.truncate(limit);
        }
        Ok(matched)
    }

    // -----------------------------------------------------------------------
    // Document RAG
    // -----------------------------------------------------------------------

    /// Parse a markdown file into chunks, embed each one, and store in AGE +
    /// chunk_embeddings.  Replaces any existing chunks for the same path.
    /// Returns the number of chunks loaded.
    pub async fn load_document(&self, path: &str, project: Option<&str>) -> Result<usize> {
        let embedder = self.embeddings.as_ref().ok_or_else(|| {
            anyhow::anyhow!("embeddings not configured — add [embeddings] to config.toml")
        })?;

        let text = std::fs::read_to_string(path)
            .map_err(|e| anyhow::anyhow!("cannot read {}: {}", path, e))?;

        // Replace-on-reload: clear existing chunks for this path first.
        let old_ids = self.store.get_chunk_ids_for_document(path).await?;
        self.store.delete_document_chunks(&old_ids).await?;
        self.store.delete_chunk_embeddings(&old_ids).await?;

        let chunks = parse_markdown(&text, path, project);
        let count = chunks.len();

        // Embed all chunks in one batch call where possible.
        let texts: Vec<String> = chunks.iter().map(|c| c.content.clone()).collect();
        let embeddings = embedder.embed(&texts).await?;

        for (chunk, embedding) in chunks.iter().zip(embeddings.iter()) {
            self.store.insert_document_chunk(chunk).await?;
            self.store
                .insert_chunk_embedding(chunk.id, embedding)
                .await?;
        }

        // Auto-ground: create GROUNDS edges to similar beliefs (Evidence.autoGroundChunks).
        self.auto_ground_chunks(&chunks, &embeddings).await?;

        Ok(count)
    }

    /// Remove all chunks (and their embeddings) for the given document path.
    /// Returns the number of chunks cleared. Returns 0 if never loaded.
    pub async fn clear_document(&self, path: &str) -> Result<usize> {
        let ids = self.store.get_chunk_ids_for_document(path).await?;
        let count = ids.len();
        self.store.delete_document_chunks(&ids).await?;
        self.store.delete_chunk_embeddings(&ids).await?;
        Ok(count)
    }

    /// Semantic search over loaded document chunks.
    /// Embeds `context`, queries chunk_embeddings by cosine distance, fetches
    /// matching DocumentChunk vertices from AGE, enriches with parent content.
    /// limit=0 means no limit.
    pub async fn query_document(
        &self,
        context: &str,
        project: Option<&str>,
        limit: usize,
    ) -> Result<Vec<QueryResult>> {
        let embedder = self.embeddings.as_ref().ok_or_else(|| {
            anyhow::anyhow!("embeddings not configured — add [embeddings] to config.toml")
        })?;

        let mut vecs = embedder.embed(&[context.to_string()]).await?;
        let query_vec = if vecs.is_empty() {
            anyhow::bail!("empty embedding response");
        } else {
            vecs.swap_remove(0)
        };

        let filter_ids: Option<Vec<Uuid>> = match project {
            None => None,
            Some(proj) => Some(self.store.get_chunk_ids_by_project(proj).await?),
        };

        let chunk_ids = self
            .store
            .query_chunks_by_vector(&query_vec, limit, filter_ids.as_deref())
            .await?;

        let mut results = Vec::with_capacity(chunk_ids.len());
        for id in chunk_ids {
            let Some(chunk) = self.store.get_chunk_by_id(id).await? else {
                continue;
            };
            let parent_content = match chunk.parent_id {
                None => None,
                Some(pid) => self.store.get_chunk_by_id(pid).await?.map(|p| p.content),
            };
            results.push(QueryResult {
                id: chunk.id.to_string(),
                document_path: chunk.document_path,
                section_path: chunk.section_path,
                content: chunk.content,
                parent_content,
            });
        }
        Ok(results)
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

    /// The grounding passages for a single belief, strongest first.
    /// `limit = 0` means no cap.
    pub async fn evidence_for_belief(
        &self,
        belief_id: Uuid,
        limit: usize,
    ) -> Result<Vec<EvidenceRef>> {
        let mut ev = self.store.get_evidence_for_beliefs(&[belief_id]).await?;
        ev.sort_by(|a, b| b.2.partial_cmp(&a.2).unwrap_or(std::cmp::Ordering::Equal));
        if limit > 0 {
            ev.truncate(limit);
        }
        let mut out = Vec::with_capacity(ev.len());
        for (_belief, chunk_id, weight) in ev {
            if let Some(c) = self.store.get_chunk_by_id(chunk_id).await? {
                out.push(EvidenceRef {
                    chunk_id,
                    document_path: c.document_path,
                    section_path: c.section_path,
                    snippet: c.content.trim().to_string(),
                    weight,
                });
            }
        }
        Ok(out)
    }

    /// `query_relevant`, enriched with the top-k grounding passages per belief.
    /// `query_relevant` itself is unchanged (backward compatible); this is purely
    /// additive. `evidence_per_belief = 0` means no cap.
    pub async fn query_relevant_grounded(
        &self,
        query: &str,
        limit: usize,
        evidence_per_belief: usize,
    ) -> Result<Vec<GroundedBelief>> {
        let beliefs = self.query_relevant(query, limit).await?;
        if beliefs.is_empty() {
            return Ok(vec![]);
        }
        let ids: Vec<Uuid> = beliefs.iter().map(|b| b.id).collect();
        let ev = self.store.get_evidence_for_beliefs(&ids).await?;

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
                entries.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
                if evidence_per_belief > 0 {
                    entries.truncate(evidence_per_belief);
                }
                for (chunk_id, weight) in entries {
                    if let std::collections::hash_map::Entry::Vacant(e) =
                        chunk_cache.entry(chunk_id)
                    {
                        let r = self
                            .store
                            .get_chunk_by_id(chunk_id)
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
            out.push(GroundedBelief {
                belief,
                evidence: refs,
            });
        }
        Ok(out)
    }

    /// Collect graph statistics.
    pub async fn stats(&self) -> Result<MimirStats> {
        let beliefs = self.store.count_beliefs().await?;
        let patterns = self.store.count_patterns().await?;
        let (supports, defeats, causes, contradicts) = self.store.count_edges().await?;
        Ok(MimirStats {
            beliefs,
            patterns,
            supports,
            defeats,
            causes,
            contradicts,
        })
    }
}

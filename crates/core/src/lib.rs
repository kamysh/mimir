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
use documents::{QueryResult, parse_markdown};
use embed::{EmbeddingProvider, make_backend};
use graph::{Belief, EdgeType, Pattern, Probability};
use inference::InferenceEngine;
use store::AgeStore;

/// Reciprocal Rank Fusion merge of multiple ranked Uuid lists.
/// Each list contributes `1 / (K + rank)` (rank is 0-based) to each contained
/// id's score; ids are deduplicated and returned sorted by total score
/// descending. K = 60 is the standard RRF constant. Used by `query_relevant`
/// to combine the token-overlap and vector-cosine rankings into one relevance
/// ranking before graph expansion and the probability-desc sort.
fn rrf_merge_ids(lists: &[Vec<Uuid>]) -> Vec<Uuid> {
    use std::collections::HashMap;
    const K: f32 = 60.0;
    let mut scores: HashMap<Uuid, f32> = HashMap::new();
    for list in lists {
        for (rank, id) in list.iter().enumerate() {
            let rrf = 1.0 / (K + rank as f32);
            *scores.entry(*id).or_insert(0.0) += rrf;
        }
    }
    let mut ranked: Vec<(Uuid, f32)> = scores.into_iter().collect();
    ranked.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
    ranked.into_iter().map(|(id, _)| id).collect()
}

pub struct MimirStats {
    pub beliefs:    usize,
    pub patterns:   usize,
    pub supports:   usize,
    pub defeats:    usize,
    pub causes:     usize,
    /// Raw directed-edge count.  CONTRADICTS is stored bidirectionally,
    /// so logical pairs = contradicts / 2.
    pub contradicts: usize,
}

pub struct MimirService {
    store: AgeStore,
    inference: InferenceEngine,
    embeddings: Option<Box<dyn EmbeddingProvider>>,
}

impl MimirService {
    pub async fn connect(cfg: &Config) -> Result<Self> {
        let pool = db::connect(&cfg.database).await?;
        sqlx::migrate!().run(&pool).await?;
        let embeddings = cfg.embeddings.as_ref().map(make_backend);
        Ok(Self {
            store: AgeStore::new(pool, cfg.database.dbname.clone()),
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
        self.embed_and_store_belief(&belief).await?;
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
        self.embed_and_store_belief(&belief).await?;
        Ok(belief)
    }

    /// Embed a belief's content and upsert the vector into `belief_embeddings`
    /// when an embedding backend is configured. No-op when `[embeddings]` is
    /// absent (the vector half of `query_relevant` simply degrades to empty).
    /// Called by `add_belief` / `add_belief_in_project` and by the `reembed`
    /// CLI to backfill existing beliefs.
    pub async fn embed_and_store_belief(&self, belief: &Belief) -> Result<()> {
        if let Some(embedder) = &self.embeddings {
            let mut vecs = embedder.embed(&[belief.content.clone()]).await?;
            if let Some(v) = vecs.pop() {
                self.store.insert_belief_embedding(belief.id, &v).await?;
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

        // Load edges among the subgraph
        let edges = self.store.get_edges_among(&ids).await?;

        let updates = self.inference.propagate_defeat(&seed, &downstream, &edges)?;
        for (id, prob) in &updates {
            self.store.update_belief_probability(*id, *prob).await?;
        }
        Ok(updates)
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
    pub async fn decay_beliefs(&self, decay_factor: Option<f64>) -> Result<usize> {
        let factor = decay_factor.unwrap_or(0.99);
        let beliefs = self.store.get_all_beliefs_for_decay().await?;
        let now = chrono::Utc::now();
        let updates = self.inference.decay_all(&beliefs, now, factor)?;
        let count = updates.len();
        for (id, conf) in updates {
            self.store.update_belief_confidence(id, conf).await?;
        }
        Ok(count)
    }

    /// Hybrid retrieval. Selection is the RRF-merged union of (a) token/keyword
    /// matches (beliefs whose lowercased content contains at least one
    /// whitespace-split query term, ranked by distinct-term match count) and
    /// (b) vector cosine top-k over `belief_embeddings` (when an embedding
    /// backend is configured; empty otherwise). The seed set is then expanded
    /// along SUPPORTS/CAUSES edges and sorted by probability descending. The
    /// output order is probability-desc; the RRF score governs only which
    /// beliefs seed the result. Spec: `Mimir.Graph` (query_relevant section).
    /// `limit = 0` means no limit.
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

        // ── RRF merge → relevance-ranked, deduplicated seed IDs.
        let seed_ids = rrf_merge_ids(&[token_ranked, vector_ranked]);
        if seed_ids.is_empty() {
            return Ok(vec![]);
        }

        // ── Materialise beliefs in seed order from the already-loaded list.
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

        // ── Sort by probability descending and truncate (unchanged invariants;
        //    see Mimir.Graph proofs).
        matched.sort_by(|a, b| {
            b.probability
                .value()
                .partial_cmp(&a.probability.value())
                .unwrap_or(std::cmp::Ordering::Equal)
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
    pub async fn load_document(
        &self,
        path: &str,
        project: Option<&str>,
    ) -> Result<usize> {
        let embedder = self
            .embeddings
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("embeddings not configured — add [embeddings] to config.toml"))?;

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
            self.store.insert_chunk_embedding(chunk.id, embedding).await?;
        }
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
        let embedder = self
            .embeddings
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("embeddings not configured — add [embeddings] to config.toml"))?;

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
            .query_chunks_by_vector(
                &query_vec,
                limit,
                filter_ids.as_deref(),
            )
            .await?;

        let mut results = Vec::with_capacity(chunk_ids.len());
        for id in chunk_ids {
            let Some(chunk) = self.store.get_chunk_by_id(id).await? else {
                continue;
            };
            let parent_content = match chunk.parent_id {
                None => None,
                Some(pid) => self
                    .store
                    .get_chunk_by_id(pid)
                    .await?
                    .map(|p| p.content),
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

    /// Collect graph statistics.
    pub async fn stats(&self) -> Result<MimirStats> {
        let beliefs  = self.store.count_beliefs().await?;
        let patterns = self.store.count_patterns().await?;
        let (supports, defeats, causes, contradicts) = self.store.count_edges().await?;
        Ok(MimirStats { beliefs, patterns, supports, defeats, causes, contradicts })
    }

    /// Update the confidence value of a belief.
    pub async fn update_confidence(&self, id: Uuid, confidence: f64) -> Result<()> {
        let c = Probability::new(confidence)?;
        self.store.update_belief_confidence(id, c).await
    }
}

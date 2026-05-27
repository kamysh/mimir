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
        Ok(belief)
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

    /// Hybrid retrieval: returns beliefs matching the query by content (case-insensitive),
    /// plus beliefs reachable from matched beliefs via SUPPORTS/CAUSES edges.
    /// Results are deduplicated and sorted by probability descending.
    /// limit=0 means no limit.
    pub async fn query_relevant(&self, query: &str, limit: usize) -> Result<Vec<Belief>> {
        let all = self.store.list_beliefs().await?;
        let q = query.to_lowercase();

        // Direct text matches
        let mut matched: Vec<Belief> = all
            .iter()
            .filter(|b| b.content.to_lowercase().contains(&q))
            .cloned()
            .collect();

        // Expand via graph: add beliefs reachable from matched ones
        let matched_ids: Vec<Uuid> = matched.iter().map(|b| b.id).collect();
        for id in matched_ids {
            let downstream = self.store.get_downstream_beliefs(id).await?;
            for b in downstream {
                if !matched.iter().any(|m| m.id == b.id) {
                    matched.push(b);
                }
            }
        }

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

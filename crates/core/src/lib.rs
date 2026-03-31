pub mod db;
pub mod graph;
pub mod inference;
pub mod store;

use anyhow::Result;
use uuid::Uuid;

use graph::{Belief, EdgeType, Pattern, Probability};
use inference::InferenceEngine;
use store::AgeStore;

pub struct AiMemService {
    store: AgeStore,
    inference: InferenceEngine,
}

impl AiMemService {
    pub async fn connect(dsn: &str) -> Result<Self> {
        let pool = db::connect(dsn).await?;
        Ok(Self {
            store: AgeStore::new(pool),
            inference: InferenceEngine::new(),
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

    /// Add a new pattern.
    pub async fn add_pattern(
        &self,
        situation: &str,
        approach: &str,
        success_rate: f64,
    ) -> Result<Pattern> {
        let mut pattern = Pattern::new(situation.to_string(), approach.to_string())?;
        pattern.success_rate = Probability::new(success_rate)?;
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

    /// Detect active contradictions in the graph.
    pub async fn detect_contradictions(&self) -> Result<Vec<(Uuid, Uuid)>> {
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
    pub async fn decay_beliefs(&self) -> Result<usize> {
        let beliefs = self.store.get_all_beliefs_for_decay().await?;
        let now = chrono::Utc::now();
        let updates = self.inference.decay_all(&beliefs, now)?;
        let count = updates.len();
        for (id, prob) in updates {
            self.store.update_belief_probability(id, prob).await?;
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

    /// Update the confidence value of a belief.
    pub async fn update_confidence(&self, id: Uuid, confidence: f64) -> Result<()> {
        let c = Probability::new(confidence)?;
        self.store.update_belief_confidence(id, c).await
    }
}

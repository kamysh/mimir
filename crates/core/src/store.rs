use anyhow::{bail, Result};
use chrono::DateTime;
use sqlx::{PgPool, Row};
use std::collections::HashMap;
use uuid::Uuid;

use crate::documents::DocumentChunk;
use crate::embed::vec_literal;
use crate::graph::{Belief, Edge, EdgeType, Pattern, Probability};

// ---------------------------------------------------------------------------
// Helper: escape single-quoted strings for AGE Cypher interpolation
// ---------------------------------------------------------------------------

fn esc(s: &str) -> String {
    // Inside AGE dollar-quoted Cypher strings, openCypher uses backslash escaping.
    // Escape backslashes first, then single quotes.
    s.replace('\\', "\\\\").replace('\'', "\\'")
}

/// Guard: Beta counts (and the scalars derived from them) are interpolated into
/// Cypher as bare numeric literals, so a non-finite f64 would render as `inf`/
/// `NaN` — invalid Cypher that fails the query opaquely. The spec models α,β as
/// rationals (always finite); enforce that here before any write.
fn ensure_finite(label: &str, values: &[(&str, f64)]) -> Result<()> {
    for &(field, v) in values {
        if !v.is_finite() {
            bail!("{label}: {field} must be finite, got {v}");
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// AGE column-based row decoding
//
// Instead of returning whole vertex/edge agtype objects (which can't be cast
// to TEXT), we return individual scalar properties. Scalar agtype values
// (strings, numbers) *can* be cast to TEXT via `::text` in the AS-clause.
// ---------------------------------------------------------------------------

/// Decode a `Belief` from a sqlx row that has columns:
///   id TEXT, content TEXT, probability TEXT, confidence TEXT,
///   created_at TEXT, last_activated_at TEXT
fn belief_from_row(row: &sqlx::postgres::PgRow) -> Result<Belief> {
    let id_str: String = row.try_get("id")?;
    let content: String = row.try_get("content")?;
    let probability_str: String = row.try_get("probability")?;
    let confidence_str: String = row.try_get("confidence")?;
    let created_at_str: String = row.try_get("created_at")?;
    let last_activated_str: String = row.try_get("last_activated_at")?;
    // project is optional — existing beliefs without it return SQL NULL
    let project: Option<String> = row.try_get("project").unwrap_or(None);

    let id = Uuid::parse_str(&id_str)?;
    let probability: f64 = probability_str.parse()?;
    let confidence: f64 = confidence_str.parse()?;
    let created_at = DateTime::parse_from_rfc3339(&created_at_str)?.with_timezone(&chrono::Utc);
    let last_activated_at =
        DateTime::parse_from_rfc3339(&last_activated_str)?.with_timezone(&chrono::Utc);

    // Beta state: read α/β/α₀/β₀ if present (post-migration 005), else derive
    // them from the stored (probability, confidence) via the prior mapping.
    // prior_from is exact, so a pre-migration row loads with mean == probability.
    let alpha: Option<f64> = row
        .try_get::<String, _>("alpha")
        .ok()
        .and_then(|s| s.parse().ok());
    let beta: Option<f64> = row
        .try_get::<String, _>("beta")
        .ok()
        .and_then(|s| s.parse().ok());
    let alpha0: Option<f64> = row
        .try_get::<String, _>("alpha0")
        .ok()
        .and_then(|s| s.parse().ok());
    let beta0: Option<f64> = row
        .try_get::<String, _>("beta0")
        .ok()
        .and_then(|s| s.parse().ok());

    let (derived_a0, derived_b0) = crate::graph::prior_from(probability, confidence);
    let alpha0 = alpha0.unwrap_or(derived_a0);
    let beta0 = beta0.unwrap_or(derived_b0);
    let alpha = alpha.unwrap_or(alpha0);
    let beta = beta.unwrap_or(beta0);

    Belief::from_stored(
        id,
        content,
        alpha,
        beta,
        alpha0,
        beta0,
        created_at,
        last_activated_at,
        project,
    )
}

/// Decode a `Pattern` from a sqlx row with columns:
///   id TEXT, situation TEXT, approach TEXT, activation_count TEXT,
///   success_rate TEXT, created_at TEXT
fn pattern_from_row(row: &sqlx::postgres::PgRow) -> Result<Pattern> {
    let id_str: String = row.try_get("id")?;
    let situation: String = row.try_get("situation")?;
    let approach: String = row.try_get("approach")?;
    let activation_count_str: String = row.try_get("activation_count")?;
    let success_rate_str: String = row.try_get("success_rate")?;
    let created_at_str: String = row.try_get("created_at")?;

    let id = Uuid::parse_str(&id_str)?;
    let activation_count: u32 = activation_count_str.parse()?;
    let success_rate: f64 = success_rate_str.parse()?;
    let created_at = DateTime::parse_from_rfc3339(&created_at_str)?.with_timezone(&chrono::Utc);

    Ok(Pattern {
        id,
        situation,
        approach,
        activation_count,
        success_rate: Probability::new(success_rate)?,
        created_at,
    })
}

/// Decode a `DocumentChunk` from a sqlx row with columns:
///   id TEXT, document_path TEXT, section_path TEXT (agtype list as JSON),
///   content TEXT, parent_id TEXT, project TEXT
fn chunk_from_row(row: &sqlx::postgres::PgRow) -> Result<DocumentChunk> {
    let id_str: String = row.try_get("id")?;
    let document_path: String = row.try_get("document_path")?;
    let section_path_str: String = row.try_get("section_path")?;
    let content: String = row.try_get("content")?;
    let parent_id_str: Option<String> = row.try_get("parent_id").unwrap_or(None);
    let project: Option<String> = row.try_get("project").unwrap_or(None);

    let id = Uuid::parse_str(&id_str)?;
    // AGE lists cast to text as JSON arrays: ["H1","H2"] or []
    let section_path: Vec<String> = serde_json::from_str(&section_path_str).unwrap_or_default();
    let parent_id = parent_id_str
        .as_deref()
        .and_then(|s| Uuid::parse_str(s).ok());

    Ok(DocumentChunk {
        id,
        document_path,
        section_path,
        content,
        parent_id,
        project,
    })
}

// ---------------------------------------------------------------------------
// AGE query helpers
// ---------------------------------------------------------------------------

/// Evidence-mass constant k for C-coupling (spec Mimir.Beta CCoupling).
/// Each GROUNDS edge of weight w contributes α += k·w as a pseudo-observation.
const EVIDENCE_MASS_K: f64 = 1.0;

/// SQL fragment for returning all Belief scalar properties cast to TEXT.
const BELIEF_RETURN_COLUMNS: &str = r#"AS (
  id             text,
  content        text,
  probability    text,
  confidence     text,
  alpha          text,
  beta           text,
  alpha0         text,
  beta0          text,
  created_at     text,
  last_activated_at text,
  project        text
)"#;

/// SQL fragment for returning all Pattern scalar properties cast to TEXT.
const PATTERN_RETURN_COLUMNS: &str = r#"AS (
  id               text,
  situation        text,
  approach         text,
  activation_count text,
  success_rate     text,
  created_at       text
)"#;

/// SQL fragment for returning all DocumentChunk scalar properties cast to TEXT.
const CHUNK_RETURN_COLUMNS: &str = r#"AS (
  id            text,
  document_path text,
  section_path  text,
  content       text,
  parent_id     text,
  project       text
)"#;

// ---------------------------------------------------------------------------
// AgeStore
// ---------------------------------------------------------------------------

pub struct AgeStore {
    pool: PgPool,
    /// AGE graph name — equals the PostgreSQL database name from config.
    graph_name: String,
}

impl AgeStore {
    pub fn new(pool: PgPool, graph_name: String) -> Self {
        Self { pool, graph_name }
    }

    // -----------------------------------------------------------------------
    // Beliefs
    // -----------------------------------------------------------------------

    pub async fn insert_belief(&self, belief: &Belief) -> Result<()> {
        let g = &self.graph_name;
        let id = belief.id.to_string();
        let content = esc(&belief.content);
        let probability = belief.probability.value();
        let confidence = belief.confidence.value();
        // Durable Beta state (spec: Mimir.Beta StoredBelief / store-load-round-trip).
        let alpha = belief.alpha;
        let beta = belief.beta;
        let alpha0 = belief.alpha0;
        let beta0 = belief.beta0;
        ensure_finite(
            "insert_belief",
            &[
                ("alpha", alpha),
                ("beta", beta),
                ("alpha0", alpha0),
                ("beta0", beta0),
            ],
        )?;
        let created_at = esc(&belief.created_at.to_rfc3339());
        let last_activated_at = esc(&belief.last_activated_at.to_rfc3339());
        let project_prop = match &belief.project {
            Some(p) => format!(", project: '{}'", esc(p)),
            None => String::new(),
        };

        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  CREATE (n:Belief {{
    id: '{id}',
    content: '{content}',
    probability: {probability},
    confidence: {confidence},
    alpha: {alpha},
    beta: {beta},
    alpha0: {alpha0},
    beta0: {beta0},
    created_at: '{created_at}',
    last_activated_at: '{last_activated_at}'{project_prop}
  }})
  RETURN n.id
$$) AS (id ag_catalog.agtype)"#
        );

        sqlx::query(&sql).execute(&self.pool).await?;
        Ok(())
    }

    /// Delete a belief and all its edges by ID. Returns true if found and deleted.
    pub async fn delete_belief(&self, id: Uuid) -> Result<bool> {
        let g = &self.graph_name;
        let id_str = id.to_string();
        // First check existence to give a meaningful return value.
        // AGE does not support RETURN after DETACH DELETE reliably.
        let exists = self.get_belief(id).await?.is_some();
        if !exists {
            return Ok(false);
        }
        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{id: '{id_str}'}})
  DETACH DELETE n
  RETURN 1
$$) AS (ok ag_catalog.agtype)"#
        );
        sqlx::query(&sql).fetch_all(&self.pool).await?;
        self.delete_belief_embeddings(&[id]).await?;
        Ok(true)
    }

    /// Delete all beliefs (and their edges) tagged with the given project.
    /// Returns the number of beliefs deleted.
    pub async fn delete_project(&self, project: &str) -> Result<usize> {
        let g = &self.graph_name;
        let project_esc = esc(project);
        // Count first so we can return a meaningful number.
        let count_sql = format!(
            r#"SELECT id::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{project: '{project_esc}'}})
  RETURN n.id
$$) AS (id ag_catalog.agtype)"#
        );
        let rows = sqlx::query(&count_sql).fetch_all(&self.pool).await?;
        let count = rows.len();
        if count == 0 {
            return Ok(0);
        }
        let ids: Vec<Uuid> = rows
            .iter()
            .filter_map(|r| {
                let s: String = r.try_get("id").ok()?;
                Uuid::parse_str(&s).ok()
            })
            .collect();
        let delete_sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{project: '{project_esc}'}})
  DETACH DELETE n
  RETURN 1
$$) AS (ok ag_catalog.agtype)"#
        );
        sqlx::query(&delete_sql).fetch_all(&self.pool).await?;
        self.delete_belief_embeddings(&ids).await?;
        Ok(count)
    }

    pub async fn get_belief(&self, id: Uuid) -> Result<Option<Belief>> {
        let g = &self.graph_name;
        let id_str = id.to_string();
        let sql = format!(
            r#"SELECT
  id::text,
  content::text,
  probability::text,
  confidence::text,
  alpha::text,
  beta::text,
  alpha0::text,
  beta0::text,
  created_at::text,
  last_activated_at::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{id: '{id_str}'}})
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            return Ok(None);
        }
        Ok(Some(belief_from_row(&rows[0])?))
    }

    /// Persist a Phase-3 Beta posterior `(alpha, beta)` and refresh the cached
    /// scalars derived from it (probability = mean = α/(α+β), confidence =
    /// strength-derived). The Beta pair is the durable source of truth; the
    /// scalars are kept in sync so legacy readers stay correct.
    ///
    /// Spec: Mimir.Beta — belief evidence state is written ONLY via the Beta
    /// posterior (store-load-round-trip). The pre-Phase-3 scalar setters
    /// `update_belief_probability` / `update_belief_confidence` are RETIRED
    /// (spec Mimir.Graph: "RETIRED SCALAR SETTERS"); this is their replacement.
    /// Build the SET-Cypher for one Beta write, validating finiteness and
    /// deriving the cached (mean, confidence) from (α, β).
    fn update_belief_beta_sql(&self, id: Uuid, alpha: f64, beta: f64) -> Result<String> {
        let g = &self.graph_name;
        let id_str = id.to_string();
        ensure_finite("update_belief_beta", &[("alpha", alpha), ("beta", beta)])?;
        // Derive the cached (mean, confidence) from (α, β) via the canonical
        // mapping (spec Mimir.Beta).
        let (mean, conf) = crate::graph::beta_to_pc(alpha, beta);
        Ok(format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{id: '{id_str}'}})
  SET n.alpha = {alpha}, n.beta = {beta}, n.probability = {mean}, n.confidence = {conf}
  RETURN n.id
$$) AS (id ag_catalog.agtype)"#
        ))
    }

    pub async fn update_belief_beta(&self, id: Uuid, alpha: f64, beta: f64) -> Result<()> {
        self.update_beliefs_beta(&[(id, alpha, beta)]).await
    }

    /// Persist a batch of Beta posteriors ATOMICALLY: all writes commit in a
    /// single transaction or none do (spec Mimir.Beta: belief state is written
    /// only via the Beta posterior; a propagation/decay sweep must not leave the
    /// graph half-updated). Used by propagate_from and decay_beliefs.
    pub async fn update_beliefs_beta(&self, updates: &[(Uuid, f64, f64)]) -> Result<()> {
        if updates.is_empty() {
            return Ok(());
        }
        // Build all statements first so a finiteness/derivation error aborts
        // before any write is issued.
        let mut stmts = Vec::with_capacity(updates.len());
        for &(id, alpha, beta) in updates {
            stmts.push((id, self.update_belief_beta_sql(id, alpha, beta)?));
        }
        let mut tx = self.pool.begin().await?;
        for (id, sql) in &stmts {
            let rows = sqlx::query(sql).fetch_all(&mut *tx).await?;
            if rows.is_empty() {
                // Belief missing — roll the whole sweep back (tx dropped on early
                // return without commit).
                bail!("belief {} not found", id);
            }
        }
        tx.commit().await?;
        Ok(())
    }

    pub async fn list_beliefs(&self) -> Result<Vec<Belief>> {
        let g = &self.graph_name;
        let sql = format!(
            r#"SELECT
  id::text,
  content::text,
  probability::text,
  confidence::text,
  alpha::text,
  beta::text,
  alpha0::text,
  beta0::text,
  created_at::text,
  last_activated_at::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        let mut beliefs = Vec::with_capacity(rows.len());
        for row in &rows {
            beliefs.push(belief_from_row(row)?);
        }
        Ok(beliefs)
    }

    /// Alias for `list_beliefs` — returns all beliefs for time-decay processing.
    pub async fn get_all_beliefs_for_decay(&self) -> Result<Vec<Belief>> {
        self.list_beliefs().await
    }

    /// Count all Belief vertices. Used by `stats`.
    pub async fn count_beliefs(&self) -> Result<usize> {
        self.count_vertices("Belief").await
    }

    /// Count all Pattern vertices. Used by `stats`.
    pub async fn count_patterns(&self) -> Result<usize> {
        self.count_vertices("Pattern").await
    }

    async fn count_vertices(&self, label: &str) -> Result<usize> {
        let g = &self.graph_name;
        let sql = format!(
            r#"SELECT n::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:{label})
  RETURN count(*) AS n
$$) AS (n ag_catalog.agtype)"#
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            return Ok(0);
        }
        let s: String = rows[0].try_get("n")?;
        Ok(s.parse()?)
    }

    /// Count edges per label. Returns (supports, defeats, causes, contradicts).
    /// CONTRADICTS edges are stored bidirectionally, so the returned value is
    /// the raw directed-edge count (logical pairs × 2).
    pub async fn count_edges(&self) -> Result<(usize, usize, usize, usize)> {
        let supports = self.count_edges_by_label("SUPPORTS").await?;
        let defeats = self.count_edges_by_label("DEFEATS").await?;
        let causes = self.count_edges_by_label("CAUSES").await?;
        let contradicts = self.count_edges_by_label("CONTRADICTS").await?;
        Ok((supports, defeats, causes, contradicts))
    }

    async fn count_edges_by_label(&self, label: &str) -> Result<usize> {
        let g = &self.graph_name;
        let sql = format!(
            r#"SELECT n::text
FROM ag_catalog.cypher('{g}', $$
  MATCH ()-[:{label}]->()
  RETURN count(*) AS n
$$) AS (n ag_catalog.agtype)"#
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            return Ok(0);
        }
        let s: String = rows[0].try_get("n")?;
        Ok(s.parse()?)
    }

    // -----------------------------------------------------------------------
    // Patterns
    // -----------------------------------------------------------------------

    pub async fn insert_pattern(&self, pattern: &Pattern) -> Result<()> {
        let g = &self.graph_name;
        let id = pattern.id.to_string();
        let situation = esc(&pattern.situation);
        let approach = esc(&pattern.approach);
        let activation_count = pattern.activation_count;
        let success_rate = pattern.success_rate.value();
        let created_at = esc(&pattern.created_at.to_rfc3339());

        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  CREATE (p:Pattern {{
    id: '{id}',
    situation: '{situation}',
    approach: '{approach}',
    activation_count: {activation_count},
    success_rate: {success_rate},
    created_at: '{created_at}'
  }})
  RETURN p.id
$$) AS (id ag_catalog.agtype)"#
        );

        sqlx::query(&sql).execute(&self.pool).await?;
        Ok(())
    }

    pub async fn get_pattern(&self, id: Uuid) -> Result<Option<Pattern>> {
        let g = &self.graph_name;
        let id_str = id.to_string();
        let sql = format!(
            r#"SELECT
  id::text,
  situation::text,
  approach::text,
  activation_count::text,
  success_rate::text,
  created_at::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (p:Pattern {{id: '{id_str}'}})
  RETURN p.id, p.situation, p.approach, p.activation_count, p.success_rate, p.created_at
$$) {PATTERN_RETURN_COLUMNS}"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            return Ok(None);
        }
        Ok(Some(pattern_from_row(&rows[0])?))
    }

    /// Delete a pattern and all its edges by ID. Returns true if found and deleted.
    pub async fn delete_pattern(&self, id: Uuid) -> Result<bool> {
        let g = &self.graph_name;
        let id_str = id.to_string();
        let exists = self.get_pattern(id).await?.is_some();
        if !exists {
            return Ok(false);
        }
        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (p:Pattern {{id: '{id_str}'}})
  DETACH DELETE p
  RETURN 1
$$) AS (ok ag_catalog.agtype)"#
        );
        sqlx::query(&sql).fetch_all(&self.pool).await?;
        Ok(true)
    }

    pub async fn list_patterns(&self) -> Result<Vec<Pattern>> {
        let g = &self.graph_name;
        let sql = format!(
            r#"SELECT
  id::text,
  situation::text,
  approach::text,
  activation_count::text,
  success_rate::text,
  created_at::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (p:Pattern)
  RETURN p.id, p.situation, p.approach, p.activation_count, p.success_rate, p.created_at
$$) {PATTERN_RETURN_COLUMNS}"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        let mut patterns = Vec::with_capacity(rows.len());
        for row in &rows {
            patterns.push(pattern_from_row(row)?);
        }
        Ok(patterns)
    }

    // -----------------------------------------------------------------------
    // Edges
    // -----------------------------------------------------------------------

    pub async fn insert_edge(&self, edge: &Edge) -> Result<()> {
        let g = &self.graph_name;
        let from_id = edge.from_id.to_string();
        let to_id = edge.to_id.to_string();
        let label = edge.edge_type.as_str();
        let weight = edge.weight.value();

        // Dynamic label in Cypher requires string interpolation.
        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (a:Belief {{id: '{from_id}'}}), (b:Belief {{id: '{to_id}'}})
  CREATE (a)-[r:{label} {{weight: {weight}}}]->(b)
  RETURN r.weight
$$) AS (weight ag_catalog.agtype)"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            bail!(
                "insert_edge: one or both beliefs not found (from={}, to={})",
                from_id,
                to_id
            );
        }
        Ok(())
    }

    /// Insert two CONTRADICTS edges (bidirectional): from→to and to→from.
    pub async fn insert_contradicts(
        &self,
        from_id: Uuid,
        to_id: Uuid,
        weight: Probability,
    ) -> Result<()> {
        let g = &self.graph_name;
        let a = from_id.to_string();
        let b = to_id.to_string();
        let w = weight.value();

        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (a:Belief {{id: '{a}'}}), (b:Belief {{id: '{b}'}})
  CREATE (a)-[r1:CONTRADICTS {{weight: {w}}}]->(b)
  CREATE (b)-[r2:CONTRADICTS {{weight: {w}}}]->(a)
  RETURN r1.weight
$$) AS (weight ag_catalog.agtype)"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            bail!(
                "insert_contradicts: one or both beliefs not found (from={}, to={})",
                a,
                b
            );
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Graph traversal
    // -----------------------------------------------------------------------

    /// Returns all (from_id, to_id) pairs connected by a CONTRADICTS edge.
    pub async fn get_contradiction_pairs(&self) -> Result<Vec<(Uuid, Uuid)>> {
        let g = &self.graph_name;
        let sql = format!(
            r#"SELECT from_id::text, to_id::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (a:Belief)-[:CONTRADICTS]->(b:Belief)
  RETURN a.id, b.id
$$) AS (from_id ag_catalog.agtype, to_id ag_catalog.agtype)"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        let mut pairs = Vec::with_capacity(rows.len());
        for row in &rows {
            let from_raw: String = row.try_get("from_id")?;
            let to_raw: String = row.try_get("to_id")?;
            let from_id = Uuid::parse_str(&from_raw)?;
            let to_id = Uuid::parse_str(&to_raw)?;
            pairs.push((from_id, to_id));
        }
        Ok(pairs)
    }

    /// Returns all edges (from_id, to_id, label, weight) between any two beliefs
    /// in the provided set of IDs. Used to load the subgraph for propagation.
    pub async fn get_edges_among(
        &self,
        ids: &[Uuid],
    ) -> Result<Vec<(Uuid, Uuid, EdgeType, Probability)>> {
        if ids.is_empty() {
            return Ok(vec![]);
        }

        let g = &self.graph_name;
        // Build a Cypher list literal: ['id1', 'id2', ...]
        let id_list = ids
            .iter()
            .map(|id| format!("'{}'", id))
            .collect::<Vec<_>>()
            .join(", ");

        let sql = format!(
            r#"SELECT from_id::text, to_id::text, label::text, weight::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (a:Belief)-[r]->(b:Belief)
  WHERE a.id IN [{id_list}]
  AND   b.id IN [{id_list}]
  RETURN a.id, b.id, type(r), r.weight
$$) AS (from_id ag_catalog.agtype, to_id ag_catalog.agtype, label ag_catalog.agtype, weight ag_catalog.agtype)"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        let mut edges = Vec::with_capacity(rows.len());
        for row in &rows {
            let from_raw: String = row.try_get("from_id")?;
            let to_raw: String = row.try_get("to_id")?;
            let label_raw: String = row.try_get("label")?;
            let weight_raw: String = row.try_get("weight")?;

            let from_id = Uuid::parse_str(&from_raw)?;
            let to_id = Uuid::parse_str(&to_raw)?;
            let edge_type: EdgeType = label_raw.parse()?;
            let weight: f64 = weight_raw.parse()?;
            let probability = Probability::new(weight)?;

            edges.push((from_id, to_id, edge_type, probability));
        }
        Ok(edges)
    }

    /// Returns ALL propagation edges (SUPPORTS/DEFEATS/CAUSES) pointing INTO any
    /// belief in `ids`, each paired with its SOURCE's stored mean. The source is
    /// UNRESTRICTED (may lie outside `ids`).
    ///
    /// This is the complete incoming-edge set each node's posterior is re-derived
    /// from (spec Mimir.Beta: posteriorOf over the whole incoming list);
    /// `get_edges_among` only sees edges whose source is also in the set, which
    /// silently drops out-of-subgraph evidence. Returning the source mean inline
    /// (the MATCH already visits node `a`) lets the caller build `external_means`
    /// with NO per-source follow-up query. CONTRADICTS is excluded (propagation
    /// skips it). `UNION ALL` (not `UNION`) preserves duplicate parallel edges —
    /// two identical A→B edges are two evidence quanta, not one. AGE 1.x has no
    /// `[:A|B|C]` syntax, so three MATCH arms are combined.
    ///
    /// Each tuple: (from_id, to_id, edge_type, weight, source_mean).
    pub async fn get_incoming_edges(
        &self,
        ids: &[Uuid],
    ) -> Result<Vec<(Uuid, Uuid, EdgeType, Probability, f64)>> {
        if ids.is_empty() {
            return Ok(vec![]);
        }

        let g = &self.graph_name;
        let id_list = ids
            .iter()
            .map(|id| format!("'{}'", id))
            .collect::<Vec<_>>()
            .join(", ");

        // Source mean = a.alpha/(a.alpha+a.beta); computed in Cypher so the
        // caller needs no second fetch. (a.alpha/a.beta are always present
        // post-migration 005; an absent value casts to NULL and parse falls back
        // to 0.5, matching beta_mean's empty-Beta convention.)
        let arm = |label: &str| {
            format!(
                "  MATCH (a:Belief)-[r:{label}]->(b:Belief)\n  \
                 WHERE b.id IN [{id_list}]\n  \
                 RETURN a.id, b.id, type(r), r.weight, a.alpha, a.beta"
            )
        };
        let sql = format!(
            r#"SELECT from_id::text, to_id::text, label::text, weight::text, src_alpha::text, src_beta::text
FROM ag_catalog.cypher('{g}', $$
{sup}
  UNION ALL
{def}
  UNION ALL
{cau}
$$) AS (from_id ag_catalog.agtype, to_id ag_catalog.agtype, label ag_catalog.agtype, weight ag_catalog.agtype, src_alpha ag_catalog.agtype, src_beta ag_catalog.agtype)"#,
            sup = arm("SUPPORTS"),
            def = arm("DEFEATS"),
            cau = arm("CAUSES"),
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        let mut edges = Vec::with_capacity(rows.len());
        for row in &rows {
            let from_id = Uuid::parse_str(&row.try_get::<String, _>("from_id")?)?;
            let to_id = Uuid::parse_str(&row.try_get::<String, _>("to_id")?)?;
            let edge_type: EdgeType = row.try_get::<String, _>("label")?.parse()?;
            let weight: f64 = row.try_get::<String, _>("weight")?.parse()?;
            let probability = Probability::new(weight)?;
            // Source mean from its stored (α, β); fall back to 0.5 (empty-Beta).
            let src_alpha: f64 = row
                .try_get::<String, _>("src_alpha")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(0.0);
            let src_beta: f64 = row
                .try_get::<String, _>("src_beta")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(0.0);
            let source_mean = crate::graph::beta_mean(src_alpha, src_beta);

            edges.push((from_id, to_id, edge_type, probability, source_mean));
        }
        Ok(edges)
    }

    // -----------------------------------------------------------------------
    // Documents
    // -----------------------------------------------------------------------

    /// Insert a DocumentChunk vertex into AGE.
    /// If the chunk has a parent_id, also inserts a CONTAINS edge from parent→child.
    pub async fn insert_document_chunk(&self, chunk: &DocumentChunk) -> Result<()> {
        let g = &self.graph_name;
        let id = chunk.id.to_string();
        let doc_path = esc(&chunk.document_path);
        let content = esc(&chunk.content);

        // Build sectionPath as a Cypher list literal: ['h1', 'h2'] or []
        let section_path_lit = {
            let inner: Vec<String> = chunk
                .section_path
                .iter()
                .map(|s| format!("'{}'", esc(s)))
                .collect();
            format!("[{}]", inner.join(", "))
        };

        let parent_prop = match chunk.parent_id {
            Some(p) => format!(", parentId: '{}'", p),
            None => String::new(),
        };
        let project_prop = match &chunk.project {
            Some(p) => format!(", project: '{}'", esc(p)),
            None => String::new(),
        };

        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  CREATE (c:DocumentChunk {{
    id: '{id}',
    documentPath: '{doc_path}',
    sectionPath: {section_path_lit},
    content: '{content}'{parent_prop}{project_prop}
  }})
  RETURN c.id
$$) AS (id ag_catalog.agtype)"#
        );
        sqlx::query(&sql).execute(&self.pool).await?;

        // Insert CONTAINS edge from parent → child when parent exists.
        if let Some(parent_id) = chunk.parent_id {
            let pid = parent_id.to_string();
            let edge_sql = format!(
                r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (p:DocumentChunk {{id: '{pid}'}}), (c:DocumentChunk {{id: '{id}'}})
  CREATE (p)-[:CONTAINS]->(c)
  RETURN 1
$$) AS (ok ag_catalog.agtype)"#
            );
            sqlx::query(&edge_sql).fetch_all(&self.pool).await?;
        }
        Ok(())
    }

    /// Insert one row into public.chunk_embeddings.
    pub async fn insert_chunk_embedding(&self, chunk_id: Uuid, embedding: &[f32]) -> Result<()> {
        let vec_str = vec_literal(embedding);
        sqlx::query(
            "INSERT INTO public.chunk_embeddings (chunk_id, embedding) \
             VALUES ($1, $2::vector) \
             ON CONFLICT (chunk_id) DO UPDATE SET embedding = EXCLUDED.embedding",
        )
        .bind(chunk_id)
        .bind(&vec_str)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Return chunk IDs for a given document path (used by clear_document).
    pub async fn get_chunk_ids_for_document(&self, path: &str) -> Result<Vec<Uuid>> {
        let g = &self.graph_name;
        let path_esc = esc(path);
        let sql = format!(
            r#"SELECT id::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk {{documentPath: '{path_esc}'}})
  RETURN c.id
$$) AS (id ag_catalog.agtype)"#
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        rows.iter()
            .map(|r| {
                let s: String = r.try_get("id")?;
                Ok(Uuid::parse_str(&s)?)
            })
            .collect()
    }

    /// Return chunk IDs tagged with a project (used by delete_project extension).
    pub async fn get_chunk_ids_by_project(&self, project: &str) -> Result<Vec<Uuid>> {
        let g = &self.graph_name;
        let proj_esc = esc(project);
        let sql = format!(
            r#"SELECT id::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk {{project: '{proj_esc}'}})
  RETURN c.id
$$) AS (id ag_catalog.agtype)"#
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        rows.iter()
            .map(|r| {
                let s: String = r.try_get("id")?;
                Ok(Uuid::parse_str(&s)?)
            })
            .collect()
    }

    /// DETACH DELETE DocumentChunk vertices by IDs. No-op if ids is empty.
    pub async fn delete_document_chunks(&self, ids: &[Uuid]) -> Result<()> {
        if ids.is_empty() {
            return Ok(());
        }
        let g = &self.graph_name;
        let id_list = ids
            .iter()
            .map(|id| format!("'{id}'"))
            .collect::<Vec<_>>()
            .join(", ");
        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk) WHERE c.id IN [{id_list}]
  DETACH DELETE c
  RETURN 1
$$) AS (ok ag_catalog.agtype)"#
        );
        sqlx::query(&sql).fetch_all(&self.pool).await?;
        Ok(())
    }

    /// Delete embedding rows for the given chunk IDs.
    pub async fn delete_chunk_embeddings(&self, ids: &[Uuid]) -> Result<()> {
        if ids.is_empty() {
            return Ok(());
        }
        sqlx::query("DELETE FROM public.chunk_embeddings WHERE chunk_id = ANY($1)")
            .bind(ids)
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    /// Cosine nearest-neighbour search over chunk_embeddings.
    /// If filter_ids is Some, only those chunk IDs are considered.
    /// limit=0 means no limit.
    pub async fn query_chunks_by_vector(
        &self,
        query_vec: &[f32],
        limit: usize,
        filter_ids: Option<&[Uuid]>,
    ) -> Result<Vec<Uuid>> {
        let vec_str = vec_literal(query_vec);
        let limit_clause = if limit > 0 {
            format!("LIMIT {limit}")
        } else {
            String::new()
        };

        let sql = match filter_ids {
            None => format!(
                "SELECT chunk_id::text FROM public.chunk_embeddings \
                 ORDER BY embedding <=> '{vec_str}'::vector {limit_clause}"
            ),
            Some(ids) => {
                // Use a subquery to filter by chunk IDs.
                // parameterized bind for the UUID array, string-interpolated for the vector.
                let id_list = ids
                    .iter()
                    .map(|id| format!("'{id}'"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "SELECT chunk_id::text FROM public.chunk_embeddings \
                     WHERE chunk_id IN ({id_list}) \
                     ORDER BY embedding <=> '{vec_str}'::vector {limit_clause}"
                )
            }
        };

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        rows.iter()
            .map(|r| {
                let s: String = r.try_get("chunk_id")?;
                Ok(Uuid::parse_str(&s)?)
            })
            .collect()
    }

    // -----------------------------------------------------------------------
    // Belief embeddings (vector half of hybrid query_relevant)
    // -----------------------------------------------------------------------

    /// Insert or replace the embedding for a belief.
    pub async fn insert_belief_embedding(&self, belief_id: Uuid, embedding: &[f32]) -> Result<()> {
        let vec_str = vec_literal(embedding);
        sqlx::query(
            "INSERT INTO public.belief_embeddings (belief_id, embedding) \
             VALUES ($1, $2::vector) \
             ON CONFLICT (belief_id) DO UPDATE SET embedding = EXCLUDED.embedding",
        )
        .bind(belief_id)
        .bind(&vec_str)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Delete embedding rows for the given belief IDs. No-op if `ids` is empty.
    pub async fn delete_belief_embeddings(&self, ids: &[Uuid]) -> Result<()> {
        if ids.is_empty() {
            return Ok(());
        }
        sqlx::query("DELETE FROM public.belief_embeddings WHERE belief_id = ANY($1)")
            .bind(ids)
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    /// Cosine nearest-neighbour search over belief_embeddings.
    /// Returns belief IDs ordered by ascending cosine distance (most similar first).
    /// limit=0 means no limit.
    pub async fn query_beliefs_by_vector(
        &self,
        query_vec: &[f32],
        limit: usize,
    ) -> Result<Vec<Uuid>> {
        let vec_str = vec_literal(query_vec);
        let limit_clause = if limit > 0 {
            format!("LIMIT {limit}")
        } else {
            String::new()
        };
        let sql = format!(
            "SELECT belief_id::text FROM public.belief_embeddings \
             ORDER BY embedding <=> '{vec_str}'::vector {limit_clause}"
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        rows.iter()
            .map(|r| {
                let s: String = r.try_get("belief_id")?;
                Ok(Uuid::parse_str(&s)?)
            })
            .collect()
    }

    /// Belief IDs that already have an embedding row (used by `reembed` to skip).
    pub async fn list_embedded_belief_ids(&self) -> Result<Vec<Uuid>> {
        let rows = sqlx::query("SELECT belief_id::text FROM public.belief_embeddings")
            .fetch_all(&self.pool)
            .await?;
        rows.iter()
            .map(|r| {
                let s: String = r.try_get("belief_id")?;
                Ok(Uuid::parse_str(&s)?)
            })
            .collect()
    }

    /// Fetch a single DocumentChunk by ID.
    pub async fn get_chunk_by_id(&self, id: Uuid) -> Result<Option<DocumentChunk>> {
        let g = &self.graph_name;
        let id_str = id.to_string();
        let sql = format!(
            r#"SELECT
  id::text,
  document_path,
  section_path,
  content::text,
  parent_id,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk {{id: '{id_str}'}})
  RETURN c.id, c.documentPath, c.sectionPath, c.content, c.parentId, c.project
$$) {CHUNK_RETURN_COLUMNS}"#
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            return Ok(None);
        }
        Ok(Some(chunk_from_row(&rows[0])?))
    }

    // -----------------------------------------------------------------------
    // Evidence edges (GROUNDS): DocumentChunk → Belief
    //
    // GROUNDS originates at a DocumentChunk and is NEVER matched by belief
    // traversal (get_downstream_beliefs / get_edges_among match (:Belief)->
    // (:Belief) only), so it cannot affect inference. Non-interference is
    // structural — see Mimir.Evidence (propagate-evidence-invariant).
    // -----------------------------------------------------------------------

    /// Create a GROUNDS edge from a DocumentChunk to a Belief, then apply
    /// C-coupling: bump α += EVIDENCE_MASS_K * weight (spec: Mimir.Beta
    /// CCoupling.coupleOne). β is unchanged; the updated (α,β) is written back.
    /// Errors if either endpoint is missing (the MATCH yields no rows).
    ///
    /// Both the CREATE GROUNDS and the α update run inside a single transaction
    /// so concurrent calls cannot lose an increment (no TOCTOU window).
    pub async fn insert_evidence(
        &self,
        chunk_id: Uuid,
        belief_id: Uuid,
        weight: Probability,
    ) -> Result<()> {
        let g = &self.graph_name;
        let c = chunk_id.to_string();
        let b = belief_id.to_string();
        let w = weight.value();

        let create_sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk {{id: '{c}'}}), (b:Belief {{id: '{b}'}})
  CREATE (c)-[r:GROUNDS {{weight: {w}}}]->(b)
  RETURN r.weight
$$) AS (weight ag_catalog.agtype)"#
        );
        let get_sql = format!(
            r#"SELECT
  id::text, content::text, probability::text, confidence::text,
  alpha::text, beta::text, alpha0::text, beta0::text,
  created_at::text, last_activated_at::text, project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{id: '{b}'}})
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta,
         n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let mut tx = self.pool.begin().await?;

        // Step 1: create the GROUNDS edge (errors if endpoints missing).
        let rows = sqlx::query(&create_sql).fetch_all(&mut *tx).await?;
        if rows.is_empty() {
            bail!(
                "insert_evidence: chunk or belief not found (chunk={}, belief={})",
                c,
                b
            );
        }

        // Step 2: read current (α, β) inside the same transaction.
        let rows = sqlx::query(&get_sql).fetch_all(&mut *tx).await?;
        let belief = rows
            .first()
            .map(belief_from_row)
            .transpose()?
            .ok_or_else(|| anyhow::anyhow!("insert_evidence: belief {} vanished", b))?;

        // Step 3: compute new α and derive cached scalars; write back atomically.
        let new_alpha = belief.alpha + EVIDENCE_MASS_K * w;
        let update_sql = self.update_belief_beta_sql(belief_id, new_alpha, belief.beta)?;
        let rows = sqlx::query(&update_sql).fetch_all(&mut *tx).await?;
        if rows.is_empty() {
            bail!("insert_evidence: belief {} disappeared before update", b);
        }

        tx.commit().await?;
        Ok(())
    }

    /// Total grounding mass per belief over all beliefs: Σ k·wᵢ per belief_id.
    /// Used by decay to resist pull toward prior in proportion to evidence mass
    /// (spec Mimir.Beta CCoupling.coupling-increases-strength).
    /// Returns only beliefs that have at least one GROUNDS edge.
    pub async fn get_grounding_mass_all(&self) -> Result<HashMap<Uuid, f64>> {
        let g = &self.graph_name;
        let sql = format!(
            r#"SELECT belief_id::text, total_weight::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk)-[r:GROUNDS]->(b:Belief)
  RETURN b.id, sum(r.weight)
$$) AS (belief_id ag_catalog.agtype, total_weight ag_catalog.agtype)"#
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        let mut out = HashMap::with_capacity(rows.len());
        for row in &rows {
            let id_raw: String = row.try_get("belief_id")?;
            let w_raw: String = row.try_get("total_weight")?;
            let id = Uuid::parse_str(&id_raw)?;
            let total: f64 = w_raw.parse()?;
            out.insert(id, total * EVIDENCE_MASS_K);
        }
        Ok(out)
    }

    /// For a set of beliefs, return their grounding as (belief_id, chunk_id, weight).
    pub async fn get_evidence_for_beliefs(
        &self,
        belief_ids: &[Uuid],
    ) -> Result<Vec<(Uuid, Uuid, f64)>> {
        if belief_ids.is_empty() {
            return Ok(vec![]);
        }
        let g = &self.graph_name;
        let id_list = belief_ids
            .iter()
            .map(|i| format!("'{}'", i))
            .collect::<Vec<_>>()
            .join(", ");
        let sql = format!(
            r#"SELECT belief_id::text, chunk_id::text, weight::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk)-[r:GROUNDS]->(b:Belief)
  WHERE b.id IN [{id_list}]
  RETURN b.id, c.id, r.weight
$$) AS (belief_id ag_catalog.agtype, chunk_id ag_catalog.agtype, weight ag_catalog.agtype)"#
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        let mut out = Vec::with_capacity(rows.len());
        for row in &rows {
            let belief_raw: String = row.try_get("belief_id")?;
            let chunk_raw: String = row.try_get("chunk_id")?;
            let weight_raw: String = row.try_get("weight")?;
            let belief_id = Uuid::parse_str(&belief_raw)?;
            let chunk_id = Uuid::parse_str(&chunk_raw)?;
            let weight: f64 = weight_raw.parse()?;
            out.push((belief_id, chunk_id, weight));
        }
        Ok(out)
    }

    /// Remove a specific GROUNDS edge. (Edges are also GC'd automatically by the
    /// DETACH DELETE on either endpoint; this is for explicit unlink.)
    pub async fn delete_evidence(&self, chunk_id: Uuid, belief_id: Uuid) -> Result<()> {
        let g = &self.graph_name;
        let c = chunk_id.to_string();
        let b = belief_id.to_string();
        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk {{id: '{c}'}})-[r:GROUNDS]->(b:Belief {{id: '{b}'}})
  DELETE r
$$) AS (v ag_catalog.agtype)"#
        );
        sqlx::query(&sql).execute(&self.pool).await?;
        Ok(())
    }

    /// Returns all Belief nodes reachable from `start_id` via PROPAGATION edges
    /// (SUPPORTS, CAUSES, or DEFEATS) — the propagation recompute set.
    ///
    /// Spec Mimir.Graph (propagation scope): the set is the UNBOUNDED transitive
    /// closure under SUPPORTS ∪ CAUSES ∪ DEFEATS (`Reaches` / `reaches-closed`),
    /// so a bare S→DEFEATS→T reaches T (`defeat-target-is-reached`) and no
    /// affected descendant is excluded by a depth cap. CONTRADICTS is excluded
    /// (it is detected, never propagated).
    ///
    /// AGE 1.x has no `[:A|B|C]` relationship-type OR syntax, so three MATCH
    /// clauses are UNION'd; `*1..` is the unbounded variable-length path (length
    /// ≥ 1, so the seed itself is excluded; AGE's VLE does not revisit a node
    /// within one path, so cycles terminate).
    pub async fn get_downstream_beliefs(&self, start_id: Uuid) -> Result<Vec<Belief>> {
        let g = &self.graph_name;
        let id_str = start_id.to_string();

        let sql = format!(
            r#"SELECT
  id::text,
  content::text,
  probability::text,
  confidence::text,
  alpha::text,
  beta::text,
  alpha0::text,
  beta0::text,
  created_at::text,
  last_activated_at::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (s:Belief {{id: '{id_str}'}})-[:SUPPORTS*1..]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.project
  UNION
  MATCH (s:Belief {{id: '{id_str}'}})-[:CAUSES*1..]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.project
  UNION
  MATCH (s:Belief {{id: '{id_str}'}})-[:DEFEATS*1..]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        let mut beliefs = Vec::with_capacity(rows.len());
        for row in &rows {
            beliefs.push(belief_from_row(row)?);
        }
        Ok(beliefs)
    }

    /// Beliefs reachable from `start_id` along CAUSES edges only — the causal
    /// descendants, i.e. the candidate set for an intervention `do(start = v)`.
    /// Mirrors `get_downstream_beliefs` but keeps only the causal branch
    /// (no SUPPORTS UNION), since an intervention propagates along causal
    /// edges alone. Excludes the seed itself (the `*1..10` path has length ≥ 1).
    pub async fn get_causal_downstream_beliefs(&self, start_id: Uuid) -> Result<Vec<Belief>> {
        let g = &self.graph_name;
        let id_str = start_id.to_string();

        let sql = format!(
            r#"SELECT
  id::text,
  content::text,
  probability::text,
  confidence::text,
  alpha::text,
  beta::text,
  alpha0::text,
  beta0::text,
  created_at::text,
  last_activated_at::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (s:Belief {{id: '{id_str}'}})-[:CAUSES*1..10]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        let mut beliefs = Vec::with_capacity(rows.len());
        for row in &rows {
            beliefs.push(belief_from_row(row)?);
        }
        Ok(beliefs)
    }
}

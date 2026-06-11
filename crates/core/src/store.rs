use anyhow::{bail, Result};
use chrono::DateTime;
use sqlx::{PgPool, Row};
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

/// SQL fragment for returning all Belief scalar properties cast to TEXT.
const BELIEF_RETURN_COLUMNS: &str = r#"AS (
  id             text,
  content        text,
  probability    text,
  confidence     text,
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
  created_at::text,
  last_activated_at::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{id: '{id_str}'}})
  RETURN n.id, n.content, n.probability, n.confidence, n.created_at, n.last_activated_at, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            return Ok(None);
        }
        Ok(Some(belief_from_row(&rows[0])?))
    }

    pub async fn update_belief_probability(
        &self,
        id: Uuid,
        probability: Probability,
    ) -> Result<()> {
        let g = &self.graph_name;
        let id_str = id.to_string();
        let p = probability.value();
        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{id: '{id_str}'}})
  SET n.probability = {p}
  RETURN n.id
$$) AS (id ag_catalog.agtype)"#
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            bail!("belief {} not found", id);
        }
        Ok(())
    }

    pub async fn update_belief_confidence(&self, id: Uuid, confidence: Probability) -> Result<()> {
        let g = &self.graph_name;
        let id_str = id.to_string();
        let c = confidence.value();
        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{id: '{id_str}'}})
  SET n.confidence = {c}
  RETURN n.id
$$) AS (id ag_catalog.agtype)"#
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            bail!("belief {} not found", id);
        }
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
  created_at::text,
  last_activated_at::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.created_at, n.last_activated_at, n.project
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

    /// Create a GROUNDS edge from a DocumentChunk to a Belief.
    /// Errors if either endpoint is missing (the MATCH yields no rows).
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
        let sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk {{id: '{c}'}}), (b:Belief {{id: '{b}'}})
  CREATE (c)-[r:GROUNDS {{weight: {w}}}]->(b)
  RETURN r.weight
$$) AS (weight ag_catalog.agtype)"#
        );
        let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
        if rows.is_empty() {
            bail!(
                "insert_evidence: chunk or belief not found (chunk={}, belief={})",
                c,
                b
            );
        }
        Ok(())
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

    /// Returns all Belief nodes reachable from `start_id` via SUPPORTS or CAUSES edges.
    ///
    /// AGE 1.x does not support the `[:A|B]` relationship-type OR syntax, so we use
    /// two separate MATCH clauses combined with UNION inside the Cypher block.
    pub async fn get_downstream_beliefs(&self, start_id: Uuid) -> Result<Vec<Belief>> {
        let g = &self.graph_name;
        let id_str = start_id.to_string();

        // Two-query UNION approach: SUPPORTS paths + CAUSES paths.
        let sql = format!(
            r#"SELECT
  id::text,
  content::text,
  probability::text,
  confidence::text,
  created_at::text,
  last_activated_at::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (s:Belief {{id: '{id_str}'}})-[:SUPPORTS*1..10]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.created_at, n.last_activated_at, n.project
  UNION
  MATCH (s:Belief {{id: '{id_str}'}})-[:CAUSES*1..10]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.created_at, n.last_activated_at, n.project
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
  created_at::text,
  last_activated_at::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (s:Belief {{id: '{id_str}'}})-[:CAUSES*1..10]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.created_at, n.last_activated_at, n.project
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

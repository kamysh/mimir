use anyhow::{bail, Result};
use chrono::DateTime;
use sqlx::{PgPool, Row};
use uuid::Uuid;

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
    let created_at =
        DateTime::parse_from_rfc3339(&created_at_str)?.with_timezone(&chrono::Utc);
    let last_activated_at =
        DateTime::parse_from_rfc3339(&last_activated_str)?.with_timezone(&chrono::Utc);

    Ok(Belief {
        id,
        content,
        probability: Probability::new(probability)?,
        confidence: Probability::new(confidence)?,
        created_at,
        last_activated_at,
        project,
    })
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
    let created_at =
        DateTime::parse_from_rfc3339(&created_at_str)?.with_timezone(&chrono::Utc);

    Ok(Pattern {
        id,
        situation,
        approach,
        activation_count,
        success_rate: Probability::new(success_rate)?,
        created_at,
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

// ---------------------------------------------------------------------------
// AgeStore
// ---------------------------------------------------------------------------

pub struct AgeStore {
    pool: PgPool,
    /// AGE graph name — equals the PostgreSQL database name from config.
    graph_name: String,
}

impl AgeStore {
    pub async fn new(pool: PgPool, graph_name: String) -> Result<Self> {
        let store = Self { pool, graph_name };
        store.ensure_labels().await?;
        Ok(store)
    }

    /// Pre-create all vertex and edge labels so concurrent callers never race
    /// on lazy label creation. Uses DO blocks with EXCEPTION to be idempotent.
    async fn ensure_labels(&self) -> Result<()> {
        const VLABELS: &[&str] = &["Belief", "Pattern"];
        const ELABELS: &[&str] = &["SUPPORTS", "DEFEATS", "CAUSES", "CONTRADICTS"];
        let g = &self.graph_name;

        for label in VLABELS {
            let sql = format!(
                "DO $$ BEGIN PERFORM ag_catalog.create_vlabel('{g}', '{label}'); \
                 EXCEPTION WHEN others THEN NULL; END $$"
            );
            sqlx::query(&sql).execute(&self.pool).await?;
        }
        for label in ELABELS {
            let sql = format!(
                "DO $$ BEGIN PERFORM ag_catalog.create_elabel('{g}', '{label}'); \
                 EXCEPTION WHEN others THEN NULL; END $$"
            );
            sqlx::query(&sql).execute(&self.pool).await?;
        }
        Ok(())
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
        let delete_sql = format!(
            r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{project: '{project_esc}'}})
  DETACH DELETE n
  RETURN 1
$$) AS (ok ag_catalog.agtype)"#
        );
        sqlx::query(&delete_sql).fetch_all(&self.pool).await?;
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
            let edge_type = EdgeType::from_str(&label_raw)?;
            let weight: f64 = weight_raw.parse()?;
            let probability = Probability::new(weight)?;

            edges.push((from_id, to_id, edge_type, probability));
        }
        Ok(edges)
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
}
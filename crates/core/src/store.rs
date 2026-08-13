use anyhow::{bail, Result};
use chrono::DateTime;
use pgvector::Vector;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;
use tokio_postgres::{Client, Row};
use uuid::Uuid;

use crate::documents::DocumentChunk;
use crate::graph::{Belief, Edge, EdgeType, MemoryType, Pattern, Probability};

// ---------------------------------------------------------------------------
// AGE PREPARE/EXECUTE helpers
//
// AGE requires the agtype parameter to be a real SQL PREPARE parameter ($1),
// not a plain literal interpolated into the Cypher string. The only way to
// achieve this from tokio-postgres is via simple_query (plain text protocol):
//   PREPARE stmt(agtype) AS SELECT … FROM cypher(…, $1) AS (…);
//   EXECUTE stmt('<json>');
//   DEALLOCATE stmt;
//
// Escaping layers for the agtype JSON value in EXECUTE stmt('...'):
//   1. JSON layer: standard JSON string escaping (\, ", and control chars)
//   2. SQL layer:  ' → '' (SQL string literal escaping)
// Single quotes in the content are fine unescaped in JSON; only SQL-level
// doubling is needed for them.
// ---------------------------------------------------------------------------

/// Escape a string for use as a JSON string value inside an agtype literal.
/// Step 1 of the two-layer escaping: JSON layer only. Escapes `\`, `"`, and
/// every JSON-mandated control character (U+0000..U+001F) — an unescaped
/// literal newline/tab/etc in the input would otherwise produce invalid JSON
/// once embedded in the agtype literal, turning a merely-unmatched query into
/// a hard PREPARE/EXECUTE error.
fn json_esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\u{08}' => out.push_str("\\b"),
            '\u{0C}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out
}

/// Escape an agtype JSON literal for embedding inside a SQL string literal
/// (the argument to EXECUTE stmt('...')).
/// Step 2: SQL-level single-quote doubling of the full agtype string.
fn sql_esc(agtype_json: &str) -> String {
    agtype_json.replace('\'', "''")
}

/// Run PREPARE / EXECUTE / DEALLOCATE for a Cypher write that takes one
/// agtype parameter, using simple_query (plain-text protocol) so AGE accepts $1.
/// `stmt_name` must be unique per connection; callers use a UUID-derived name.
/// `prepare_sql` is the PREPARE statement (without trailing semicolon).
/// `agtype_json` is the raw JSON object (unescaped); this function applies
/// the SQL-layer escaping before sending.
async fn age_execute(
    client: &Client,
    stmt_name: &str,
    prepare_sql: &str,
    agtype_json: &str,
) -> Result<()> {
    // If PREPARE fails we return early — no session state was created, so
    // DEALLOCATE would error on a non-existent statement. Do NOT move
    // DEALLOCATE above this line.
    client.simple_query(prepare_sql).await?;
    let exec = format!("EXECUTE {}('{}')", stmt_name, sql_esc(agtype_json));
    let result = client.simple_query(&exec).await;
    // DEALLOCATE runs unconditionally after EXECUTE, even on EXECUTE failure,
    // so the session is always left clean.
    let _ = client
        .simple_query(&format!("DEALLOCATE {}", stmt_name))
        .await;
    result?;
    Ok(())
}

/// Like `age_execute`, but for a Cypher read: runs PREPARE / EXECUTE /
/// DEALLOCATE and returns the `SimpleQueryRow`s from EXECUTE (non-Row
/// messages, e.g. the command-complete tag, are dropped). Shared by every
/// `*_by_project`-style scoped read (list_beliefs_by_project,
/// list_patterns_by_project, get_contradiction_pairs_by_project,
/// get_direct_downstream_by_project) so the PREPARE/EXECUTE/DEALLOCATE
/// sequence exists in one place instead of being hand-rolled per method.
async fn age_query_rows(
    client: &Client,
    stmt_name: &str,
    prepare_sql: &str,
    agtype_json: &str,
) -> Result<Vec<tokio_postgres::SimpleQueryRow>> {
    client.simple_query(prepare_sql).await?;
    let exec = format!("EXECUTE {}('{}')", stmt_name, sql_esc(agtype_json));
    let result = client.simple_query(&exec).await;
    let _ = client
        .simple_query(&format!("DEALLOCATE {}", stmt_name))
        .await;
    let msgs = result?;
    Ok(msgs
        .into_iter()
        .filter_map(|m| match m {
            tokio_postgres::SimpleQueryMessage::Row(row) => Some(row),
            _ => None,
        })
        .collect())
}

/// Closed enum for vertex labels used in `count_vertices`. Using an enum
/// instead of `&str` makes it impossible to pass arbitrary user input as a
/// Cypher label.
enum VertexLabel {
    Belief,
    Pattern,
}

impl VertexLabel {
    fn label(self) -> &'static str {
        match self {
            Self::Belief => "Belief",
            Self::Pattern => "Pattern",
        }
    }
}

/// Closed enum for edge labels used in `count_edges_by_label`.
enum EdgeLabel {
    Supports,
    Defeats,
    Causes,
    Contradicts,
}

impl EdgeLabel {
    fn label(self) -> &'static str {
        match self {
            Self::Supports => "SUPPORTS",
            Self::Defeats => "DEFEATS",
            Self::Causes => "CAUSES",
            Self::Contradicts => "CONTRADICTS",
        }
    }
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

/// A row that exposes its columns as text by name, implemented for both the
/// extended-protocol `Row` and the simple-query-protocol `SimpleQueryRow` so
/// `belief_from_row`-style decoding works over either query path.
trait TextRow {
    fn text(&self, name: &str) -> Option<&str>;
}

impl TextRow for Row {
    fn text(&self, name: &str) -> Option<&str> {
        self.get(name)
    }
}

impl TextRow for tokio_postgres::SimpleQueryRow {
    fn text(&self, name: &str) -> Option<&str> {
        self.get(name)
    }
}

/// Decode a `Belief` from a tokio-postgres Row with columns:
///   id TEXT, content TEXT, probability TEXT, confidence TEXT,
///   alpha TEXT, beta TEXT, alpha0 TEXT, beta0 TEXT,
///   created_at TEXT, last_activated_at TEXT, project TEXT
fn belief_from_row(row: &Row) -> Result<Belief> {
    belief_from_text_row(row)
}

/// Same decoding as `belief_from_row`, for rows produced via `simple_query`
/// (used by the PREPARE/EXECUTE-with-agtype-param pattern).
fn belief_from_simple_row(row: &tokio_postgres::SimpleQueryRow) -> Result<Belief> {
    belief_from_text_row(row)
}

fn belief_from_text_row<R: TextRow>(row: &R) -> Result<Belief> {
    let id_str: &str = row
        .text("id")
        .ok_or_else(|| anyhow::anyhow!("missing column id"))?;
    let content: &str = row
        .text("content")
        .ok_or_else(|| anyhow::anyhow!("missing column content"))?;
    let probability_str: &str = row
        .text("probability")
        .ok_or_else(|| anyhow::anyhow!("missing column probability"))?;
    let confidence_str: &str = row
        .text("confidence")
        .ok_or_else(|| anyhow::anyhow!("missing column confidence"))?;
    let created_at_str: &str = row
        .text("created_at")
        .ok_or_else(|| anyhow::anyhow!("missing column created_at"))?;
    let last_activated_str: &str = row
        .text("last_activated_at")
        .ok_or_else(|| anyhow::anyhow!("missing column last_activated_at"))?;
    let project: Option<&str> = row.text("project");

    let id = Uuid::parse_str(id_str)?;
    let probability: f64 = probability_str.parse()?;
    let confidence: f64 = confidence_str.parse()?;
    let created_at = DateTime::parse_from_rfc3339(created_at_str)?.with_timezone(&chrono::Utc);
    let last_activated_at =
        DateTime::parse_from_rfc3339(last_activated_str)?.with_timezone(&chrono::Utc);

    // Beta state: read α/β/α₀/β₀ if present (post-migration 005), else derive
    // them from the stored (probability, confidence) via the prior mapping.
    let alpha_str: Option<&str> = row.text("alpha");
    let beta_str: Option<&str> = row.text("beta");
    let alpha0_str: Option<&str> = row.text("alpha0");
    let beta0_str: Option<&str> = row.text("beta0");

    let alpha: Option<f64> = alpha_str.and_then(|s| s.parse().ok());
    let beta: Option<f64> = beta_str.and_then(|s| s.parse().ok());
    let alpha0: Option<f64> = alpha0_str.and_then(|s| s.parse().ok());
    let beta0: Option<f64> = beta0_str.and_then(|s| s.parse().ok());

    let (derived_a0, derived_b0) = crate::graph::prior_from(probability, confidence);
    let alpha0 = alpha0.unwrap_or(derived_a0);
    let beta0 = beta0.unwrap_or(derived_b0);
    let alpha = alpha.unwrap_or(alpha0);
    let beta = beta.unwrap_or(beta0);

    // Absent or unparseable memory_type (pre-migration rows) decodes as Fact,
    // preserving today's decay behavior for every belief written before this
    // field existed.
    let memory_type: MemoryType = row
        .text("memory_type")
        .and_then(|s| s.parse().ok())
        .unwrap_or_default();

    Belief::from_stored(
        id,
        content.to_owned(),
        alpha,
        beta,
        alpha0,
        beta0,
        created_at,
        last_activated_at,
        memory_type,
        project.map(str::to_owned),
    )
}

/// Decode a `Pattern` from a tokio-postgres Row with columns:
///   id TEXT, situation TEXT, approach TEXT, activation_count TEXT,
///   success_rate TEXT, created_at TEXT
fn pattern_from_row(row: &Row) -> Result<Pattern> {
    pattern_from_text_row(row)
}

/// Same decoding as `pattern_from_row`, for rows produced via `simple_query`.
fn pattern_from_simple_row(row: &tokio_postgres::SimpleQueryRow) -> Result<Pattern> {
    pattern_from_text_row(row)
}

fn pattern_from_text_row<R: TextRow>(row: &R) -> Result<Pattern> {
    let id_str: &str = row
        .text("id")
        .ok_or_else(|| anyhow::anyhow!("missing column id"))?;
    let situation: &str = row
        .text("situation")
        .ok_or_else(|| anyhow::anyhow!("missing column situation"))?;
    let approach: &str = row
        .text("approach")
        .ok_or_else(|| anyhow::anyhow!("missing column approach"))?;
    let activation_count_str: &str = row
        .text("activation_count")
        .ok_or_else(|| anyhow::anyhow!("missing column activation_count"))?;
    let success_rate_str: &str = row
        .text("success_rate")
        .ok_or_else(|| anyhow::anyhow!("missing column success_rate"))?;
    let created_at_str: &str = row
        .text("created_at")
        .ok_or_else(|| anyhow::anyhow!("missing column created_at"))?;
    let project: Option<&str> = row.text("project");

    let id = Uuid::parse_str(id_str)?;
    let activation_count: u32 = activation_count_str.parse()?;
    let success_rate: f64 = success_rate_str.parse()?;
    let created_at = DateTime::parse_from_rfc3339(created_at_str)?.with_timezone(&chrono::Utc);

    Ok(Pattern {
        id,
        situation: situation.to_owned(),
        approach: approach.to_owned(),
        activation_count,
        success_rate: Probability::new(success_rate)?,
        created_at,
        project: project.map(str::to_owned),
    })
}

/// Decode a `DocumentChunk` from a tokio-postgres Row with columns:
///   id TEXT, document_path TEXT, section_path TEXT (agtype list as JSON),
///   content TEXT, parent_id TEXT, project TEXT
fn chunk_from_row(row: &Row) -> Result<DocumentChunk> {
    let id_str: &str = row.get("id");
    let document_path: &str = row.get("document_path");
    let section_path_str: &str = row.get("section_path");
    let content: &str = row.get("content");
    let parent_id_str: Option<&str> = row.get("parent_id");
    let project: Option<&str> = row.get("project");

    let id = Uuid::parse_str(id_str)?;
    // AGE lists cast to text as JSON arrays: ["H1","H2"] or []
    let section_path: Vec<String> = serde_json::from_str(section_path_str).unwrap_or_default();
    let parent_id = parent_id_str.and_then(|s| Uuid::parse_str(s).ok());

    Ok(DocumentChunk {
        id,
        document_path: document_path.to_owned(),
        section_path,
        content: content.to_owned(),
        parent_id,
        project: project.map(str::to_owned),
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
  memory_type    text,
  project        text
)"#;

/// SQL fragment for returning all Pattern scalar properties cast to TEXT.
const PATTERN_RETURN_COLUMNS: &str = r#"AS (
  id               text,
  situation        text,
  approach         text,
  activation_count text,
  success_rate     text,
  created_at       text,
  project          text
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
    client: Arc<Mutex<Client>>,
    /// AGE graph name — equals the PostgreSQL database name from config.
    graph_name: String,
}

impl AgeStore {
    /// Construct a new store. `graph_name` must consist solely of ASCII
    /// alphanumeric characters and underscores — it is interpolated directly
    /// into SQL strings (as the `cypher('{g}', …)` graph-name argument) and
    /// cannot be parameterized. The validation here makes that invariant a
    /// type-level guarantee rather than a config-discipline assumption.
    pub fn new(client: Client, graph_name: String) -> Result<Self> {
        anyhow::ensure!(
            !graph_name.is_empty()
                && graph_name
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_'),
            "graph_name must be non-empty and contain only ASCII alphanumeric/underscore characters: {:?}",
            graph_name
        );
        Ok(Self {
            client: Arc::new(Mutex::new(client)),
            graph_name,
        })
    }

    // -----------------------------------------------------------------------
    // Beliefs
    // -----------------------------------------------------------------------

    pub async fn insert_belief(&self, belief: &Belief) -> Result<()> {
        let g = &self.graph_name;
        let id = belief.id.to_string();
        let probability = belief.probability.value();
        let confidence = belief.confidence.value();
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
        let created_at = belief.created_at.to_rfc3339();
        let last_activated_at = belief.last_activated_at.to_rfc3339();
        let memory_type = belief.memory_type.as_str();

        let project_prop = match &belief.project {
            Some(p) => format!(r#", "project": "{}""#, json_esc(p)),
            None => String::new(),
        };
        let agtype_json = format!(
            r#"{{"id": "{id}", "content": "{}", "created_at": "{created_at}", "last_activated_at": "{last_activated_at}", "memory_type": "{memory_type}"{project_prop}}}"#,
            json_esc(&belief.content)
        );

        let stmt = format!("age_ins_{}", belief.id.simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT * FROM ag_catalog.cypher('{g}', $$ \
             CREATE (n:Belief {{id: $id, content: $content, \
             probability: {probability}, confidence: {confidence}, \
             alpha: {alpha}, beta: {beta}, alpha0: {alpha0}, beta0: {beta0}, \
             created_at: $created_at, last_activated_at: $last_activated_at, \
             memory_type: $memory_type{}}}) \
             RETURN n.id $$, $1) AS (id ag_catalog.agtype)",
            if belief.project.is_some() {
                ", project: $project"
            } else {
                ""
            }
        );

        let client = self.client.lock().await;
        age_execute(&client, &stmt, &prepare, &agtype_json).await
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
        let client = self.client.lock().await;
        client.query(&sql, &[]).await?;
        drop(client);
        self.delete_belief_embeddings(&[id]).await?;
        Ok(true)
    }

    /// Delete all beliefs (and their edges) tagged with the given project.
    /// Returns the number of beliefs deleted.
    pub async fn delete_project(&self, project: &str) -> Result<usize> {
        let g = &self.graph_name;
        let agtype_json = format!(r#"{{"project": "{}"}}"#, json_esc(project));

        // Count first so we can return a meaningful number.
        // UUID-derived names avoid collision on connection reuse (PREPARE is session-scoped).
        let stmt_count = format!("age_delproj_count_{}", Uuid::new_v4().simple());
        let prepare_count = format!(
            "PREPARE {stmt_count}(agtype) AS SELECT id::text \
             FROM ag_catalog.cypher('{g}', $$ \
             MATCH (n:Belief) WHERE n.project = $project RETURN n.id \
             $$, $1) AS (id agtype)"
        );
        let exec_count = format!("EXECUTE {stmt_count}('{}')", sql_esc(&agtype_json));

        let client = self.client.lock().await;
        client.simple_query(&prepare_count).await?;
        let msgs = client.simple_query(&exec_count).await;
        let _ = client
            .simple_query(&format!("DEALLOCATE {stmt_count}"))
            .await;
        let msgs = msgs?;

        let count = msgs
            .iter()
            .filter(|m| matches!(m, tokio_postgres::SimpleQueryMessage::Row(_)))
            .count();
        if count == 0 {
            return Ok(0);
        }
        let ids: Vec<Uuid> = msgs
            .iter()
            .filter_map(|m| {
                if let tokio_postgres::SimpleQueryMessage::Row(row) = m {
                    row.get(0).and_then(|s| Uuid::parse_str(s).ok())
                } else {
                    None
                }
            })
            .collect();

        let stmt_del = format!("age_delproj_del_{}", Uuid::new_v4().simple());
        let prepare_del = format!(
            "PREPARE {stmt_del}(agtype) AS SELECT * \
             FROM ag_catalog.cypher('{g}', $$ \
             MATCH (n:Belief) WHERE n.project = $project DETACH DELETE n RETURN 1 \
             $$, $1) AS (ok agtype)"
        );
        age_execute(&client, &stmt_del, &prepare_del, &agtype_json).await?;

        // Also purge Pattern nodes tagged with the same project.
        let stmt_pat = format!("age_delproj_pat_{}", Uuid::new_v4().simple());
        let prepare_pat = format!(
            "PREPARE {stmt_pat}(agtype) AS SELECT * \
             FROM ag_catalog.cypher('{g}', $$ \
             MATCH (p:Pattern) WHERE p.project = $project DETACH DELETE p RETURN 1 \
             $$, $1) AS (ok agtype)"
        );
        age_execute(&client, &stmt_pat, &prepare_pat, &agtype_json).await?;

        drop(client);
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
  memory_type::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{id: '{id_str}'}})
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
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
        let mut client = self.client.lock().await;
        let tx = client.transaction().await?;
        for (id, sql) in &stmts {
            let rows = tx.query(sql, &[]).await?;
            if rows.is_empty() {
                // Belief missing — roll the whole sweep back.
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
  memory_type::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        let mut beliefs = Vec::with_capacity(rows.len());
        for row in &rows {
            beliefs.push(belief_from_row(row)?);
        }
        Ok(beliefs)
    }

    /// Like `list_beliefs`, but scoped to a project: returns beliefs whose
    /// `project` matches, plus untagged beliefs (`project` unset), which are
    /// treated as global and always included alongside any project's beliefs.
    pub async fn list_beliefs_by_project(&self, project: &str) -> Result<Vec<Belief>> {
        let g = &self.graph_name;
        let agtype_json = format!(r#"{{"project": "{}"}}"#, json_esc(project));
        let stmt = format!("age_list_beliefs_proj_{}", Uuid::new_v4().simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT \
             id::text, content::text, probability::text, confidence::text, \
             alpha::text, beta::text, alpha0::text, beta0::text, \
             created_at::text, last_activated_at::text, memory_type::text, project::text \
             FROM ag_catalog.cypher('{g}', $$ \
             MATCH (n:Belief) WHERE n.project = $project OR n.project IS NULL \
             RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project \
             $$, $1) {BELIEF_RETURN_COLUMNS}"
        );

        let client = self.client.lock().await;
        let rows = age_query_rows(&client, &stmt, &prepare, &agtype_json).await?;
        let mut beliefs = Vec::with_capacity(rows.len());
        for row in &rows {
            beliefs.push(belief_from_simple_row(row)?);
        }
        Ok(beliefs)
    }

    /// Alias for `list_beliefs` — returns all beliefs for time-decay processing.
    pub async fn get_all_beliefs_for_decay(&self) -> Result<Vec<Belief>> {
        self.list_beliefs().await
    }

    /// Count all Belief vertices. Used by `stats`.
    pub async fn count_beliefs(&self) -> Result<usize> {
        self.count_vertices(VertexLabel::Belief).await
    }

    /// Count all Pattern vertices. Used by `stats`.
    pub async fn count_patterns(&self) -> Result<usize> {
        self.count_vertices(VertexLabel::Pattern).await
    }

    async fn count_vertices(&self, label: VertexLabel) -> Result<usize> {
        let g = &self.graph_name;
        let label = label.label();
        let sql = format!(
            r#"SELECT n::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:{label})
  RETURN count(*) AS n
$$) AS (n ag_catalog.agtype)"#
        );
        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        if rows.is_empty() {
            return Ok(0);
        }
        let s: &str = rows[0].get("n");
        Ok(s.parse()?)
    }

    /// Count edges per label. Returns (supports, defeats, causes, contradicts).
    /// CONTRADICTS edges are stored bidirectionally, so the returned value is
    /// the raw directed-edge count (logical pairs × 2).
    pub async fn count_edges(&self) -> Result<(usize, usize, usize, usize)> {
        let supports = self.count_edges_by_label(EdgeLabel::Supports).await?;
        let defeats = self.count_edges_by_label(EdgeLabel::Defeats).await?;
        let causes = self.count_edges_by_label(EdgeLabel::Causes).await?;
        let contradicts = self.count_edges_by_label(EdgeLabel::Contradicts).await?;
        Ok((supports, defeats, causes, contradicts))
    }

    async fn count_edges_by_label(&self, label: EdgeLabel) -> Result<usize> {
        let g = &self.graph_name;
        let label = label.label();
        let sql = format!(
            r#"SELECT n::text
FROM ag_catalog.cypher('{g}', $$
  MATCH ()-[:{label}]->()
  RETURN count(*) AS n
$$) AS (n ag_catalog.agtype)"#
        );
        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        if rows.is_empty() {
            return Ok(0);
        }
        let s: &str = rows[0].get("n");
        Ok(s.parse()?)
    }

    /// Returns every (defeater_id, defeated_id, defeater_created_at) triple for
    /// DEFEATS relationships in the graph. Used by the attenuated-deletion sweep
    /// (docs/proposals/80-memory-evolution-open-questions.md, section 1) to find
    /// defeated beliefs whose grace period has elapsed. DEFEATS edges carry no
    /// timestamp of their own, so the defeater's `created_at` is returned as the
    /// proxy for when the defeat happened — see `InferenceEngine::find_expired_defeated`.
    pub async fn get_defeats_with_timestamps(
        &self,
    ) -> Result<Vec<(Uuid, Uuid, chrono::DateTime<chrono::Utc>)>> {
        let g = &self.graph_name;
        let sql = format!(
            r#"SELECT defeater_id::text, defeated_id::text, defeater_created_at::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (a:Belief)-[:DEFEATS]->(b:Belief)
  RETURN a.id, b.id, a.created_at
$$) AS (defeater_id ag_catalog.agtype, defeated_id ag_catalog.agtype, defeater_created_at ag_catalog.agtype)"#
        );
        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        let mut triples = Vec::with_capacity(rows.len());
        for row in &rows {
            let defeater_id = Uuid::parse_str(row.get::<_, &str>("defeater_id"))?;
            let defeated_id = Uuid::parse_str(row.get::<_, &str>("defeated_id"))?;
            let created_at_str: &str = row.get("defeater_created_at");
            let defeater_created_at =
                DateTime::parse_from_rfc3339(created_at_str)?.with_timezone(&chrono::Utc);
            triples.push((defeater_id, defeated_id, defeater_created_at));
        }
        Ok(triples)
    }

    /// Like `get_defeats_with_timestamps`, scoped to a project: only edges
    /// where both endpoints match the project (or are untagged/global) are
    /// returned, matching `list_beliefs_by_project`'s inclusion semantics.
    pub async fn get_defeats_with_timestamps_by_project(
        &self,
        project: &str,
    ) -> Result<Vec<(Uuid, Uuid, chrono::DateTime<chrono::Utc>)>> {
        let g = &self.graph_name;
        let agtype_json = format!(r#"{{"project": "{}"}}"#, json_esc(project));
        let stmt = format!("age_defeats_ts_proj_{}", Uuid::new_v4().simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT defeater_id::text, defeated_id::text, defeater_created_at::text \
             FROM ag_catalog.cypher('{g}', $$ \
             MATCH (a:Belief)-[:DEFEATS]->(b:Belief) \
             WHERE (a.project = $project OR a.project IS NULL) \
               AND (b.project = $project OR b.project IS NULL) \
             RETURN a.id, b.id, a.created_at \
             $$, $1) AS (defeater_id agtype, defeated_id agtype, defeater_created_at agtype)"
        );

        let client = self.client.lock().await;
        let rows = age_query_rows(&client, &stmt, &prepare, &agtype_json).await?;
        let mut triples = Vec::with_capacity(rows.len());
        for row in &rows {
            let defeater_id_raw = row
                .get("defeater_id")
                .ok_or_else(|| anyhow::anyhow!("missing column defeater_id"))?;
            let defeated_id_raw = row
                .get("defeated_id")
                .ok_or_else(|| anyhow::anyhow!("missing column defeated_id"))?;
            let created_at_raw = row
                .get("defeater_created_at")
                .ok_or_else(|| anyhow::anyhow!("missing column defeater_created_at"))?;
            let defeater_id = Uuid::parse_str(defeater_id_raw)?;
            let defeated_id = Uuid::parse_str(defeated_id_raw)?;
            let defeater_created_at =
                DateTime::parse_from_rfc3339(created_at_raw)?.with_timezone(&chrono::Utc);
            triples.push((defeater_id, defeated_id, defeater_created_at));
        }
        Ok(triples)
    }

    // -----------------------------------------------------------------------
    // Patterns
    // -----------------------------------------------------------------------

    pub async fn insert_pattern(&self, pattern: &Pattern) -> Result<()> {
        let g = &self.graph_name;
        let id = pattern.id.to_string();
        let activation_count = pattern.activation_count;
        let success_rate = pattern.success_rate.value();
        let created_at = pattern.created_at.to_rfc3339();

        let project_prop = match &pattern.project {
            Some(p) => format!(r#", "project": "{}""#, json_esc(p)),
            None => String::new(),
        };
        let project_cypher = if pattern.project.is_some() {
            ", project: $project"
        } else {
            ""
        };

        let agtype_json = format!(
            r#"{{"id": "{id}", "situation": "{}", "approach": "{}", "created_at": "{created_at}"{project_prop}}}"#,
            json_esc(&pattern.situation),
            json_esc(&pattern.approach),
        );

        let stmt = format!("age_ins_pat_{}", pattern.id.simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT * FROM ag_catalog.cypher('{g}', $$ \
             CREATE (p:Pattern {{id: $id, situation: $situation, approach: $approach, \
             activation_count: {activation_count}, success_rate: {success_rate}, \
             created_at: $created_at{project_cypher}}}) \
             RETURN p.id $$, $1) AS (id ag_catalog.agtype)"
        );

        let client = self.client.lock().await;
        age_execute(&client, &stmt, &prepare, &agtype_json).await
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
  created_at::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (p:Pattern {{id: '{id_str}'}})
  RETURN p.id, p.situation, p.approach, p.activation_count, p.success_rate, p.created_at, p.project
$$) {PATTERN_RETURN_COLUMNS}"#
        );

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
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
        let client = self.client.lock().await;
        client.query(&sql, &[]).await?;
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
  created_at::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (p:Pattern)
  RETURN p.id, p.situation, p.approach, p.activation_count, p.success_rate, p.created_at, p.project
$$) {PATTERN_RETURN_COLUMNS}"#
        );

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        let mut patterns = Vec::with_capacity(rows.len());
        for row in &rows {
            patterns.push(pattern_from_row(row)?);
        }
        Ok(patterns)
    }

    /// Like `list_patterns`, but scoped to a project (same `project =
    /// $project OR project IS NULL` semantics as `list_beliefs_by_project`).
    pub async fn list_patterns_by_project(&self, project: &str) -> Result<Vec<Pattern>> {
        let g = &self.graph_name;
        let agtype_json = format!(r#"{{"project": "{}"}}"#, json_esc(project));
        let stmt = format!("age_list_patterns_proj_{}", Uuid::new_v4().simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT \
             id::text, situation::text, approach::text, activation_count::text, \
             success_rate::text, created_at::text, project::text \
             FROM ag_catalog.cypher('{g}', $$ \
             MATCH (p:Pattern) WHERE p.project = $project OR p.project IS NULL \
             RETURN p.id, p.situation, p.approach, p.activation_count, p.success_rate, p.created_at, p.project \
             $$, $1) {PATTERN_RETURN_COLUMNS}"
        );

        let client = self.client.lock().await;
        let rows = age_query_rows(&client, &stmt, &prepare, &agtype_json).await?;
        let mut patterns = Vec::with_capacity(rows.len());
        for row in &rows {
            patterns.push(pattern_from_simple_row(row)?);
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

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
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

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
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

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        let mut pairs = Vec::with_capacity(rows.len());
        for row in &rows {
            let from_raw: &str = row.get("from_id");
            let to_raw: &str = row.get("to_id");
            pairs.push((Uuid::parse_str(from_raw)?, Uuid::parse_str(to_raw)?));
        }
        Ok(pairs)
    }

    /// Like `get_contradiction_pairs`, but scoped to a project: only pairs
    /// where both endpoints match the project (or are untagged/global) are
    /// returned, matching `list_beliefs_by_project`'s inclusion semantics.
    pub async fn get_contradiction_pairs_by_project(
        &self,
        project: &str,
    ) -> Result<Vec<(Uuid, Uuid)>> {
        let g = &self.graph_name;
        let agtype_json = format!(r#"{{"project": "{}"}}"#, json_esc(project));
        let stmt = format!("age_contra_pairs_proj_{}", Uuid::new_v4().simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT from_id::text, to_id::text \
             FROM ag_catalog.cypher('{g}', $$ \
             MATCH (a:Belief)-[:CONTRADICTS]->(b:Belief) \
             WHERE (a.project = $project OR a.project IS NULL) \
               AND (b.project = $project OR b.project IS NULL) \
             RETURN a.id, b.id \
             $$, $1) AS (from_id agtype, to_id agtype)"
        );

        let client = self.client.lock().await;
        let rows = age_query_rows(&client, &stmt, &prepare, &agtype_json).await?;
        let mut pairs = Vec::with_capacity(rows.len());
        for row in &rows {
            let from_raw = row
                .get("from_id")
                .ok_or_else(|| anyhow::anyhow!("missing column from_id"))?;
            let to_raw = row
                .get("to_id")
                .ok_or_else(|| anyhow::anyhow!("missing column to_id"))?;
            pairs.push((Uuid::parse_str(from_raw)?, Uuid::parse_str(to_raw)?));
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

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        let mut edges = Vec::with_capacity(rows.len());
        for row in &rows {
            let from_raw: &str = row.get("from_id");
            let to_raw: &str = row.get("to_id");
            let label_raw: &str = row.get("label");
            let weight_raw: &str = row.get("weight");

            let from_id = Uuid::parse_str(from_raw)?;
            let to_id = Uuid::parse_str(to_raw)?;
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

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        let mut edges = Vec::with_capacity(rows.len());
        for row in &rows {
            let from_id = Uuid::parse_str(row.get::<_, &str>("from_id"))?;
            let to_id = Uuid::parse_str(row.get::<_, &str>("to_id"))?;
            let edge_type: EdgeType = row.get::<_, &str>("label").parse()?;
            let weight: f64 = row.get::<_, &str>("weight").parse()?;
            let probability = Probability::new(weight)?;
            // Source mean from its stored (α, β); fall back to 0.5 (empty-Beta).
            let src_alpha: f64 = row
                .get::<_, Option<&str>>("src_alpha")
                .and_then(|s| s.parse().ok())
                .unwrap_or(0.0);
            let src_beta: f64 = row
                .get::<_, Option<&str>>("src_beta")
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

        // sectionPath is a JSON array of strings — valid agtype list.
        let section_path_json = {
            let inner: Vec<String> = chunk
                .section_path
                .iter()
                .map(|s| format!(r#""{}""#, json_esc(s)))
                .collect();
            format!("[{}]", inner.join(", "))
        };

        // parentId is a UUID ([0-9a-f-] only) — no JSON or SQL escaping needed.
        let parent_prop = match chunk.parent_id {
            Some(p) => format!(r#", "parentId": "{}""#, p),
            None => String::new(),
        };
        let project_prop = match &chunk.project {
            Some(p) => format!(r#", "project": "{}""#, json_esc(p)),
            None => String::new(),
        };

        let agtype_json = format!(
            r#"{{"id": "{id}", "documentPath": "{}", "sectionPath": {section_path_json}, "content": "{}"{parent_prop}{project_prop}}}"#,
            json_esc(&chunk.document_path),
            json_esc(&chunk.content),
        );

        let extra_props = format!(
            "{}{}",
            if chunk.parent_id.is_some() {
                ", parentId: $parentId"
            } else {
                ""
            },
            if chunk.project.is_some() {
                ", project: $project"
            } else {
                ""
            }
        );
        let stmt = format!("age_ins_chunk_{}", chunk.id.simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT * FROM ag_catalog.cypher('{g}', $$ \
             CREATE (c:DocumentChunk {{id: $id, documentPath: $documentPath, \
             sectionPath: $sectionPath, content: $content{extra_props}}}) \
             RETURN c.id $$, $1) AS (id ag_catalog.agtype)"
        );

        let client = self.client.lock().await;
        age_execute(&client, &stmt, &prepare, &agtype_json).await?;

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
            client.query(&edge_sql, &[]).await?;
        }
        Ok(())
    }

    /// Insert one row into public.chunk_embeddings.
    pub async fn insert_chunk_embedding(&self, chunk_id: Uuid, embedding: &[f32]) -> Result<()> {
        let vec = Vector::from(embedding.to_vec());
        let client = self.client.lock().await;
        client
            .execute(
                "INSERT INTO public.chunk_embeddings (chunk_id, embedding) \
                 VALUES ($1, $2) \
                 ON CONFLICT (chunk_id) DO UPDATE SET embedding = EXCLUDED.embedding",
                &[&chunk_id, &vec],
            )
            .await?;
        Ok(())
    }

    /// Return chunk IDs for a given document path (used by clear_document).
    pub async fn get_chunk_ids_for_document(&self, path: &str) -> Result<Vec<Uuid>> {
        let g = &self.graph_name;
        let agtype_json = format!(r#"{{"documentPath": "{}"}}"#, json_esc(path));
        let stmt = format!("age_chunk_ids_by_path_{}", Uuid::new_v4().simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT id::text \
             FROM ag_catalog.cypher('{g}', $$ \
             MATCH (c:DocumentChunk) WHERE c.documentPath = $documentPath RETURN c.id \
             $$, $1) AS (id agtype)"
        );
        let exec = format!("EXECUTE {stmt}('{}')", sql_esc(&agtype_json));
        let client = self.client.lock().await;
        client.simple_query(&prepare).await?;
        let msgs = client.simple_query(&exec).await;
        let _ = client.simple_query(&format!("DEALLOCATE {stmt}")).await;
        msgs?
            .iter()
            .filter_map(|m| {
                if let tokio_postgres::SimpleQueryMessage::Row(row) = m {
                    row.get(0).and_then(|s| Uuid::parse_str(s).ok())
                } else {
                    None
                }
            })
            .map(Ok)
            .collect()
    }

    /// Return chunk IDs tagged with a project (used by delete_project extension).
    pub async fn get_chunk_ids_by_project(&self, project: &str) -> Result<Vec<Uuid>> {
        let g = &self.graph_name;
        let agtype_json = format!(r#"{{"project": "{}"}}"#, json_esc(project));
        let stmt = format!("age_chunk_ids_by_proj_{}", Uuid::new_v4().simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT id::text \
             FROM ag_catalog.cypher('{g}', $$ \
             MATCH (c:DocumentChunk) WHERE c.project = $project RETURN c.id \
             $$, $1) AS (id agtype)"
        );
        let exec = format!("EXECUTE {stmt}('{}')", sql_esc(&agtype_json));
        let client = self.client.lock().await;
        client.simple_query(&prepare).await?;
        let msgs = client.simple_query(&exec).await;
        let _ = client.simple_query(&format!("DEALLOCATE {stmt}")).await;
        msgs?
            .iter()
            .filter_map(|m| {
                if let tokio_postgres::SimpleQueryMessage::Row(row) = m {
                    row.get(0).and_then(|s| Uuid::parse_str(s).ok())
                } else {
                    None
                }
            })
            .map(Ok)
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
        let client = self.client.lock().await;
        client.query(&sql, &[]).await?;
        Ok(())
    }

    /// Delete embedding rows for the given chunk IDs.
    pub async fn delete_chunk_embeddings(&self, ids: &[Uuid]) -> Result<()> {
        if ids.is_empty() {
            return Ok(());
        }
        let client = self.client.lock().await;
        client
            .execute(
                "DELETE FROM public.chunk_embeddings WHERE chunk_id = ANY($1)",
                &[&ids],
            )
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
        let vec = Vector::from(query_vec.to_vec());
        let limit_clause = if limit > 0 {
            format!("LIMIT {limit}")
        } else {
            String::new()
        };

        let client = self.client.lock().await;
        let rows = match filter_ids {
            None => {
                let sql = format!(
                    "SELECT chunk_id::text FROM public.chunk_embeddings \
                     ORDER BY embedding <=> $1 {limit_clause}"
                );
                client.query(&sql, &[&vec]).await?
            }
            Some(ids) => {
                let sql = format!(
                    "SELECT chunk_id::text FROM public.chunk_embeddings \
                     WHERE chunk_id = ANY($2) \
                     ORDER BY embedding <=> $1 {limit_clause}"
                );
                client.query(&sql, &[&vec, &ids]).await?
            }
        };
        rows.iter()
            .map(|r| Ok(Uuid::parse_str(r.get::<_, &str>("chunk_id"))?))
            .collect()
    }

    // -----------------------------------------------------------------------
    // Belief embeddings (vector half of hybrid query_relevant)
    // -----------------------------------------------------------------------

    /// Insert or replace the embedding for a belief.
    pub async fn insert_belief_embedding(&self, belief_id: Uuid, embedding: &[f32]) -> Result<()> {
        let vec = Vector::from(embedding.to_vec());
        let client = self.client.lock().await;
        client
            .execute(
                "INSERT INTO public.belief_embeddings (belief_id, embedding) \
                 VALUES ($1, $2) \
                 ON CONFLICT (belief_id) DO UPDATE SET embedding = EXCLUDED.embedding",
                &[&belief_id, &vec],
            )
            .await?;
        Ok(())
    }

    /// Delete embedding rows for the given belief IDs. No-op if `ids` is empty.
    pub async fn delete_belief_embeddings(&self, ids: &[Uuid]) -> Result<()> {
        if ids.is_empty() {
            return Ok(());
        }
        let client = self.client.lock().await;
        client
            .execute(
                "DELETE FROM public.belief_embeddings WHERE belief_id = ANY($1)",
                &[&ids],
            )
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
        let vec = Vector::from(query_vec.to_vec());
        let limit_clause = if limit > 0 {
            format!("LIMIT {limit}")
        } else {
            String::new()
        };
        let sql = format!(
            "SELECT belief_id::text FROM public.belief_embeddings \
             ORDER BY embedding <=> $1 {limit_clause}"
        );
        let client = self.client.lock().await;
        let rows = client.query(&sql, &[&vec]).await?;
        rows.iter()
            .map(|r| Ok(Uuid::parse_str(r.get::<_, &str>("belief_id"))?))
            .collect()
    }

    /// Like `query_beliefs_by_vector`, but restricted to `filter_ids`: the
    /// cosine ranking runs only over that id set, so a project-scoped caller's
    /// top-K window can't be crowded out by other projects' embeddings (which
    /// `belief_id = ANY($2)` in `query_beliefs_by_vector` alone cannot do,
    /// since there is no `project` column on `belief_embeddings`).
    pub async fn query_beliefs_by_vector_filtered(
        &self,
        query_vec: &[f32],
        limit: usize,
        filter_ids: &[Uuid],
    ) -> Result<Vec<Uuid>> {
        if filter_ids.is_empty() {
            return Ok(Vec::new());
        }
        let vec = Vector::from(query_vec.to_vec());
        let limit_clause = if limit > 0 {
            format!("LIMIT {limit}")
        } else {
            String::new()
        };
        let sql = format!(
            "SELECT belief_id::text FROM public.belief_embeddings \
             WHERE belief_id = ANY($2) \
             ORDER BY embedding <=> $1 {limit_clause}"
        );
        let client = self.client.lock().await;
        let rows = client.query(&sql, &[&vec, &filter_ids]).await?;
        rows.iter()
            .map(|r| Ok(Uuid::parse_str(r.get::<_, &str>("belief_id"))?))
            .collect()
    }

    /// Cosine nearest-neighbour search over chunk_embeddings, returning (chunk_id, similarity).
    /// similarity = 1.0 - cosine_distance. Results ordered by similarity descending.
    /// limit=0 means no limit. Used by auto-grounding in insert_belief.
    pub async fn query_chunks_by_vector_scored(
        &self,
        query_vec: &[f32],
        limit: usize,
        filter_ids: Option<&[Uuid]>,
    ) -> Result<Vec<(Uuid, f64)>> {
        let vec = Vector::from(query_vec.to_vec());
        let limit_clause = if limit > 0 {
            format!("LIMIT {limit}")
        } else {
            String::new()
        };
        let client = self.client.lock().await;
        let rows = match filter_ids {
            None => {
                let sql = format!(
                    "SELECT chunk_id::text, 1.0 - (embedding <=> $1) AS similarity \
                     FROM public.chunk_embeddings \
                     ORDER BY embedding <=> $1 {limit_clause}"
                );
                client.query(&sql, &[&vec]).await?
            }
            Some(ids) => {
                let sql = format!(
                    "SELECT chunk_id::text, 1.0 - (embedding <=> $1) AS similarity \
                     FROM public.chunk_embeddings \
                     WHERE chunk_id = ANY($2) \
                     ORDER BY embedding <=> $1 {limit_clause}"
                );
                client.query(&sql, &[&vec, &ids]).await?
            }
        };
        rows.iter()
            .map(|r| {
                let id = Uuid::parse_str(r.get::<_, &str>("chunk_id"))?;
                let sim: f64 = r.get("similarity");
                Ok((id, sim))
            })
            .collect()
    }

    /// Cosine nearest-neighbour search over belief_embeddings, returning (belief_id, similarity).
    /// similarity = 1.0 - cosine_distance. Results ordered by similarity descending.
    /// limit=0 means no limit. Used by auto-grounding in load_document.
    pub async fn query_beliefs_by_vector_scored(
        &self,
        query_vec: &[f32],
        limit: usize,
    ) -> Result<Vec<(Uuid, f64)>> {
        let vec = Vector::from(query_vec.to_vec());
        let limit_clause = if limit > 0 {
            format!("LIMIT {limit}")
        } else {
            String::new()
        };
        let sql = format!(
            "SELECT belief_id::text, 1.0 - (embedding <=> $1) AS similarity \
             FROM public.belief_embeddings \
             ORDER BY embedding <=> $1 {limit_clause}"
        );
        let client = self.client.lock().await;
        let rows = client.query(&sql, &[&vec]).await?;
        rows.iter()
            .map(|r| {
                let id = Uuid::parse_str(r.get::<_, &str>("belief_id"))?;
                let sim: f64 = r.get("similarity");
                Ok((id, sim))
            })
            .collect()
    }

    /// Belief IDs that already have an embedding row (used by `reembed` to skip).
    pub async fn list_embedded_belief_ids(&self) -> Result<Vec<Uuid>> {
        let client = self.client.lock().await;
        let rows = client
            .query("SELECT belief_id::text FROM public.belief_embeddings", &[])
            .await?;
        rows.iter()
            .map(|r| Ok(Uuid::parse_str(r.get::<_, &str>("belief_id"))?))
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
        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
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
  created_at::text, last_activated_at::text, memory_type::text, project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (n:Belief {{id: '{b}'}})
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta,
         n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let mut client = self.client.lock().await;
        let tx = client.transaction().await?;

        // Step 1: create the GROUNDS edge (errors if endpoints missing).
        let rows = tx.query(&create_sql, &[]).await?;
        if rows.is_empty() {
            bail!(
                "insert_evidence: chunk or belief not found (chunk={}, belief={})",
                c,
                b
            );
        }

        // Step 2: read current (α, β) inside the same transaction.
        let rows = tx.query(&get_sql, &[]).await?;
        let belief = rows
            .first()
            .map(belief_from_row)
            .transpose()?
            .ok_or_else(|| anyhow::anyhow!("insert_evidence: belief {} vanished", b))?;

        // Step 3: compute new α and derive cached scalars; write back atomically.
        let new_alpha = belief.alpha + EVIDENCE_MASS_K * w;
        let update_sql = self.update_belief_beta_sql(belief_id, new_alpha, belief.beta)?;
        let rows = tx.query(&update_sql, &[]).await?;
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
        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        let mut out = HashMap::with_capacity(rows.len());
        for row in &rows {
            let id = Uuid::parse_str(row.get::<_, &str>("belief_id"))?;
            let total: f64 = row.get::<_, &str>("total_weight").parse()?;
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
        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        let mut out = Vec::with_capacity(rows.len());
        for row in &rows {
            let belief_id = Uuid::parse_str(row.get::<_, &str>("belief_id"))?;
            let chunk_id = Uuid::parse_str(row.get::<_, &str>("chunk_id"))?;
            let weight: f64 = row.get::<_, &str>("weight").parse()?;
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
        let client = self.client.lock().await;
        client.execute(&sql, &[]).await?;
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
  memory_type::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (s:Belief {{id: '{id_str}'}})-[:SUPPORTS*1..]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project
  UNION
  MATCH (s:Belief {{id: '{id_str}'}})-[:CAUSES*1..]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project
  UNION
  MATCH (s:Belief {{id: '{id_str}'}})-[:DEFEATS*1..]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        let mut beliefs = Vec::with_capacity(rows.len());
        for row in &rows {
            beliefs.push(belief_from_row(row)?);
        }
        Ok(beliefs)
    }

    /// Direct (1-hop) SUPPORTS/CAUSES/DEFEATS successors of `start_id`, scoped
    /// to `project` (matches `project = $project OR project IS NULL`, same
    /// semantics as `list_beliefs_by_project`).
    ///
    /// This exists so a project-scoped caller can walk the transitive closure
    /// hop-by-hop in application code, stopping the frontier at any node
    /// outside scope — a scoped node reached only via an out-of-scope
    /// intermediate is correctly excluded, unlike filtering
    /// `get_downstream_beliefs`'s unbounded closure by endpoint alone (which
    /// admits a node whose only path back into scope bridges through an
    /// out-of-scope node). AGE 1.x cannot express this as one query: it has no
    /// `[:A|B|C]` relationship-type OR syntax (three MATCH clauses UNION'd,
    /// same as `get_downstream_beliefs`) and, verified directly against the
    /// live server, no `all(x IN list WHERE ...)` list-predicate support
    /// either (`ERROR: syntax error at or near "("`), so per-hop-node
    /// filtering cannot be inlined into a single variable-length-path query.
    pub async fn get_direct_downstream_by_project(
        &self,
        start_id: Uuid,
        project: &str,
    ) -> Result<Vec<Belief>> {
        let g = &self.graph_name;
        let id_str = start_id.to_string();
        let agtype_json = format!(r#"{{"project": "{}"}}"#, json_esc(project));
        let stmt = format!("age_direct_downstream_proj_{}", Uuid::new_v4().simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT \
             id::text, content::text, probability::text, confidence::text, \
             alpha::text, beta::text, alpha0::text, beta0::text, \
             created_at::text, last_activated_at::text, memory_type::text, project::text \
             FROM ag_catalog.cypher('{g}', $$ \
             MATCH (s:Belief {{id: '{id_str}'}})-[:SUPPORTS]->(n:Belief) \
             WHERE n.project = $project OR n.project IS NULL \
             RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project \
             UNION \
             MATCH (s:Belief {{id: '{id_str}'}})-[:CAUSES]->(n:Belief) \
             WHERE n.project = $project OR n.project IS NULL \
             RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project \
             UNION \
             MATCH (s:Belief {{id: '{id_str}'}})-[:DEFEATS]->(n:Belief) \
             WHERE n.project = $project OR n.project IS NULL \
             RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project \
             $$, $1) {BELIEF_RETURN_COLUMNS}"
        );

        let client = self.client.lock().await;
        let rows = age_query_rows(&client, &stmt, &prepare, &agtype_json).await?;
        let mut beliefs = Vec::with_capacity(rows.len());
        for row in &rows {
            beliefs.push(belief_from_simple_row(row)?);
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
  memory_type::text,
  project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (s:Belief {{id: '{id_str}'}})-[:CAUSES*1..10]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.alpha, n.beta, n.alpha0, n.beta0, n.created_at, n.last_activated_at, n.memory_type, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
        );

        let client = self.client.lock().await;
        let rows = client.query(&sql, &[]).await?;
        let mut beliefs = Vec::with_capacity(rows.len());
        for row in &rows {
            beliefs.push(belief_from_row(row)?);
        }
        Ok(beliefs)
    }
}

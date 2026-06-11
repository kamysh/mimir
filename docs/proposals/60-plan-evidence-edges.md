# Phase 4 — Document-grounded beliefs (evidence edges)

## Why

Today documents are a parallel island: `DocumentChunk` nodes connect only to each
other (`CONTAINS`), beliefs connect only to each other (`SUPPORTS`/`DEFEATS`/
`CAUSES`/`CONTRADICTS`), and the two stores meet only through a shared `project`
string. Retrieval is split in half — `query_relevant` over beliefs, `query_document`
over chunks — and they never inform one another.

This phase makes a document chunk a first-class **evidence node** for a belief, so
documents become part of reasoning instead of a lookup beside it. Two layers:

- **C-core** (ship now, self-contained): attach chunks to beliefs and surface the
  grounding passage when a belief is retrieved. Pure provenance + retrieval.
- **C-coupling** (gated on Phase 3 Beta): let grounding contribute *principled*
  evidence mass to a belief's confidence, so a fact someone wrote down with a
  source doesn't decay like a hunch.

**Hard invariant for both layers:** the evidence overlay must not perturb belief↔
belief inference. A document chunk has no probability/confidence; if it leaked into
propagation it would corrupt every downstream belief. C is designed so it provably
cannot.

## What makes this safe — verified against the current code

- `get_downstream_beliefs` traverses strictly `MATCH (s:Belief)-[:SUPPORTS*1..10]->
  (n:Belief)` UNION the `CAUSES` variant — rooted at `:Belief`, label list is
  `SUPPORTS`/`CAUSES` only, every hop is `:Belief`.
- `get_edges_among` matches `(a:Belief)-[r]->(b:Belief)` — accepts any relationship
  type, but **both endpoints must be `:Belief`**.
- `delete_belief` and `delete_document_chunks` both `DETACH DELETE`; `delete_project`
  clears beliefs and chunks together.
- `query_relevant` returns `Vec<Belief>` and the assembly ends at a single
  `Ok(matched)` after sort+truncate — a clean enrichment hook.

A new edge that **originates at a `DocumentChunk`** and is **labelled `GROUNDS`**
(∉ the SUPPORTS/CAUSES traversal lists) therefore cannot be matched by any belief
traversal, and is auto-removed when either endpoint is deleted. Non-interference is
structural.

## The edge

`(c:DocumentChunk)-[:GROUNDS {weight}]->(b:Belief)`, `weight ∈ [0,1]` = grounding
strength, many-to-many. It is deliberately **not** a belief edge: not added to
`EdgeType`, not referenced by any propagation or expansion query. Do **not** reuse
`SUPPORTS`/`CAUSES` for chunk→belief — that is exactly the failure mode this design
avoids.

---

## C-core — attach + provenance retrieval

### Migration `004_evidence_edges.sql` (idempotent)

```sql
-- Evidence edge: a DocumentChunk grounds a Belief. Excluded from all inference.
DO $$ BEGIN
  PERFORM ag_catalog.create_elabel(current_database()::text, 'GROUNDS');
EXCEPTION WHEN others THEN NULL; END $$;
```

No table or backfill; existing data is untouched.

### Store layer (`store.rs`) — mirror the `insert_edge` pattern

```rust
/// Create a GROUNDS edge from a DocumentChunk to a Belief.
pub async fn insert_evidence(&self, chunk_id: Uuid, belief_id: Uuid, weight: Probability) -> Result<()> {
    let g = &self.graph_name;
    let (c, b, w) = (chunk_id.to_string(), belief_id.to_string(), weight.value());
    let sql = format!(
        r#"SELECT * FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk {{id: '{c}'}}), (b:Belief {{id: '{b}'}})
  CREATE (c)-[r:GROUNDS {{weight: {w}}}]->(b)
  RETURN r.weight
$$) AS (weight ag_catalog.agtype)"#
    );
    let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
    if rows.is_empty() {
        bail!("insert_evidence: chunk or belief not found (chunk={c}, belief={b})");
    }
    Ok(())
}

/// For a set of beliefs, return their grounding (belief_id, chunk_id, weight).
pub async fn get_evidence_for_beliefs(&self, belief_ids: &[Uuid]) -> Result<Vec<(Uuid, Uuid, f64)>> {
    if belief_ids.is_empty() { return Ok(vec![]); }
    let g = &self.graph_name;
    let id_list = belief_ids.iter().map(|i| format!("'{i}'")).collect::<Vec<_>>().join(", ");
    let sql = format!(
        r#"SELECT belief_id::text, chunk_id::text, weight::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (c:DocumentChunk)-[r:GROUNDS]->(b:Belief)
  WHERE b.id IN [{id_list}]
  RETURN b.id, c.id, r.weight
$$) AS (belief_id ag_catalog.agtype, chunk_id ag_catalog.agtype, weight ag_catalog.agtype)"#
    );
    // parse rows -> (Uuid, Uuid, f64)  (same decode shape as get_edges_among)
    // ...
}
```

`delete_evidence(chunk_id, belief_id)` for explicit unlink; otherwise GC is
automatic (DETACH DELETE on either endpoint). A reverse
`get_beliefs_grounded_by(chunk_ids)` is optional, for "what does this passage
support."

### Service layer (`lib.rs`)

```rust
pub struct EvidenceRef {
    pub chunk_id: Uuid,
    pub document_path: String,
    pub section_path: Vec<String>,
    pub snippet: String,   // chunk content, trimmed
    pub weight: f64,
}
pub struct GroundedBelief { pub belief: Belief, pub evidence: Vec<EvidenceRef> }

pub async fn add_evidence(&self, belief_id: Uuid, chunk_id: Uuid, weight: f64) -> Result<()> {
    self.store.insert_evidence(chunk_id, belief_id, Probability::new(weight)?).await
}

/// query_relevant, plus the top-k grounding passages per belief. query_relevant
/// itself is unchanged (backward compatible); this is purely additive.
pub async fn query_relevant_grounded(
    &self, query: &str, limit: usize, evidence_per_belief: usize,
) -> Result<Vec<GroundedBelief>> {
    let beliefs = self.query_relevant(query, limit).await?;
    let ids: Vec<Uuid> = beliefs.iter().map(|b| b.id).collect();
    let ev = self.store.get_evidence_for_beliefs(&ids).await?;
    // group ev by belief_id, fetch chunk content/section, sort by weight desc,
    // truncate to evidence_per_belief, assemble GroundedBelief { belief, evidence }.
    // ...
}
```

### MCP / CLI surface

- MCP: `add_evidence {chunk_id, belief_id, weight?}`; `query_relevant` gains
  `include_evidence: bool` + `evidence_per_belief: int` (result carries an
  `evidence[]` array per belief); `get_evidence {belief_id}`.
- CLI: `mimir evidence add <chunk_id> <belief_id> [--weight 0.8]`;
  `mimir query "<text>" --evidence`; `mimir evidence list <belief_id>`.
- **Linking workflow:** `load_document` → `query_document` already returns chunk
  IDs (`DocumentChunkResult.id`) → `add_evidence(chunk_id, belief_id)`. No new way
  to obtain IDs is needed.

### Skill update (`10-mimir-SKILL.md`)

The comply-or-override rule gets teeth: override a `p≥0.8` belief only after reading
its grounding passage, and cite the passage when acting on the belief. Retrieval now
hands the agent the belief *and* its source in one call.

---

## Non-interference — the guarantee

**Theorem (operational).** For any graph `G` and any overlay `E` consisting of
`GROUNDS` edges and `DocumentChunk` nodes, `get_downstream_beliefs`,
`get_edges_among`, and hence every `propagate_*` result are identical on `G` and
`G ∪ E`.

*Proof.* `get_downstream_beliefs` is rooted at `:Belief` and restricted to
`:SUPPORTS`/`:CAUSES`; `get_edges_among` requires both endpoints `:Belief`. Every
edge in `E` originates at a `:DocumentChunk` and carries label `GROUNDS ∉
{SUPPORTS, CAUSES, DEFEATS, CONTRADICTS}`. So no element of `E` is matched by either
query, the seed/edge sets fed to `InferenceEngine` are unchanged, and propagation
(a pure function of those sets) yields identical output. ∎

**Agda — `spec/Mimir/Evidence.agda`.** Model belief inference as a function of the
belief-edge multiset only, and an evidence overlay as a disjoint set:

```agda
-- propagate depends only on edges whose label ∈ inferenceLabels
-- GROUNDS ∉ inferenceLabels (by construction)
propagate-evidence-invariant :
  ∀ (g : Graph) (e : EvidenceOverlay) → propagate g ≡ propagate (g ⊎ overlayEdges e)
```

This is the formal counterpart of the theorem and the thing that makes C safe to
ship: the existing `Mimir.Inference` proofs are preserved verbatim.

---

## C-coupling — documents inform belief state (after Phase 3 Beta)

This is the "documents are part of thinking" payoff, done principledly. Under the
Phase-3 `Beta(α, β)` belief model:

- A `GROUNDS` edge of weight `w` is a **pseudo-observation**. `add_evidence` bumps
  `α += k·w` (k = evidence-mass constant), raising both the mean and the strength
  `α+β` — i.e. confidence rises because there is *evidence*, not because of
  heuristic spreading.
- Decay-toward-prior is resisted in proportion to total grounding mass `Σ k·wᵢ`:
  grounded beliefs hold confidence and decay slower than ungrounded ones.

**Do not** bolt this onto the current scalar `confidence` field — that value is a
heuristic, and coupling evidence into it would be unprincipled. Confidence coupling
belongs on the Beta posterior, where a pseudo-observation is an actual update. Hence
the explicit dependency on Phase 3. (Orthogonally, it composes with the Phase-1
do-operator: an intervention query can prefer grounded beliefs.)

---

## Eval-harness threading

- Tasks gain `docs/*.md` and a `belief.json` `evidence` mapping (the section/snippet
  that grounds the belief).
- Seeding: `load_document(doc, project=eval-<task>)`, then `add_evidence(matching
  chunk, belief, w)`.
- New arm **`grounded`** = `query_relevant_grounded` (belief + passage), compared
  against `belief` (bare belief), `doc` (raw `query_document`), `static`, `control`.
- Hypothesis: does belief+grounding beat a bare belief, and does the passage **reduce
  wrong overrides** (the agent can check the source before discarding the belief)?
- **The decisive C task — "stale belief vs fresh contradicting document":** seed a
  now-wrong belief *and* a fresh document that corrects it, grounded to that belief.
  Measure whether the `grounded` arm lets the agent correctly override the stale
  belief. This is precisely the case bare-belief and static cannot handle, and it
  is the cleanest demonstration that documents are participating in reasoning.

---

## Acceptance criteria

- `add_evidence` creates a `GROUNDS` edge; `query_relevant_grounded` returns each
  belief with its top-k passages.
- **Regression (the load-bearing one):** seed `GROUNDS` edges + `DocumentChunk`
  nodes over an existing graph and assert `propagate_from` output is bit-identical
  to the no-evidence baseline — the executable form of the non-interference theorem.
- `delete_belief` / `delete_project` leave no dangling `GROUNDS` edges.
- `spec/Mimir/Evidence.agda` type-checks.

## Sequencing

C-core is independent and shippable now; its isolation test and the Agda lemma are
part of it. C-coupling waits on Phase 3 Beta. Suggested order: **C-core now** — it
delivers provenance and the harness `grounded` arm, which lets you *measure* whether
grounding helps before investing in confidence coupling — then Phase 3, then
C-coupling.

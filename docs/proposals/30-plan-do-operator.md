# Phase 1 — the do-operator: give `CAUSES` real semantics

**Goal.** Add an interventional query `P(· | do(target = value))` that finally
makes `CAUSES` mean something `SUPPORTS` doesn't. Today `EdgeType::Causes` is
handled by the identical arm as `Supports` in `inference.rs`
(`EdgeType::Supports | EdgeType::Causes => boost`), so the edge type is
decorative. This phase is small, self-contained, and the highest-leverage change
relative to the project's stated intent.

**Principle (Pearl).** `do(X = x)` is graph surgery: **delete the edges into X,
clamp X to x, and propagate forward along causal edges only.** The contrast that
makes it worth having:

- *Observational* (`query_relevant`, `propagate_from`) expands along
  **SUPPORTS ∪ CAUSES** — evidential association.
- *Interventional* (`query_intervention`, new) severs the target's parents and
  follows **CAUSES only** — the evidential/correlational paths through non-causal
  edges are exactly what an intervention must cut.

**Critical design decision: intervention is a read-only query, not a mutation.**
`propagate_from` writes updated probabilities back to the store. `query_intervention`
must **not** — a counterfactual is a hypothetical projection, and persisting the
surgery would corrupt the graph. It computes and returns; it never calls
`update_belief_probability`.

---

## Changes, file by file

### 1. `crates/core/src/inference.rs`

The existing `propagate_defeat(&self, seed, downstream, edges)` uses only
`seed.id` and `seed.probability`. Refactor its body into a private core that both
the existing function and the new `intervene` share, so the BFS logic lives in
one place (and so Phase 2 upgrades both at once).

```rust
/// Shared propagation core. `seed_id`/`seed_prob` is the changed node; `edges`
/// is the edge set to follow (already filtered by the caller). Pure; no writeback.
fn propagate_core(
    &self,
    seed_id: Uuid,
    seed_prob: Probability,
    downstream: &[Belief],
    edges: &[(Uuid, Uuid, EdgeType, Probability)],
) -> Result<Vec<(Uuid, Probability)>> {
    // ... body of the current propagate_defeat, using seed_id/seed_prob ...
}

pub fn propagate_defeat(
    &self,
    seed: &Belief,
    downstream: &[Belief],
    edges: &[(Uuid, Uuid, EdgeType, Probability)],
) -> Result<Vec<(Uuid, Probability)>> {
    self.propagate_core(seed.id, seed.probability, downstream, edges)
}

/// P(· | do(target = value)). Graph surgery: drop every edge INTO `target_id`,
/// keep only CAUSES edges, clamp target to `value`, propagate forward.
/// Pure and read-only — returns projected downstream probabilities; writes nothing.
pub fn intervene(
    &self,
    target_id: Uuid,
    value: Probability,
    downstream: &[Belief],
    edges: &[(Uuid, Uuid, EdgeType, Probability)],
) -> Result<Vec<(Uuid, Probability)>> {
    let surgical: Vec<(Uuid, Uuid, EdgeType, Probability)> = edges
        .iter()
        .copied()
        .filter(|&(_from, to, et, _w)| to != target_id && et == EdgeType::Causes)
        .collect();
    self.propagate_core(target_id, value, downstream, &surgical)
}
```

That's the whole engine change — `intervene` is the surgery filter plus a reuse
of the core. Note `EdgeType` already derives `PartialEq, Eq` (`graph.rs`), so the
`et == EdgeType::Causes` compare is free.

### 2. `crates/core/src/store.rs`

Add a causal-only descendants query, mirroring `get_downstream_beliefs` (which
UNIONs `SUPPORTS*1..10` and `CAUSES*1..10`) but keeping just the causal branch:

```rust
/// Beliefs reachable from `start_id` along CAUSES edges only (the causal
/// descendants — the candidate set for an intervention).
pub async fn get_causal_downstream_beliefs(&self, start_id: Uuid) -> Result<Vec<Belief>> {
    let g = &self.graph_name;
    let id_str = start_id.to_string();
    let sql = format!(
        r#"SELECT
  id::text, content::text, probability::text, confidence::text,
  created_at::text, last_activated_at::text, project::text
FROM ag_catalog.cypher('{g}', $$
  MATCH (s:Belief {{id: '{id_str}'}})-[:CAUSES*1..10]->(n:Belief)
  RETURN n.id, n.content, n.probability, n.confidence, n.created_at, n.last_activated_at, n.project
$$) {BELIEF_RETURN_COLUMNS}"#
    );
    let rows = sqlx::query(&sql).fetch_all(&self.pool).await?;
    rows.iter().map(belief_from_row).collect()
}
```

Reuse the existing `get_edges_among(&ids)` for the edge set — it returns all edge
types among the id set; `intervene` filters to `CAUSES`.

*(Acceptable shortcut if you want to skip the new store method for v1: reuse
`get_downstream_beliefs`. Since `intervene` follows only CAUSES edges, non-causal
descendants simply never update. It over-fetches but is correct. Prefer the
dedicated method.)*

### 3. `crates/core/src/lib.rs` (`MimirService`)

Add the read-only orchestration, parallel to `propagate_from` but **without the
writeback loop**:

```rust
/// Counterfactual projection P(· | do(target = value)). Read-only: computes and
/// returns projected probabilities for the causal descendants of `target`; does
/// NOT write to the store. Contrast `propagate_from`, which mutates.
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
    let edges = self.store.get_edges_among(&ids).await?;
    // No writeback — this is a hypothetical.
    self.inference.intervene(target_id, value, &downstream, &edges)
}
```

### 4. `crates/mcp/src/main.rs`

Two edits, both mirroring `propagate_from`.

Tool definition in `tools_list()` (after the `propagate_from` entry, ~line 200):

```json
{
    "name": "query_intervention",
    "description": "Counterfactual query P(downstream | do(target = value)). Severs the target's incoming edges and propagates along CAUSES edges only. READ-ONLY: returns projected probabilities for causal descendants; does NOT modify the graph. Use for 'if I change X, what downstream is affected?' — distinct from query_relevant (evidential association) and propagate_from (which mutates).",
    "inputSchema": {
        "type": "object",
        "properties": {
            "id":    { "type": "string" },
            "value": { "type": "number", "minimum": 0.0, "maximum": 1.0 }
        },
        "required": ["id", "value"]
    }
},
```

Handler arm in `handle_tool_call` (mirror the `propagate_from` arm, ~line 412):

```rust
"query_intervention" => {
    let id_str = args["id"].as_str()
        .ok_or_else(|| anyhow::anyhow!("missing 'id'"))?;
    let value = args["value"].as_f64()
        .ok_or_else(|| anyhow::anyhow!("missing 'value'"))?;
    let id = uuid::Uuid::parse_str(id_str)?;
    let updates = svc.query_intervention(id, value).await?;
    let result: Vec<Value> = updates.into_iter()
        .map(|(uid, prob)| json!({ "id": uid.to_string(), "projected_probability": prob.value() }))
        .collect();
    Ok(json!(result))
}
```

Note the result key is `projected_probability`, not `new_probability` — it signals
"hypothetical", reinforcing that nothing was written.

### 5. `crates/cli/src/main.rs` (optional, recommended)

Add a `mimir intervene <UUID> <VALUE>` subcommand mirroring `cmd_query`'s output
shape, calling `svc.query_intervention(id, value)`. Useful for manual testing and
for a future hook. Keep the human format consistent: `<id>  p_proj=<v>  <content>`.

### 6. `spec/Mimir/Inference.agda`

The current spec proves per-edge monotonicity. Add the interventional semantics
and the structural theorem that gives the do-operator its meaning:

- Define `surgical : Edges → BeliefId → Edges` keeping only `CAUSES` edges whose
  target ≠ the intervened node.
- State and prove **`intervene-ignores-parents`**: for any edge set `E` and target
  `t`, no edge of `surgical E t` points into `t` — i.e. the intervened node's
  value is independent of its former parents. This is the formal content of
  graph mutilation and is a straightforward filter-membership lemma.
- (If Phase 2 lands first, also restate the result on the log-odds core.)

---

## Tests (`crates/core/src/inference.rs` `#[cfg(test)]` + integration)

1. **Surgery ignores incoming edges to target.** Graph `A -CAUSES-> T -CAUSES-> B`.
   `intervene(T, 1.0, …)` updates `B` and is unaffected by `A`'s probability or
   the `A→T` edge (vary `A`, assert `B`'s projection is identical).
2. **Only CAUSES is followed.** Graph `T -SUPPORTS-> B`. `intervene(T, v, …)`
   leaves `B` unchanged (empty/no-op), because the surgical set drops SUPPORTS.
3. **Observational ≠ interventional on a confounder.** Classic fork
   `C -CAUSES-> T`, `C -CAUSES-> B` (so T and B are associated via C but T does
   not cause B). `propagate_from(T)` (follows CAUSES from T) does not reach B —
   good — but the *evidential* `query_relevant` expansion would surface B as
   related; assert `query_intervention(T, v)` returns no change to B, encoding
   "forcing T tells you nothing about B." Document this as the canonical example.
4. **Read-only.** After `query_intervention`, re-read all beliefs from the store
   and assert no probability changed (integration test against a live AGE graph).
5. **Validation.** `value` outside [0,1] → error; unknown `target_id` → error.

---

## Edge cases / known limitations (call out, don't fix here)

- **Cycles in the causal subgraph.** `propagate_core` is still the existing
  single-pass BFS, so a causal cycle gives an order-dependent result. Acceptable
  for Phase 1; Phase 2 (log-odds fixpoint) fixes it for both functions at once.
  Note it in a code comment rather than working around it.
- **No confounder adjustment.** This implements the *structural* do-operator
  (mutilation + forward propagation), not back-door/front-door adjustment over a
  joint distribution. That's correct for this graph model (beliefs carry marginal
  probabilities, not a joint), and is the honest scope. Don't claim more.

---

## Acceptance criteria (definition of done)

- `cargo build` and `cargo test -p mimir-core` green, including the 5 new tests.
- `query_intervention` exists end-to-end: `MimirService` method → MCP tool listed
  in `tools/list` → handler returns `projected_probability` results.
- An integration test proves **no writeback** occurs.
- `EdgeType::Causes` now has behavior distinct from `Supports` (test #2 fails if
  someone collapses them again).
- `Inference.agda` type-checks with the `intervene-ignores-parents` lemma proved
  (`{-# OPTIONS --safe #-}` retained).
- README "MCP tools" table gains a `query_intervention` row.

If any criterion can't be met, stop and report rather than working around it.

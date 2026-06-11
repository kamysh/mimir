# Phase 2 — propagation that's actually well-defined

**The bug.** `InferenceEngine::propagate_defeat` is a single-pass BFS that
enqueues each node once but mutates `belief_map[to_id]` every time an incoming
edge is processed. So for any node with **multiple parents or on a re-convergent
path**, the result depends on BFS visitation order, and contributions
double-count. The Agda spec proves each *edge step* is monotone and then claims
"correctness of the full BFS follows by induction over the downstream list" —
but per-edge monotonicity does not give a well-defined global result. Order-
independence and convergence are neither proved nor true for the current code.

**The fix (recommended — Option A).** Stop mutating per-edge in traversal order.
Instead, **snapshot** every node's probability at pass start, **aggregate all of
a node's incoming edges in one shot**, and **iterate to a fixpoint**. This:

- removes order-dependence and double-counting (the aggregation is a product, so
  it commutes);
- **is backward-compatible on every currently-tested case** — for a node with
  exactly one incoming edge it reduces to today's `attenuate`/`boost` formulas
  (verified below), so existing unit tests pass unchanged;
- converges on cycles (which the current code handles arbitrarily).

Because Phase 1 routed both `propagate_defeat` and `intervene` through a shared
`propagate_core`, this single rewrite upgrades observational propagation **and**
the do-operator at once.

> A note on scope and honesty: this phase fixes the **aggregation** defect. It
> does *not* resolve the deeper "is a stored probability a prior or a posterior?"
> ambiguity — recomputing from stored values still treats them as the base. That
> ambiguity is what Phase 3 (explicit `Beta` prior) resolves. Don't claim Phase 2
> makes propagation idempotent across repeated calls; claim only that a single
> propagation is order-independent and convergent.

---

## Algorithm (Option A)

Let the changed node be `seed`, clamped to `seed_prob` and held fixed. For every
other node `v` in the subgraph let `base[v]` be its probability at pass start.

Per-node combine (order-independent; products over the node's incoming edges):

```
p ← base[v]
p ← 1 − (1 − p) · ∏_{e ∈ supports(v)} (1 − w_e · val[src_e])     # noisy-OR of support/causes
p ← p · ∏_{e ∈ defeats(v)} (1 − w_e · val[src_e])               # noisy-AND of defeats
val[v] ← clamp(p, 0, 1)
```

`CONTRADICTS` is skipped, as today. **Single-edge reduction check** (so you can
see the existing tests still hold):

- one defeat, `base=0.7, w=1.0, val_src=0.8` → `0.7 · (1−0.8) = 0.14` ✓ (matches `test_propagate_defeat_single_defeat_edge_reduces_probability`)
- one support, `base=0.3, w=0.5, val_src=0.8` → `1−(1−0.3)(1−0.4) = 0.58` ✓ (matches `test_propagate_defeat_single_support_edge_increases_probability`)

Fixpoint loop:

```
initialize val[v] = base[v] for all v; val[seed] = seed_prob
repeat up to MAX_ITERS:
    for v in subgraph sorted by id, v ≠ seed:
        val[v] = combine(v)               # reads current val[...] of parents
    if max_v |val[v] − val_prev[v]| < EPS: break
return { (v, val[v]) : |val[v] − base[v]| > EPS }   # seed excluded; only changed nodes
```

Use `const MAX_ITERS: usize = 50;` and `const EPS: f64 = 1e-9;`. The subgraph is
finite; on a DAG one Gauss–Seidel-style sweep in topological order is exact, and
sorted-id sweeps converge fast in practice. If you observe oscillation on dense
cyclic graphs, add damping `val[v] = (1−λ)·val_prev[v] + λ·combine(v)` with
`λ=0.5`; default `λ=1`. **Never loop unbounded** — if `MAX_ITERS` is hit without
convergence, return the current values and `tracing::warn!` once with the
subgraph size; do not error.

---

## Changes, file by file

### `crates/core/src/inference.rs`

- Rewrite the body of `propagate_core` (the private fn introduced in Phase 1;
  if Phase 1 hasn't landed, introduce it now per that plan's §1) to the snapshot
  + per-node aggregation + fixpoint above. **Signature stays identical**, so
  `propagate_defeat`, `intervene`, and all callers are untouched.
- Build incoming adjacency keyed by **target**:
  `HashMap<Uuid, Vec<(EdgeType, Probability, Uuid /*src*/)>>`.
- Keep `attenuate_by_defeat` and `boost_by_support` as public single-edge
  primitives (still referenced by their unit tests and by the Agda
  correspondence). `combine` may call them in the 1-edge case or implement the
  products directly; either is fine as long as the reduction identities hold.
- Add `const MAX_ITERS` / `const EPS` and the damping constant.

### `crates/core/src/lib.rs`

- No signature changes. `propagate_from` and `query_intervention` already call
  the core.
- **Optional behavior upgrade:** today `add_edge` (line ~179) calls
  `propagate_from` only when the new edge is `DEFEATS`. Now that propagation is
  well-defined for all structural edges, consider triggering `propagate_from`
  on `SUPPORTS` and `CAUSES` inserts too. Flag this as a discussion point — it
  changes write-path cost — and gate behind the same single call. Do not enable
  silently.

### `spec/Mimir/Inference.agda`

Scope the proof to what's provable cleanly:

- Reformulate `boost`/`attenuate` as the one-shot combine over an edge list and
  prove **`combine-order-independent`**: permuting the incoming-edge list leaves
  the result unchanged. This is immediate from commutativity of `_*_` over the
  product — and it is exactly the property the old BFS lacked.
- Reprove the monotonicity halves in aggregated form: **support/causes-only
  combine ≥ base** (product of `(1 − w·v) ≤ 1` ⇒ noisy-OR ≥ base) and
  **defeats-only combine ≤ base** (product of factors `≤ 1`).
- **Explicitly document** that fixpoint convergence of the iteration is *not*
  proved in Agda (it's an operational property bounded by `MAX_ITERS`). Replace
  the current overclaiming comment ("correctness of the full BFS follows by
  induction over the downstream list") with an accurate statement: the spec
  proves per-node order-independence and monotonicity; the service caps
  iteration. This corrects a real inconsistency in the current spec.

---

## Tests (`crates/core/src/inference.rs` + integration)

1. **Regression — single-edge unchanged.** The existing `propagate_defeat`
   single-edge tests must pass with zero edits. (They will, by the reduction
   identities.)
2. **Order-independence on a diamond.** `S→A→T` and `S→B→T`, all SUPPORTS.
   Compute `propagate_defeat(S, …)` and assert `T` equals the one-shot combine
   value, and that shuffling the `edges` slice produces the identical result.
   This test **fails on the current code** (that's the point) and passes after.
3. **Multi-parent noisy-OR.** `T` with two supporters `p1,w1` and `p2,w2`;
   assert `val[T] = 1 − (1−base)(1−w1·p1)(1−w2·p2)` within `1e-9`.
4. **Convergence on a cycle.** `A↔B` SUPPORTS both directions; assert the loop
   terminates within `MAX_ITERS` and the result is stable on a second call from
   the same base.
5. **proptests:** combine result in `[0,1]`; support-only combine `≥ base`;
   defeat-only combine `≤ base`; result invariant under a random permutation of
   the incoming-edge vector.

---

## Acceptance criteria

- `cargo test -p mimir-core` green, including the new order-independence/
  cycle/noisy-OR tests, **and** the pre-existing single-edge propagation tests
  unmodified.
- `propagate_defeat` and `intervene` produce identical results regardless of the
  order of the `edges` slice (assertable in a test by shuffling).
- The fixpoint loop is provably bounded (`MAX_ITERS`) and emits a single warning,
  not an error, on non-convergence.
- `Inference.agda` type-checks with `combine-order-independent` proved and the
  overclaiming BFS comment replaced by an accurate one. `--safe` retained.
- No public signature changed; Phase 1 functionality (do-operator) still passes
  its tests and now inherits order-independence.

If the diamond test can't be made to pass without changing a public signature,
stop and report — that would indicate the `propagate_core` refactor from Phase 1
wasn't in place.

---

## Optional Alternative — Option B (full log-odds unification)

If you'd rather unify support and defeat into a single principled rule, replace
`combine` with a **logarithmic opinion pool**: carry `L[v] = logit(base[v])`
(with `p` clamped to `[ε, 1−ε]`, `ε=1e-6`, so `logit` is finite), add signed
evidence per incoming edge — `+w·logit(val[src])` for SUPPORTS/CAUSES,
`−w·logit(val[src])` for DEFEATS — sum over all parents, and set
`val[v] = sigmoid(L[v] + Σ contributions)`. Same fixpoint loop.

Tradeoffs, stated plainly:

- **Pro:** one symmetric rule; order-independence is even more obvious (sum
  commutes); it is literally naive-Bayes log-likelihood-ratio accumulation.
- **Con:** it **changes semantics** — a *disbelieved* supporter (`p_src < 0.5`,
  `logit < 0`) now actively *suppresses* the target, whereas the noisy-OR view
  has it merely "not fire." The single-edge reduction identities above **no
  longer hold**, so the existing unit tests must be rewritten, and the Agda
  monotonicity lemmas are replaced by order-independence only.

Default to Option A. Take Option B only on an explicit instruction to change
support semantics — it is a modeling decision, not a bug fix.

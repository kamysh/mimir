# Phase 3 (optional) — beliefs as Beta(α, β)

Do this only after Phases 1–2 have proved the system earns its keep. It is the
most invasive change (touches the data representation) and the highest-payoff
conceptually: it makes `confidence` a real quantity that *updates* instead of
only decaying, unifies the two ad-hoc scalars under one model, and **resolves the
prior-vs-posterior ambiguity Phase 2 left open**.

## The model

Represent each belief as a Beta distribution `Beta(α, β)`, `α, β > 0`:

- **probability** = mean = `α / (α + β)` (what the rest of the system reads today).
- **confidence / strength** = pseudo-count `κ = α + β` (variance falls as `κ` grows;
  `Var = αβ / (κ²(κ+1))`). This is what `confidence` was always gesturing at.

Store the **prior** `(α₀, β₀)` fixed at insertion, separately from accumulated
evidence. The posterior is `α = α₀ + Σ pos_evidence`, `β = β₀ + Σ neg_evidence`,
recomputed from the edge structure on each propagation. Because evidence is
re-derived rather than folded into a mutated scalar, **propagation becomes
idempotent** — calling it twice yields the same result, which Phase 2 could not
guarantee.

## Mappings (document these constants in one place)

- **Insertion** `(p, c) → (α₀, β₀)`: pick a pseudo-count from confidence,
  `κ = KAPPA_MIN + c · (KAPPA_MAX − KAPPA_MIN)` (e.g. `KAPPA_MIN = 2` ≈ near-
  uniform, `KAPPA_MAX = 200`), then `α₀ = p·κ`, `β₀ = (1−p)·κ`. So `c=0` ⇒ weak
  prior easily moved by evidence; `c=1` ⇒ strong prior.
- **Support** from a parent (weight `w`, parent mean `μ_src`): add positive
  evidence `Δα = w · μ_src · UNIT` (`UNIT` a configurable evidence quantum, e.g.
  `4.0`). **Defeat:** `Δβ = w · μ_src · UNIT`. Conjugate accumulation — this is
  the Bayesian version of Phase 2's noisy-OR/noisy-AND, now with a real strength.
- **Decay** = pull the posterior toward the prior strength (aging evidence makes
  you less sure): `(α, β) ← (1,1) + f^days · ((α, β) − (1,1))`. The mean drifts
  toward 0.5 as evidence ages — giving the current confidence-decay actual
  consequence (today confidence decays but never feeds back into probability).

## Changes, file by file

- **`crates/core/migrations/004_beta_beliefs.sql`** — one-time backfill. AGE
  vertices store properties in `agtype`, so the "migration" is a Cypher `SET`
  over existing `Belief` vertices computing `n.alpha`, `n.beta`, `n.alpha0`,
  `n.beta0` from current `n.probability`, `n.confidence` via the insertion
  mapping. Keep `probability`/`confidence` as derived/cached properties for
  backward-compatible reads during rollout.
- **`crates/core/src/graph.rs`** — extend `Belief` with `alpha`, `beta`,
  `alpha0`, `beta0` (validated `> 0`). Add `fn mean(&self) -> Probability` and
  `fn strength(&self) -> f64`. Keep `probability()`/`confidence()` as accessors
  computing from `(α,β)` so call sites don't all change at once. Add a
  `Beta` newtype if you want the invariants enforced in one spot.
- **`crates/core/src/store.rs`** — read/write the new properties; `belief_from_row`
  gains `alpha/beta/alpha0/beta0` columns with a fallback that derives them from
  `probability/confidence` when absent (so a partially-migrated graph still
  loads). `update_belief_probability` is superseded by an `update_belief_beta`.
- **`crates/core/src/inference.rs`** — replace the combine with conjugate
  evidence accumulation in `(α,β)` space (the Phase-2 fixpoint structure carries
  over verbatim; only `combine` changes — it now sums `Δα`/`Δβ` from parents onto
  `(α₀, β₀)` and recomputes the mean). `decay_all` decays the pair toward `(1,1)`.
  `is_contradicting` can keep using means for compatibility, or switch to an
  overlap/divergence test (note as optional).
- **`crates/core/src/lib.rs`** — `add_belief` takes `(p, c)` as today and maps to
  `(α₀,β₀)` at the boundary, so the public API and MCP/CLI surface are unchanged.
  Propagation writes `(α,β)` back.
- **MCP/CLI** — surface unchanged at first (`probability`/`confidence` derived).
  Optionally add a `belief_strength` field to `get_belief` output and a
  `--strength` column to `mimir list`.
- **`spec/Mimir/Types.agda` / `Graph.agda` / `Inference.agda`** — model `Belief`
  with `α, β` (as `ℕ` numerators over a fixed denominator, consistent with the
  existing `Prob = ℕ%` approximation). Prove: `mean ∈ [0,1]`; support increases
  `α` ⇒ mean non-decreasing; defeat increases `β` ⇒ mean non-increasing; decay
  toward `(1,1)` moves the mean monotonically toward `½`. The idempotence claim
  (posterior = prior + evidence, evidence re-derived) becomes a clean equational
  lemma — state it.

## Tests

- Round-trip: `(p,c) → (α₀,β₀) → mean/strength` recovers `p` exactly and a
  monotone function of `c`.
- **Idempotence:** two consecutive `propagate_from` calls from the same base
  yield identical `(α,β)` (the property Phase 2 explicitly could not promise).
- Conjugacy: N support observations move the mean the Bayesian amount; strength
  grows by `N·UNIT`.
- Decay drifts mean toward 0.5 and reduces strength; a never-corroborated belief
  ages toward uninformative rather than staying confidently stale.
- Migration: a graph written pre-migration loads post-migration with means equal
  (within rounding) to the old probabilities.

## Acceptance criteria

- Public MCP/CLI API and the hooks are unaffected (means/confidence still read
  the same); existing integration tests pass.
- `propagate_from` is idempotent (test-enforced).
- A pre-Phase-3 database backfills cleanly and loads with unchanged means.
- The Agda model carries `(α,β)` with the four monotonicity/idempotence lemmas
  proved; `--safe` retained.
- `confidence` now has a feedback path into `probability` via decay — demonstrably
  (a decay test shows the mean moving), unlike today.

If the backfill can't preserve means within rounding tolerance, stop and report;
silent drift in existing beliefs is not acceptable.

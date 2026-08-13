# mimir memory evolution — open questions for future work

Status: **discussion draft, not a plan**. Everything below is a candidate; none of it is
scheduled or approved. Purpose is to pin down the shape of each idea and the specific
decisions still needed before any of it becomes a `30-`/`40-`-style implementation plan.

Context: this followed from reading arXiv 2512.13564 ("Memory in the Age of AI Agents: A
Survey"), which produced the `memory_type` (Fact/Experiential/Working) feature (shipped,
uncommitted as of this writing) and surfaced four further candidates. The candidates below
are those four, sharpened against the paper's Section 5 (memory dynamics) and Section 7.1
(retrieval vs. generation), and against concrete failures observed in the session that
produced this doc — most usefully, a correction chain (`10c534fb → 99d9b202 → 95e91143`)
that sat in the graph as three separate nodes instead of one current-state summary.

## 1. Consolidation (cluster-level) — IMPLEMENTED as attenuated deletion (2026-08-13)

**Shipped**: `InferenceEngine::find_expired_defeated` (pure, unit-tested — 5 cases:
threshold, grace period, latest-defeat-resets-clock, missing-belief-skip) +
`MimirService::sweep_expired_defeated(prob_threshold, grace_hours, project)`, exposed via
`mimir sweep-defeated --threshold --grace-hours --project` (CLI) and the
`sweep_expired_defeated` MCP tool, mirroring `decay_all`'s dual exposure. Store layer:
`AgeStore::get_defeats_with_timestamps[_by_project]` (project-scoped variant added
specifically so the sweep is never accidentally global — 4 new integration tests cover
threshold, grace-period, and project-isolation behavior against the live DB, all inserting
into throwaway `_test-*` projects only). 85 unit + 47 integration tests pass, clippy clean
across the workspace. Not yet committed. No Agda changes — this is a maintenance operation
in the same category as `decay_all`/`delete_belief`, not a proven invariant.

Original design discussion (rejected alternatives, evidence for the final design) kept
below for the record.

**Original problem statement**: mimir has no automated merging of redundant or superseded
beliefs. A correction chain — old belief, defeat edge, new belief, another defeat edge,
another new belief — accumulates as N separate nodes. `query_relevant` can return any of
them, including stale ones, and a caller has to reconstruct "what's actually true now" by
reading the whole chain and its edges.

**Why it's rejected as scoped** (user pushback, 2026-08-13: "I don't see the scenarios
where this can be beneficial" — correct call): the case for collapsing nodes at write time
doesn't survive contact with what mimir already does.
- Storage/graph size isn't a real constraint at ~800 beliefs; consolidation buys no
  performance.
- Collapsing nodes trades away the audit trail (why the belief changed, what was tried
  first) for a marginal readability gain.
- The actual failure this session ("chains resurfacing as if independent") traced to
  `record_defeat` never being called, not to the graph shape — already fixed by the
  call-it-immediately rule (belief `20b15e36`). Once supersession is linked promptly,
  the graph-mutation case weakens further.

**What does remain a real, narrower question — read-side, not write-side**: `query_relevant`
fuses vector/token/probability rankings via weighted RRF with probability at **weight 0.1**
against the semantic leg's **weight 1.0** (`crates/core/src/lib.rs`, `W_VECTOR`/`W_TOKEN`/
`W_PRIOR` — this weighting is deliberate, so a confident-but-irrelevant belief can't bury a
strong semantic match). Consequence: a defeated node's Beta-attenuated probability drop is
only a *gentle nudge* in the final ranking, not a filter — a stale node that's still
semantically close to the query can still surface near its corrector, even when
`record_defeat` was called correctly and promptly. So attenuation alone doesn't fully solve
the "which one is current" problem either.

**Revised decision (2026-08-13, second pass)**: the read-side filter proposed above was
itself rejected on user pushback — it's not a resolution, it's more permanent retrieval
logic layered on top of the decision to keep superseded nodes around at all, which is the
actual complication being objected to. Weighing "keep + filter" against "just delete
superseded nodes" directly:
- Keeping them buys an audit trail that hasn't actually been used for its own sake this
  session — the only time chain history mattered was in *this session's own postmortem*,
  an unusual reflective case, not normal operation.
- The RRF weight-0.1 finding above means keeping a superseded node doesn't even give a
  retrieval-time safety net — it can still rank near its corrector, so "keep it just in
  case" doesn't reliably protect anything at read time either.
- Deletion is a smaller, one-time cost paid at `record_defeat` time; keeping-plus-filtering
  is unbounded complexity paid on every future query, permanently, for a benefit (history
  inspection) that hasn't materialized as a real need.
- `delete_belief` already exists and does the right thing mechanically (Cypher
  `DETACH DELETE`, cascades all incident edges — `crates/core/src/store.rs`). There's also
  live precedent: `10c534fb` was deleted outright, not just defeated, when found flatly
  wrong.

**Revised again (2026-08-13, third pass) — attenuated deletion, not immediate**: the user
pointed out the actual danger in "delete at `record_defeat` time" directly: my own defeat
calls are themselves conclusions, and this session's own history shows conclusions I assert
with high confidence are wrong often enough that immediate, permanent deletion is too
aggressive a response to a single `record_defeat` call. Concretely: `10c534fb` was
defeated once (`99d9b202`), and that first correction later turned out to itself need
refining (`ec68a138`) before the design actually settled — if `10c534fb` had been hard-deleted
the moment the first defeat landed, there would have been nothing left to refine against.

**Current position**: do not delete at `record_defeat` time. Instead:
- `record_defeat` keeps doing exactly what it does today (Beta-attenuation, no new deletion
  behavior at write time).
- A defeated node becomes eligible for actual deletion only after (a) its probability has
  stayed below some low threshold, and (b) a minimum grace period has elapsed since the
  defeat, with no intervening `record_support`/reversal — i.e. the defeat has to survive
  scrutiny over time, not just be asserted once.
- This is a **new periodic sweep**, not a repurposing of `decay_all` — checked directly:
  `decay_all` operates purely on elapsed time since `last_activated_at` and has no
  awareness of DEFEATS edges or probability thresholds at all (`crates/core/src/lib.rs`,
  `decay_beliefs`). Reusing its *cadence* (run at the same trigger points, e.g. session
  start) is reasonable; reusing its *function* is not — the deletion sweep needs different
  inputs (DEFEATS-connected components, probability, time-since-defeat) that `decay_all`
  doesn't compute.
- This is structurally symmetric with the Working→Fact staging pattern already decided
  (write cheap, promote/discard only after the conclusion holds up under reflection) —
  applied to the decay side: a defeat is provisional until it survives a grace period,
  exactly like a Working belief is provisional until it survives reflection before
  promotion.

**Grace period, decided from real data (2026-08-13, verified count)**: queried the live
mimir graph directly instead of guessing. First pass asserted 44 edges without actually
running `count(*)` — wrong; corrected below.
```
MATCH ()-[:DEFEATS]->() RETURN count(*)                                        -- 48 raw edges
MATCH (a:Belief)-[:DEFEATS]->(b:Belief) RETURN DISTINCT a.id, b.id             -- 46 distinct pairs (2 duplicated)
MATCH (a:Belief)-[:DEFEATS]->(mid:Belief)-[:DEFEATS]->(c:Belief) RETURN DISTINCT mid.id  -- 7 chain-interior nodes
```
Of 46 distinct DEFEATS pairs, **7 are chain-interior** (a defeated belief that itself later
defeated something else) — ~15%; the other ~85% are terminal, one-shot corrections that
never got revised further. For the 7 chain cases, the time between a node's creation and it
getting defeated in turn: 32s, ~3min, ~3.5min, ~4.6min, ~7.8min, ~29min, ~86min, and one
outlier at **~10.3 hours** (`158f9f21` → `7f6e24fa`, 2026-08-11). Every other self-correction
happened within the same working session, in minutes.

**Decision**: grace period = **24 hours**, or equivalently "survive until the next
session-start sweep" (reusing `decay_all`'s existing session-start trigger point rather
than inventing a new schedule). This clears the one real 10-hour outlier with margin
without an open-ended or arbitrarily long window. Revisit only if a future case is observed
that takes longer than this to settle — not from first-principles reasoning.

## 2. Forgetting for Experiential beliefs

**Problem**: `Experiential` beliefs are exempt from `decay_all` by design (the lesson
doesn't get less true with elapsed time) but that means the bucket only grows — currently
123 beliefs, no ceiling.

**Shape from the paper** (Sec 5.2.3): time-based (already excluded, by design), frequency-
based (retrieval-count — beliefs nothing ever retrieves are candidates), importance-driven
(LLM-judged redundancy or staleness independent of retrieval activity).

**Open questions**:
- Does mimir even track retrieval frequency today? (Need to check — if `query_relevant`
  doesn't log which beliefs it returned, frequency-based forgetting needs that
  instrumentation first.)
- Is this "forgetting" (delete) or "demotion" (something else, e.g. drop out of default
  ranking but stay queryable on request)? Deleting a hard-won lesson because it's rarely
  retrieved could just mean it's rarely relevant, not that it's wrong.
- What's the actual pain being solved — is 123 beliefs (growing at maybe 5-10/session)
  actually a problem yet, or is this premature? Worth checking whether `query_relevant`'s
  ranking degrades measurably before building a pruning mechanism for it.

## 3. Type-aware ranking

**Problem**: `query_relevant`'s weighted-RRF fusion treats `Fact` and `Experiential`
identically. A "how should I approach X" query plausibly wants Experiential ranked higher;
"what is X" plausibly wants Fact ranked higher.

**Shape**: not covered directly by the survey (its hybrid-retrieval discussion is
lexical+semantic+graph fusion, not function-type-conditioned weighting) — this stays a
mimir-specific design.

**Open questions**:
- Is query-shape detection ("how" vs "what") reliable enough to key ranking off, or does
  it need an explicit caller-supplied hint instead (e.g. a `prefer_type` param on
  `query_relevant`)?
- This was explicitly flagged as more speculative than the other candidates until
  `memory_type` sees real usage across more sessions — is there enough usage data yet to
  even evaluate whether current ranking is actually a problem?

## 4. Generative retrieval (new, from this reading)

**Problem**: `query_relevant` returns N separate belief JSON blobs. The caller (a Claude
Code session) has to notice contradictions between them itself. This session's own
recurring failure — "discovering a contradicting record after acting" — was partly this:
being handed 5 beliefs and not reconciling them before acting.

**Shape from the paper** (Sec 7.1): "retrieve then generate" — retrieved items become raw
material for a synthesized, coherent representation, rather than being handed back
verbatim.

**Open questions**:
- This is the most speculative of the four and probably the most expensive (an extra LLM
  call inside `query_relevant`, latency and cost tradeoff against the current single DB
  round-trip). Worth prototyping before committing, if at all.
- Was going to subsume consolidation (item 1) — moot now, since item 1 shipped as
  attenuated deletion instead of a graph-collapse feature; the two no longer compete for
  the same problem.

**Concrete mechanism, from Sec 5.1.1 (2026-08-13)**: "generative retrieval" was speculative
because it had no attached algorithm. Sec 5.1.1's *incremental semantic summarization* —
fuse each new item into a running summary one at a time (MemGPT/Mem0's simple merge; later
RL-optimized in Mem1/MemAgent to fight semantic drift across steps) — is exactly the missing
mechanism: apply the same fold-in-order-with-consistency-checking operation to
`query_relevant`'s ranked result list instead of to a raw dialogue stream. Still not
scoped as work (same cost/latency concern above applies), but no longer an unattached idea.

**Note on where Sec 5.1.1 does *not* apply**: mimir's beliefs are already atomic,
single-claim, and short by design (`insert_belief`'s "one claim per belief" discipline) —
they aren't raw or verbose the way the survey's target data (dialogue transcripts,
interaction logs) is. The *partitioned* summarization paradigm (cluster then summarize —
RAPTOR, ReadAgent/LightMem) is structurally what the original, rejected consolidation
design in section 1 would have been (collapse a DEFEATS chain into one summary node). It
was rejected specifically because mimir's belief layer doesn't have the raw/verbose-data
problem 5.1.1 solves — the compression benefit that justifies it in general agent memory
systems doesn't transfer here.

## 5. Document-chunk summarization (new, from Sec 5.1.1, not previously listed)

**Problem**: unlike the belief graph, `DocumentChunk`/`load_document`
(`crates/core/src/documents.rs`) genuinely *is* raw, potentially long, verbose data —
5.1.1's actual target. Today mimir only does structured construction on documents
(heading-bounded chunking, one flat passage-level granularity); there's no summarization
layer on top, so `query_document` can only retrieve at passage granularity, never
"what is this whole document about."

**Shape from the paper**: partitioned semantic summarization (RAPTOR: recursive
clustering + per-cluster summary; ReadAgent/LightMem: cluster by topic first, then
summarize each cluster) applied to `DocumentChunk`s — generate one summary chunk per
section-cluster (or one per document), stored and embedded like any other chunk, giving
`query_document` a coarser retrieval tier alongside today's passage-level one.

**Not evaluated yet** — this is a fresh observation from this reading, not weighed against
alternatives or scoped. Whether it's worth building depends on whether coarse
"what's this document about" queries are an actual need, which hasn't been established.

## Not in scope for this doc

- The `memory_type` field itself — already implemented, tested, and its design settled
  (see mimir beliefs `ec68a138`, `422e325d`). Not reopened here.
- Auto-DEFEATS on correction — already implemented (belief `9269d940`).
- The reclassification backfill — already done, one-time operation (belief `941aa15d`).

## Next step

None of the four items above should move to a `3x-plan-*.md`-style implementation doc
until the open questions in its section are actually answered — with the user, not
assumed. This doc exists to make those questions explicit while the context from reading
the survey is still fresh, not to pre-decide them.

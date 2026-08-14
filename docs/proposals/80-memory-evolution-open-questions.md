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

**Shape from the paper** (Sec 5.2.3): time-based (already excluded, by design),
~~frequency-based~~ (retrieval-count — REJECTED by user, 2026-08-14: "i don't like
frequency based update" — rarely-retrieved is not the same signal as wrong or low-value,
a rare-but-critical lesson would get pruned by exactly this mechanism), importance-driven
(LLM-judged redundancy or staleness independent of retrieval activity — the only shape
still on the table if this is ever built).

**Checked empirically (2026-08-14), not speculation anymore**:
- Does mimir track retrieval frequency today? **No.** `last_activated_at` is set once at
  insert (`store.rs:451`) and never updated anywhere else — confirmed by grepping every
  write site, and independently corroborated by `spec/Mimir/Types.agda:60`'s own comment
  ("write-once; drives decay"). Frequency-based forgetting needs new instrumentation
  (an on-read touch) before it's buildable at all — not a design question, a prerequisite.
- Is 123 beliefs actually a problem yet? **Live count re-checked, still exactly 123** —
  same figure as when this doc was first written, despite ~2 months elapsed (oldest
  2026-06-08, newest 2026-08-13) and a full day of heavy session work since. Real growth
  rate ≈2/day, not the 5-10/session guessed originally. No observed symptom of ranking
  degradation. This is premature to build — there's no evidence of actual pain yet.

**Still open** (the one question that isn't a fact-check):
- Is this "forgetting" (delete) or "demotion" (drop out of default ranking, stay queryable
  on request)? Deleting a hard-won lesson because it's rarely retrieved could just mean
  it's rarely relevant, not that it's wrong. Genuinely a design call, not something to
  resolve unilaterally.

**Conclusion**: don't build this yet. Both practical blockers (no instrumentation, no
demonstrated pain) are now confirmed facts rather than open questions — revisit only if
the belief count actually starts causing a measurable retrieval problem.

## 3. Type-aware ranking

**Problem**: `query_relevant`'s weighted-RRF fusion treats `Fact` and `Experiential`
identically. A "how should I approach X" query plausibly wants Experiential ranked higher;
"what is X" plausibly wants Fact ranked higher.

**Shape**: not covered directly by the survey (its hybrid-retrieval discussion is
lexical+semantic+graph fusion, not function-type-conditioned weighting) — this stays a
mimir-specific design.

**IMPLEMENTED as an explicit caller hint (2026-08-14)**: query-shape auto-detection ("how"
vs "what") was rejected as too fragile a heuristic over free text. Shipped instead: an
optional `prefer_type: Option<MemoryType>` parameter on `query_relevant` (CLI
`--prefer-type`, MCP `prefer_type`), a fourth RRF leg (`W_TYPE`) alongside vector/token/
prior — matching-type beliefs get a rank boost, non-matches are still returned, and
omitting the parameter leaves ranking byte-for-byte unchanged (empty leg contributes
nothing to `weighted_rrf`).

Tuning note, caught by a real integration test before shipping: the first attempt used
`W_TYPE = 0.1` (same weight class as `W_PRIOR`) and **failed** — `test_query_relevant_
prefer_type_reorders_tied_matches` showed two beliefs with identical content still ranked
by the "wrong" type. Root cause: `W_TOKEN` (0.3) and `W_PRIOR` (0.1) both derive from the
same underlying candidate order, so near-duplicate/tied beliefs (the exact case this
feature targets) inherit a *correlated* tie-break bias from both legs at once
(≈0.3+0.1)×(1/60−1/61) ≈ 0.000109, versus `W_TYPE=0.1`'s ≈0.000027 — four times too weak
to matter. Raised to `W_TYPE = 0.5` (clears the combined bias with margin, still far below
`W_VECTOR = 1.0` so a real semantic match always wins over type preference alone) — test
passes, full suite green (48 integration + 85 unit).

## 4. Generative retrieval (new, from this reading)

**Problem**: `query_relevant` returns N separate belief JSON blobs. The caller (a Claude
Code session) has to notice contradictions between them itself. This session's own
recurring failure — "discovering a contradicting record after acting" — was partly this:
being handed 5 beliefs and not reconciling them before acting.

**Shape from the paper** (Sec 7.1): "retrieve then generate" — retrieved items become raw
material for a synthesized, coherent representation, rather than being handed back
verbatim.

**RESOLVED as a protocol fix, not a tool change (2026-08-14)**: an extra LLM call inside
`query_relevant` was the wrong shape for this — the caller asking the question is *already*
an LLM (the Claude Code session itself), so a second round-trip to synthesize what it could
synthesize directly is pure latency/cost with no new capability. Checked the actual gap
empirically: `docs/claude-code-setup/skill/SKILL.md`'s READ discipline had a checkpoint for
disposing of *one* belief against your plan ("Following/Overriding belief `<id>`") but
**nothing** telling the agent to reconcile *multiple returned beliefs against each other*
before acting — that's the literal mechanism of the "handed 5 beliefs, acted on the first,
found the contradiction later" failure. Added a "Reconcile the set, not just each belief
individually" subsection to SKILL.md (and mirrored to both `CLAUDE.md`s) instructing exactly
that: scan for disagreement between results, and treat an unresolved conflict as a
`record_defeat` write-back opportunity, not something to silently pick a favorite on.

This also settles the paper's Sec 5.1.1 "incremental semantic summarization" angle raised
earlier — see section 6 below for why that mechanism doesn't transfer to belief-graph
data the way it does to raw dialogue/interaction logs. No Rust change; no new
latency/cost. If synthesis quality still turns out insufficient after the caller is
actually held to this discipline, that would be new evidence for revisiting the
tool-side LLM-call design — not assumed necessary up front.

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

**SPEC DRAFTED, awaiting approval before any Rust (2026-08-14)** — per this project's
absolute rule (no implementation code without a governing, user-approved Agda spec
first), the deliverable at this stage is `spec/Mimir/Documents.agda`, not code. `agda
--safe Mimir.agda` passes (exit 0).

Chose one-document-per-summary, not RAPTOR's full recursive cluster tree — that's more
mechanism than the stated problem ("what's this document about") needs, and nothing has
established that finer-grained cluster summaries are actually wanted. Design, minimal by
construction:

- `DocumentChunk` gains one field, `isSummary : Bool` (always `false` for chunks
  `load_document` parses). A summary chunk is otherwise a completely ordinary
  `DocumentChunk` — same AGE label, same `chunk_embeddings` row, same `CONTAINS`
  machinery — so no new storage, and it participates in `query_document`'s existing ANN
  ranking unmodified (it can surface there on its own semantic merit; no RRF change,
  unlike section 3 — this doesn't need weight-tuning because it isn't a ranked query).
- Two new MCP tools: `set_document_summary(path, content, project?)` (upsert — replaces
  any prior summary for that path, never accumulates) and `get_document_summary(path)`
  (direct lookup, not a semantic search — "what's this about" is an exact-match ask).
- **Generation stays outside mimir-core**, same reasoning as section 2's judge:
  mimir-core has no LLM-completion client (only embedding backends) and none is being
  added. The caller — an interactive session right after `load_document`, or a periodic
  job like section 2's — writes the summary text and pushes it via
  `set_document_summary`. mimir's role stays storage + retrieval, never generation.
- Invariant (stated, not proved from types — same status as the file's existing
  cross-store consistency invariant): at most one summary chunk per `documentPath`,
  maintained by the upsert's remove-then-insert pattern.

**Open**: is this actually wanted? Unlike sections 2/3, there's no empirical signal here
(no measured "coarse queries fail" pain) — this stays a design proposal until the user
decides it's worth the Rust + MCP-tool implementation.

## 6. Failure-driven reflection as the consolidation promotion method (new, from Sec 5.1.2)

**Problem**: the Working→Fact design (superseded twice: `ec68a138`'s narrow "staging tier
for a not-yet-confident conclusion", then the shipped `mimir hook stop` design, belief
`670f78a1` — always write Working, promote/discard only at session/task end) says a
Working belief gets "promoted after it holds up under reflection" — but "reflection" was
never given a concrete method. Consolidation currently means 1:1 rewrite-and-promote or
discard; there's no mechanism for extracting something better than the first-draft
conclusion already written.

**Shape from the paper** (Sec 5.1.2, Distilling Experiential Memory): *failure-driven
reflection* (Matrix, SAGE, R2D2) — extract insight from the **gap** between a trajectory
and what actually happened (a correction, a ground-truth mismatch), not from the
trajectory alone. Contrasts with *success-based* distillation (AWM/Memp, which only
summarize what worked).

**Where this connects to something already observed**: this session's own
`10c534fb → 99d9b202 → ec68a138` chain is a concrete instance of exactly this pattern —
the durable lesson (the narrow Working-as-staging-tier design) wasn't in the first belief,
it was in the *correction to* the first belief. A promotion step that only rewrites the
original Working belief would miss that; a promotion step that looks at "what got
corrected and why" would have captured it directly.

**Also relevant**: a possible backstop for a failure mode this session hit repeatedly —
an agent forgetting to write a belief mid-task until a hook forced it. The paper's
trainable-extraction systems (Mem-α, Memory-R1's `LLMExtract`) run distillation as an
automated pass over a transcript rather than relying solely on in-the-moment judgment.

**Not evaluated yet** — no design decision here, just naming a concrete mechanism (failure-
driven reflection) for a step ("reflection" in the promotion process) that's currently
undefined. Previously blocked on Working having zero live writers (belief `6dc25486`) —
no longer true as of 2026-08-14: `mimir hook stop` enforces consolidation at every turn end
(belief `670f78a1`), so Working now accumulates real per-session data. Whether manual
promotion turns out to be insufficient in practice, and failure-driven reflection worth
building, can now actually be evaluated against that data rather than staying purely
speculative.

## Not in scope for this doc

- The `memory_type` field itself — already implemented, tested, and its design settled
  (final form: belief `670f78a1`, superseding `ec68a138`/`422e325d`/`6dc25486` — always
  write `working`, consolidate at session/task end, enforced by `mimir hook stop`). Not
  reopened here.
- Auto-DEFEATS on correction — already implemented (belief `9269d940`).
- The reclassification backfill — already done, one-time operation (belief `941aa15d`).

## Next step

None of the four items above should move to a `3x-plan-*.md`-style implementation doc
until the open questions in its section are actually answered — with the user, not
assumed. This doc exists to make those questions explicit while the context from reading
the survey is still fresh, not to pre-decide them.

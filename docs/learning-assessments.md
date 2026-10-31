# Numeric learning assessments

Mimir stores typed estimates, decisions and suggestions on experience versions,
and separate correctness and usefulness contributions on review versions.
`learning_capabilities` advertises contract version 1 and assessment model 1.
These APIs support the harness learning extension; this checkout does not install
the harness capture loop or activate a judge.

## Recording and reviewing

`record_experience` accepts an optional `learning_items` array. Each item has a
UUID, kind (`estimate`, `decision`, `suggestion`), `source_ref`, `actor`, original
`statement`, `conditions`, and optional `predictions`. A prediction contains
`quantity`, numeric `value`, `unit`, `horizon`, `recorded_at`, and `inferred`.
Optional `probability`, `lower`, and `upper` preserve the stated uncertainty.
Intervals require both finite bounds and must contain the point estimate.
Dates and references are caller-provided provenance, not independently verified
facts. An inferred numeric interpretation must not be used as an original
forecast when evaluating calibration.

The experience ID identifies one incident. A learning item ID belongs to exactly
one incident, source reference and actor; corrections cannot move that identity
to a different source. Several items can describe one incident. The caller must
reuse incident IDs when a summary and a test receipt concern the same outcome;
different IDs cannot automatically be recognized as the same real event.

`review_experience` accepts optional `assessments`:

```json
{
  "target": {"candidate_key": "responsive-cleanup"},
  "scope": "large-task-records-v1",
  "rubric": "net-task-benefit-v1",
  "correctness": {"value": 1.0, "weight": 1.0},
  "usefulness": {"value": 1.0, "weight": 1.0},
  "evidence_indices": [0],
  "item_ids": [],
  "rationale": "The referenced comparison resolved the scoped claim and showed a net benefit."
}
```

A target is an existing `belief_id` or a belief candidate declared in that same
review. A procedure can be represented by an explicit belief about its behavior
and benefit; standalone Pattern records retain their existing success-count
semantics. Scope and rubric keys are required, at most 200 bytes, and participate
in aggregation identity. Different keys never pool evidence automatically.

Correctness values are in [0,1], usefulness values in [-1,1], and weights in
[0,1]. A null value means unresolved and requires zero weight. Positive weight
requires at least one valid index into that exact experience version's evidence.
Item references must exist in that version. An `agent_report` alone cannot carry
observed evidence weight. `tool_result` and `user_feedback` remain caller-reported
provenance: the reviewer must still judge relevance and reliability. An unknown
overall task outcome can coexist with a resolved narrow claim.

There is at most one contribution per incident, belief, scope and rubric. Typed
contributions cannot overlap legacy feedback or graph links for that target in
the same review. Candidate aliases are resolved before checking this restriction.
Typed assessments do not modify generic graph probability or pattern counts.

## Scores and history

For the current review of each current experience version:

```
A = 1 + sum(correctness.weight * correctness.value)
B = 1 + sum(correctness.weight * (1 - correctness.value))
C = A / (A + B)
S = sum(usefulness.weight * usefulness.value)
W = sum(usefulness.weight)
U = S / (1 + W)
```

Unresolved axes add zero. The initial scores are C=0.50 and U=0.00. These are
uncalibrated estimates. Responses include evidence masses, incident and
unresolved counts, A/B/S/W, and a conditional model spread for correctness.
Zero usefulness mass means no measured benefit, which differs from measured
neutral benefit. Neither score grants authority or proves causal benefit.

`get_lesson_assessment` requires `project`, `belief_id`, `scope`, and `rubric`.
It validates project ownership and returns the current scores. Querying a valid
lesson with no active evidence returns the prior. `lesson_assessment_history`
accepts the same keys plus `offset` and `limit` (1–100) and returns immutable
contributions, their source/review revisions, current applicability flag and a
next-page offset. `experience_history` supplies the matching source versions.
History remains inspectable after a target is removed, while current-score reads
require an existing target.

`query_learning_context` includes `assessments` for the returned beliefs, grouped
by exact applicability scope and rubric. It caps groups at 100 and explicitly
sets `assessments_truncated`. Use exact assessment/history queries for known
groups beyond that retrieval budget. This does not change similarity ranking or
silently substitute a learning score for generic belief probability.

Revising an experience immediately makes its old review contributions inactive.
Revising a review replaces its contributions atomically. Retrying an acknowledged
or ambiguously acknowledged request reuses the same IDs, expected revision and
payload. Conflicting or stale payloads fail. Historical rows remain immutable;
queries join the active revision pointers so obsolete evidence cannot contribute.

## Compatibility and formal contract

Old JSON requests need no new fields. Empty optional fields are omitted from
serialized experiences and reviews, preserving legacy payload shape for retries.
The judge discovers the two new assessment read tools optionally, so older MCP
peers still work. Its review guidance supports typed assessment fields when the
advertised schema contains them.

Migrations 008 and 009 add only assessment contributions and item-identity
reservations. They preserve existing graph probabilities and records. They have
been exercised only in disposable test data for this stage. Deployment must
coordinate server and judge versions and back up the live database first. A
binary rollback cannot make older code understand typed reviews already stored;
rollback after live writes requires coordinated recovery, not just executable
replacement.

`Mimir.Assessment` proves bounds on rational aggregates, positive denominators,
unknown-evidence invariance, retry idempotence, correction replacement, stale
review exclusion, unrelated-group isolation and preservation of an arbitrary
control state. It uses the existing versioned-contribution laws. Runtime uses
finite f64 values with range checks and retains unrounded scores; displays can
round to two decimals. No runtime refinement, semantic extraction completeness,
evidence honesty or statistical calibration proof is claimed.

## Verification

The focused lifecycle regression uses real PostgreSQL/AGE migrations and checks
numeric success/correction/unresolved cases, retries, reconnection, invalid
evidence, identity conflicts, project isolation, duplicate contributions,
legacy-feedback overlap, history paging and unchanged generic probability.
MCP tests exercise capability discovery, typed review dispatch, numeric reads
and history alongside the existing learning cycle. Core property checks cover
score bounds and finite-value validation. The aggregate formal entrypoint is
`agda Mimir.agda` from `spec/` in the repository's Nix environment.

Automatic extraction, later-outcome discovery, reviewer self-trigger prevention,
the harness UI and live model calibration remain subsequent harness work.

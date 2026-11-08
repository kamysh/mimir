# Numeric learning assessments

Mimir stores typed estimates, decisions and suggestions on experience versions,
and separate correctness and usefulness contributions on review versions.
`learning_capabilities` advertises contract version 3 and assessment model 1.
These APIs support the harness learning extension; this checkout does not install
the harness capture loop or activate a judge.

## Recording and reviewing

`record_experience` accepts an optional `learning_items` array. Each item has a
local `key` for PostgreSQL UUID allocation, kind (`estimate`, `decision`, `suggestion`), `source_ref`, `actor`, original
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

Candidate names belong to one experience. Declare each name once in a review;
later reviews must retain its original belief or pattern declaration. A belief
target using `candidate_key` must name a belief candidate declared in that same
review. A pattern name cannot be used as a belief target.

Duplicate or undeclared names, changed declarations and attempts to publish a
deleted candidate return `needs_input` with the affected field and repair
guidance before publication. Use `get_learning_review` and `experience_history`
to inspect the original declaration and assigned ID. If different knowledge was
intended, ask the user which declaration or new stable name is appropriate;
do not silently rename or recreate a candidate. Refusal leaves the review and
candidate history unchanged. Retrying an already completed review still returns
its original answer after a candidate is deleted, without recreating that node.

## Compatibility and formal contract

### PostgreSQL-owned item identities

New learning items and review-extracted items declare an experience-local
`key`, such as `estimate-1`, and omit `id`. PostgreSQL generates their persistent
UUID with the ownership ledger's `gen_random_uuid()` default. Neither the model
nor Rust allocates these UUIDs. The same key can be used by different experiences
without sharing an item identity.

An assessment can use `item_keys` for these local references. Allocation resolves
them to `item_ids` before source validation and persistence. Stored items and
review readbacks include both the key and the allocated UUID. Review receipts
include the extracted key-to-UUID mapping in `item_ids`.

The reservation and the enclosing experience/review share one transaction.
Repeated keys reuse their committed allocation and immutable source/actor;
conflicting provenance, stale revisions, invalid references and failed reviews
cannot publish partial reservations. Corrections retain extracted UUIDs, kinds
and exact original quotations. Existing UUID-only items remain valid for
corrections when their ownership is already recorded. A supplied UUID cannot
create a new ownership row; new declarations must use a key and omit `id`.

An extracted item's `actor` must exactly match its cited `source_records`
entry's actor. Speakers named inside that source's text or embedded JSON belong
in `conditions`; they do not replace the recorded actor. A `wrong_actor`
refusal reports the exact `extracted_items[index].actor` path, stable item key,
source reference, expected actor and received actor. Identity conflicts are
reported separately, and rejection rolls back any tentative allocation.

The additive migration preserves historical payloads and UUIDs, imports missing
ownership reservations from existing history, adds nullable local keys, and
sets the PostgreSQL UUID default. Old clients that invent new item UUIDs need
to adopt local keys; existing no-item requests retain their prior shape. Server
and judge deployment must be coordinated because older binaries cannot read
the new keyed payloads. This change does not modify any live installation.

`Mimir.ItemAllocation` specifies the allocation boundary before the canonical
learning/source validators. Its general laws cover database-originated new
identities, stable key retries, refusal of unreserved caller UUIDs, isolation of
experience-local keys and rollback of reservations. UUID freshness is checked;
random generation is not assumed infallible. Existing ownership and item
retention laws continue to govern the allocated canonical items.

Requests without new item declarations need no new fields. Learning contract
version 3 requires PostgreSQL-owned IDs; the judge refuses a version 2 peer
before reviewing. Empty optional fields are omitted from
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

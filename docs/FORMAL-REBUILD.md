## Subsequent Rust implementation alignment

Current amendment: the user subsequently instructed removal of application
review limits. Historical entries below describing budgets, deadlines, content
caps or bounded MCP lines are superseded by `JudgeAccounting`,
`JudgeControllerAccounting`, `CompleteBytes`, the unbounded MCP transition
systems, and optional diagnostic-only persistence limits. General accounting,
frame provenance, revision receipts, ownership and cancellation laws remain
obligations. `ConfigurationUpgrade` specifies removal of exactly the four
retired LLM keys, with migration and idempotence proofs. See runtime/README.md
for current behavior; historical verification records do not certify this change.


The documented implementation findings have been addressed against the checked
contracts. Current changes, source mapping and verification are recorded in
[RUST-CONFORMANCE.md](RUST-CONFORMANCE.md). This includes the earlier judge
startup and persistence stages. Version 2.1.0 and installed binaries remain
unchanged. The specification-only completion receipt below is historical;
it does not certify a Rust binary or deployment.

## Completed bounded specification task

The detailed behavioral specification and coverage audit are complete. The final
Agda aggregate check passed with exit 0; all 638 safe modules are imported by the
root. See [FORMAL-BEHAVIOR-VERIFICATION.json](FORMAL-BEHAVIOR-VERIFICATION.json)
and [FORMAL-BEHAVIOR-COVERAGE.md](FORMAL-BEHAVIOR-COVERAGE.md).

Completion: 2026-10-31 03:59:41 UTC, before the agreed 07:03:56 UTC deadline.
No Rust source, installed binaries, version numbers, or system configuration
changed in this bounded task. Later implementation work is tracked in the
receipt linked above; the checked specification is not a runtime verification claim.
The 102 obsolete dependency-proof modules removed earlier remain absent.

The final connections include core startup, MCP/CLI execution, shared judge
client ownership/deadline/counter (including overflow), durable finalization,
standalone notification/OAuth/SMTP, watch/digest snapshots, configured embeddings,
physical storage/read contracts, legacy row decoding and AGE statement cleanup.
No new postulate was introduced. All three approved database assumptions remain
outside the safe root.

Verification resource issue: downstream reduction repeatedly unfolded the
already-defined OAuth SHA-256 identity helper. Making that checked helper
abstract preserved its definition and avoided normalizing library internals at
each use. The final batch maximum residency was 1.386 GB; no claim is based on
the earlier exhausted/interrupted runs.

Everything below is chronological history. Older pending, partial and incomplete
entries describe their own checkpoints; use the current receipt and coverage map
for the completed specification and the later Rust implementation receipt.

---

## Current task: completed behavioral specification within eight hours

User direction on 2026-10-30 replaces the broader implementation stage for now:
extend the existing Agda specification to fully detail Mimir behavior. Work starts
2026-10-30 23:03:56 UTC; completion is required before 2026-10-31 07:03:56 UTC.
No Rust edits, builds, installations, dependency-internal proof projects or system
changes are included. Reuse existing application models and complete operation
semantics, states, transitions, failure outcomes and protocols. Type checking and
an operation-to-specification coverage review are part of this task. The user
explicitly clarified that eight hours is a completion deadline, not permission
to stop with an unfinished specification. Completion requires the actual
behavioral specification and checks, not elapsed time or a partial report.

Execution budget, elapsed from that original start (480 minutes total):

| Minutes | Subtask | Observable output |
| --- | --- | --- |
| 0–30 | Gap inventory | MCP, CLI and background lifecycle coverage against existing definitions; behavior gaps separated from Rust correspondence gaps. |
| 30–120 | Learning and persistence | Complete experience/review transitions, corrections, ownership, assessment updates, transaction outcomes and retry behavior. |
| 120–210 | Graph, numerics and retrieval | Propagation, decay, intervention, scoring, selection, project boundaries and limits, using standard numerical operations. |
| 210–270 | Judge | Existing startup/controller/budget/completion/recovery models connected with missing transitions specified. |
| 270–315 | Documents and embeddings | Loading, replacement, chunk/vector association, querying and failure preservation. |
| 315–375 | Interfaces and other lifecycles | CLI/MCP defaults/errors, configuration, migrations and notification transitions. |
| 375–435 | Integration and verification | Aggregate type check and operation-by-operation behavioral coverage audit. |
| 435–480 | Correction reserve | Resolve verification failures and uncovered behavior before delivery. |

Completion requires inputs, validation, results, state changes and failure
outcomes for every operation. Enumeration or an unspecified application callback
does not establish coverage. Existing detailed models are reused rather than
rewritten. Reallocate against measured progress without silently dropping behavior.

READ COMMITTED was personally approved by selector reply on 2026-10-30 and added
to assumptions/Mimir/Assumptions/PostgreSQL.agda. Its exclusions and application
proof obligations are unchanged. The declaration passed the persistent interactive checker with checked=true and no goals or warnings (bULU7ecG log). Historical
entries below that say approval is pending record the earlier state.

## Graph/retrieval and judge composition checkpoint

New safe definitions cover RRF binary32 operation order and weights, token
ranking, type preference, scoped traversal, native path-query semantics,
learning-context pattern statistics and assessment grouping, current graph
records, direct edge writes, identity deletion, decay/intervention calculations,
and their inference/read protocols. Identity deletion instantiates the existing
lock-before-write transaction proof. The concrete storage carrier includes the
learning graph, document chunks, vectors and grounding edges.

Judge extensions reuse the existing handshake/controller/budget/persistence
models: JudgeHost, JudgeFinalization, JudgeSelection, JudgeRevisionPolicy and
JudgeBatchReadback specify watch outcomes, finish-report order, deferred queue
reconciliation, bounded candidate-conflict handling and final rereads of every
original selection. Focused checks are recorded in the persistent bULU7ecG log;
this is not the final aggregate receipt. Service/wire composition remains open.

Source findings requiring explicit specification boundaries:

- Native unscoped traversal UNIONs homogeneous SUPPORTS, CAUSES and DEFEATS
  paths; scoped BFS can mix them. Native causal traversal is depth 1..10 and lacks DISTINCT. GraphPaths records
  those query choices separately from the required complete, distinct mixed-edge
  or causal reachability results. AGE path internals remain a standard dependency
  boundary; native queries are not assumed to satisfy the stronger contract.
- RRF is binary32; the safe F32 interface supplies standard primitive operations.
  No new postulate or invented binary64/rational substitute was introduced.
  Unicode lowercase/alphanumeric and configured database text collation are
  likewise standard dependency boundaries, not application ranking callbacks.
- Native document replacement writes are sequential, while DocumentStore already
  requires atomic paired publication. Preserve that law; record native
  nonconformance instead of weakening it to fit current code.
- Direct insertion can persist a belief before an embedding failure. Bulk project
  deletion is a sequence of publications; identity deletion is one transaction.
- A count SELECT and a page SELECT may see different committed states. Each read
  protocol retains its separate snapshot rather than assuming repeatable reads.

No Rust, installed binary, application version or system configuration changed.
The original eight-hour deadline remains 2026-10-31 07:03:56 UTC.

## Step 2 core definitions checked; step 3 active

Concrete record/review plans now instantiate the learning transaction protocol,
including payload-size admission, revision/ownership checks, immutable histories,
active contribution replacement, numerical recomputation and ambiguous commit
outcomes. Standard Agda Float operations implement application formulas; no new
application postulate was added. Candidate node numeric fields now use Float so
the posterior calculation composes directly with actual graph-state publication.

Assessment formulas, current/history queries, pending selection, current review,
source/review history, provenance and explanation projections have focused safe
checks. Read protocols give each SELECT a separate input snapshot. Candidate-ID
bindings are response-only: ordinary experience reads normalize them to empty.

Source audit: /tmp/mimir-formal-source-audit-wnej_f8d.json: 537 safe modules,
all root-imported, no holes/escape markers. Interactive receipt remains the
bULU7ecG log. This is not a new aggregate-check receipt. Wire integration and the
final aggregate remain pending. Pattern statistics are defined; learning-context
ranking/assembly belongs with step-3 retrieval. No Rust or installed binary changed.

## Step 1 gap inventory completed

The behavioral coverage map is [FORMAL-BEHAVIOR-COVERAGE.md](FORMAL-BEHAVIOR-COVERAGE.md),
with machine-readable native locations/defaults in FORMAL-BEHAVIOR-COVERAGE.json.
It covers all 34 MCP operations, all 27 CLI leaf commands and seven cross-cutting
lifecycle groups. Native advertised tool names match the Agda catalog exactly;
CLI leaves are extracted from all six command enums; referenced modules exist.
These are inventory checks, not claims that the listed behavior is complete.

Reusable detailed learning/judge/persistence/notification models are identified.
The next work is concrete learning publication and read/projection composition.
Current retrieval scoring is mostly comments, and legacy percentage inference
cannot substitute for current Beta behavior. Dependency internals and Rust
correspondence remain excluded from this eight-hour specification task.
Step 1 used the user's selected Sol/high; Astra/high is recommended for step 2.
No model switch or additional agent was started. No Agda or Rust source was
changed during this inventory step; final aggregate verification remains due.

## Assessment, edge and concrete concurrency composition checked

The 517-module aggregate passed, exit 0:
/tmp/mimir-agda-assessment-edges-1EtPo6aA.log and .exit.
Elapsed 66.503s; maximum residency 1,119,741,496 bytes; unchanged 2 GiB cap.
Source audit: /tmp/mimir-formal-source-audit-zt5nr0g_.json, all safe modules
imported by the root, no proof holes or escape markers. This aggregate reused
completed interfaces; it is not a claim of a successful cold one-process rebuild.

ReviewPlanning.Following proves a second review using the first review's old
expected revision cannot publish any changes to the actual represented state,
including assessments and edges. It applies to the concrete planner for arbitrary
candidate-ID inputs. Native lock participation and fresh reads still must realize
the state supplied to this theorem. READ COMMITTED approval remains pending.

AssessmentWrites gives each admitted, resolved assessment its physical key,
original payload and application calculation expressions. General laws prove
exact row count, payload preservation, target identity and key uniqueness.
AssessmentHistory connects each row to an immutable applied-review version,
preserves prior references and excludes a new revision colliding with historical
assessment rows. These modules passed saved interactive checks. The native
arithmetic, row encoding and SQL correspondence remain open.

The aggregate attempt after the Binary64 comment correction invalidated dependent
interfaces and exhausted the unchanged 2 GiB heap cap while checking
JudgeReportReadBack. Receipt: /tmp/mimir-agda-assessment-publication-G518hesc.log,
exit 251, maximum residency 2,107,786,544 bytes. A focused interactive load also
exhausted that cap at the references proof; receipt:
/tmp/mimir-formal-interactive-record-composition-7GuJzjVe.log, exit 251.
The initial aggregate did not succeed. Explicit intermediate proof
arguments let references check, but the combined saved reload then exhausted the
cap at diagnosticEmission (receipt: 1ElLsAhY interactive log, exit 251).
The reference/counter portion was extracted to JudgeReportReferenceReadBack with
the existing Parser exports preserved. That module completed and its interface
was saved; compiling it together with the remainder still exhausted the cap
(receipt: MtTvKo4u interactive log, exit 251). The next focused check reuses that
completed interface in a fresh checker. That saved load passed checked=true,
with no goals or warnings (bULU7ecG interactive log). The theorem was not weakened
and the cap was not raised; the successful aggregate receipt is above.

ReviewEdges proves owned-edge replacement, preservation of unrelated edges,
absence of accumulation across replacements and provenance of generated edges.
Reverse-link completeness and publication composition now passed saved
interactive checks with no goals or warnings. Numerical recomputation and
SQL/native correspondence remain open; the represented publication is not yet
the complete native write set. Next: recomputation scope and arithmetic flow.
No Rust, version, binary, production or system-configuration changes.
Full rebuild remains active and incomplete.

## Typed review history and state-dependent planning checked

ReviewLedger stores submitted and applied reviews separately. It reuses the
existing revision state and ordered-history law, without assuming a global
request-to-effects materializer. General laws preserve immutable rows, select
the newly applied review, leave unrelated histories unchanged and retract active
selection on source correction. Its current-request pointer must match the
newest row's request key and source/review revisions.

ReviewPreparationPublication combines that typed history with the actual
prepared registry, graph nodes and ownership registry. Fresh writes require
matching project/CAS revision, a non-replay decision and room in the i64 counter.
ReviewPlanning executes validation, source pinning, bounded-revision checks,
exact-retry reconstruction and fresh preparation. It proves retry/stale revision
plans cannot append or publish changes, and replay IDs have live reservation
support. No abstract materialize parameter is used on this concrete path.
The supplied current experience still must come from the locked database read.

This is not yet the complete SQL transaction bundle: assessment rows, owned
edge replacement and numerical recomputation must be composed before a native
whole-write-set claim is justified. The conditional atomicity theorem currently
covers only the explicitly represented fields.

The 513-module aggregate passed, exit 0:
/tmp/mimir-agda-review-planning-cPp3eEGs.log and .exit.
Elapsed 36.667s; maximum residency 1,128,912,840 bytes; unchanged 2 GiB heap cap.
Source audit: /tmp/mimir-formal-source-audit-4xd6mzxs.json. Saved interactive
loads checked=true with no goals or warnings. READ COMMITTED approval remains
pending; no assumption instance was added. No Rust, version, binary, production
or system-configuration changes. Full rebuild remains active and incomplete.

## Review preparation and ownership composition checked

ReviewPreparation now computes candidate reservations, the proposed graph and
concrete materialization before semantic target/evidence admission. Its prepared
result explicitly equates the review checked by admission with the review
selected for publication. CandidateReview validates the submitted structure
first and exposes prepareValid to avoid repeating that validation in composition.
CandidateGraphUniqueness proves graph identity uniqueness is preserved across
arbitrary reservation batches, including earlier creations in the same batch.
Native ingress still must establish the initial unique-ID invariant.

ItemOwnerBatch composes the existing ItemOwners reservation model. General laws
preserve every existing ownership entry, establish all accepted item provenance,
and leave unmentioned identities unchanged. A failed batch returns no partial
registry. ReviewPreparation now reserves extracted-item ownership before
candidate preparation and proves recorded-item ownership is preserved when it
held on entry. Both source reference and actor are included with experience ID.

The 510-module aggregate passed, exit 0:
/tmp/mimir-agda-review-preparation-sJnpj0rw.log and .exit.
Elapsed 41.030s; maximum residency 1,018,834,304 bytes; unchanged 2 GiB heap cap.
Source audit: /tmp/mimir-formal-source-audit-g0rv_ofr.json. All saved changed
modules reloaded checked=true without holes, unsolved metas or warnings.

Remaining: compose this state-dependent preparation with revision classification,
immutable requested/applied history and the complete SQL write set. The generic
ReviewJournal materialize parameter cannot itself instantiate state-dependent
candidate allocation; this remains an explicit gap. Numerical recomputation,
SQL/native correspondence and the other inventoried operation groups remain
unfinished. READ COMMITTED postulate approval is still pending; no declaration
or instance was added. No Rust, version, binary, production or configuration
changes. Full rebuild remains active and incomplete.

## Candidate graph and joint publication checked

CandidateGraph specifies complete initial belief/pattern creation values and
links every command to its assigned final reservation. General proofs establish
that new command IDs are distinct and absent from the supplied occupied graph
IDs and prior registry IDs. Native preparation must supply the actual graph IDs.
Belief/pattern project fields allow global existing nodes; timestamps are signed
integers so the node carrier does not exclude pre-epoch existing values.
CandidatePublication preserves live reservation/node correspondence (identity,
project, kind, content and memory/pattern fields) and retains existing graph
nodes. Its atomic publication theorem requires the exact complete registry/node
bundle; it does not prove the current SQL realizes it or establish native ingress
identity uniqueness.

The 507-module aggregate passed, exit 0:
/tmp/mimir-agda-candidate-publication-pkl45cGN.log and .exit.
Elapsed 49.085s; maximum residency 994,647,616 bytes; unchanged 2 GiB heap cap.
Source audit: /tmp/mimir-formal-source-audit-c3lx03bt.json.

DatabaseReadCommitted is a checked safe interface only. The user was separately
asked to approve its read-only SELECT visibility postulate; approval is pending,
no postulate/instance has been declared. The two previously approved actual
postulates remain the only declarations in the isolated PostgreSQL module.
Official boundary source:
https://www.postgresql.org/docs/current/transaction-iso.html#XACT-READ-COMMITTED

Next independent work: fresh-review semantic preparation against the actual
proposed candidate nodes, then item ownership and concrete table writes. No Rust,
version, binaries, production data or system configuration changed. Full rebuild
remains incomplete and active.

## Candidate batch, materialization and retry composition checked

CandidateBatch composes each checked reservation in request order. General
proofs establish stable existing lookups, preservation of each declaration,
exact returned keys/counts and live final-registry support for every binding.
Generated IDs remain inputs and collision checks are obligations, not assumptions.
CandidateReview connects those bindings to concrete checked materialization,
including assessment cardinality and original quotations/coverage preservation.
CandidateReplay models candidate_ids: missing, changed or retired declarations
are rejected; accepted results retain cardinality and point to the same reserved
identities. An immediately replayed successful batch has no false validation
rejection. This extends the earlier retry proof, which covered inert evidence
and history but not native candidate-ID reconstruction failures.

The 504-module safe aggregate passed, exit 0:
/tmp/mimir-agda-candidate-composition-05QOvATp.log and .exit.
Elapsed 48.875s, maximum residency 988,327,952 bytes, unchanged 2 GiB heap cap.
All changed modules passed saved interactive reloads. Source audit:
/tmp/mimir-formal-source-audit-ihydinam.json.

Still open: pending graph-node creation and its atomic relationship to registry
rows, semantic admission against those nodes, concrete table write sets, and
Rust/native correspondence. The earlier abstract materialize parameter is not
a completed state-dependent native implementation; concrete candidate planning
must discharge that gap rather than assume it. The native candidates table has
a UNIQUE node_id constraint, but create_candidate_node currently creates a graph
node before inserting that row; checking collision against independent existing
graph nodes remains an application obligation.

No Rust, version, binary, production database or system configuration changes.
The full rebuild continues.

## Transaction ordering and review composition checked

LearningTransaction now specifies begin/acquire/read/decide/write/commit and
rollback paths with retained phase errors and rollback receipts. Its independent
scope policy requires the same transaction handle and shared lock for reads,
writes and commits. General completed-run and interrupted-prefix proofs establish
that the executable script respects this policy. A failed rollback receipt ends
the application trace; it does not claim that the database released the handle.

LearningTransactionReceipt proves every reported fresh success contains an
observed commit acknowledgement. Unknown commit outcomes remain uncertain.
ReviewTransaction connects that protocol to ReviewJournal: exact retry performs
only rollback, publication preserves active evidence and consecutive immutable
history under the approved atomicity contract. ReviewSerialization proves that
requests based on the old revision cannot append again once they read the first
publication. Native lock participation, coherent reads, SQL effects and actual
adapter correspondence remain explicit obligations, not assumed conclusions.

All four modules passed saved interactive reloads with no goals or warnings.
The 501-module safe aggregate passed (exit 0):
/tmp/mimir-agda-learning-transactions-1BjWu2Ug.log and .exit.
Elapsed 43.101s, maximum residency 968,945,816 bytes, unchanged 2 GiB heap cap.
Source audit: /tmp/mimir-formal-source-audit-ddkifl_e.json.
No new postulates, Rust edits, version changes, binary installs or production
changes. The full rebuild remains incomplete and active. Next: candidate batch
reservation/materialization composition, then the remaining concrete write set.

Mimir retrieval works again in this continuation; its general spec-first reminder
was useful but it provided no transaction-specific history. Muninn still has no
index for this worktree. Source evidence:
/tmp/mimir-transaction-protocol-source-HXO3zTxJ.log and .exit.

## User-directed removal of obsolete float and formatter work — completed

The user explicitly instructed removal after being told that obsolete dependency
proofs and aggregate imports remained. This supersedes the earlier decision to
retain them. Removed 102 source modules and their 102 compiled Agda interfaces:
89 standalone formatter/SIMD/word-layout/exponent-table modules, 11 custom float
arithmetic/quantization/conversion modules, and the unused Dyadic and
BinaryPowerLaws modules. No backups were created. Exact removal manifest and
no-stale-import audit: /tmp/mimir-obsolete-proof-removal-audit.json.

The new FloatValue module is a value carrier and sign/zero boundary, not an
arithmetic or formatting implementation. FloatConversion declares two supplied
conversion functions, cast/fromParts; it has no concrete instance, postulate,
or claim of native conversion correctness. NumericTokens separates shared
number/diagnostic types from parser execution. 101 consumer modules now receive
the conversion dependency explicitly. The surviving conditional laws quantify
over that dependency; this is not a completed native library correspondence.
No new assumption was smuggled into safe modules. Mimir numerical validation,
assessment, evidence, graph, inference, decay and propagation laws remain.

FloatConversion, SerdeNumeric and SerdeNumericOrdinary passed saved interactive
loads. Two checks exhausted the unchanged 2 GiB heap cap (exit 251):
/tmp/mimir-formal-interactive-record-composition-JQfNI46S.log and .exit;
/tmp/mimir-formal-interactive-record-composition-WeYP7mgI.log and .exit.
Generated dependency aliases were made private, and the remaining report,
incident and record modules passed individual saved interactive loads against
completed dependencies. The interactive receipt is
/tmp/mimir-formal-interactive-record-composition-7GuJzjVe.log.

The first aggregate attempt then failed with an Agda 2.8.0 internal compiler
error in Substitute.conApp while checking McpClientTransport.incomingReceipt,
projecting Reply from Effect.receiving (exit 154):
/tmp/mimir-agda-obsolete-proof-cleanup-XIju0X8G.log and .exit.
A localized reload reproduced it. Disabling projection-like optimization only
for Reply instead produced an ordinary type mismatch; that pragma was removed.
The parameter-independent Effect/Reply declarations now live in the safe
McpTransportEffect module and are publicly re-exported by McpClientTransport.
Their equations and all transport proof statements are unchanged. This saved
interactive check passed with no goals or warnings. No compiler flag or proof
weakening was retained. The final 497-module safe aggregate passed, exit 0:
/tmp/mimir-agda-obsolete-proof-cleanup-lcMohedo.log and .exit.
Elapsed 45.273s; unchanged 2 GiB heap cap. This completes the requested removal,
not the full Mimir rebuild or native conversion correspondence.

Source audit /tmp/mimir-formal-source-audit-3ze2lb34.json found 497 safe modules,
all imported by the root, with no holes or escape markers. The removal audit
also confirms no obsolete source or compiled interface was recreated and no
missing or stale imports remain. Counts are not coverage metrics.
The historical entries below describe removed work and are not current tasks.

Before cleanup, the user individually approved the advisory-lock postulate.
assumptions/Mimir/Assumptions/PostgreSQL.agda now contains exactly two approved
postulates: atomicTransactions and transactionAdvisoryLocks. The updated module
passed isolated interactive and batch declaration checks, exit 0:
/tmp/mimir-agda-approved-locks-O7JvXBgz.log and .exit.
Isolation audit /tmp/mimir-assumption-isolation-audit-0dkcjmr7.json found exactly
two declarations and no safe imports of assumption modules. The approved Rust
formatter assumption remains undeclared; no surviving module needs an instance
of the removed formatter implementation.

The independent writer audit found update_beliefs_beta lacks the learning
advisory lock, and propagate_from/decay_beliefs compute from reads outside the
write transaction. add_edge also inserts before separate propagation. These
are source-level transaction-boundary gaps, not a reproduced production race.
Evidence: /tmp/mimir-learning-writers-Bzqr4wAp.log and .exit;
/tmp/mimir-propagation-transaction-boundary-eQUm0ACW.log and .exit.
All-writer participation and coherent snapshots remain application obligations.

No Rust, version, binary, production data or system configuration changes.
The full rebuild remains unfinished and authorized; cleanup is the immediate
user-directed work, not a replacement for the larger objective.

## Review history and active-evidence composition verified

The safe 594-module aggregate passed (exit 0):
/tmp/mimir-agda-review-journal-hSJ5dJSt.log and .exit.
Elapsed 56.903s; maximum residency 1,243,443,512 bytes; unchanged 2 GiB heap cap.
Source audit: /tmp/mimir-formal-source-audit-wjzjngfc.json. The preceding audit
phuo6g7e correctly reported an unfinished interactive hole before it was solved;
it was not a completed verification result.

LearningPublication now separates submitted retry Payload from materialized
Contribution. Its explicit materialize parameter is an application obligation,
not an assumed implementation or approved postulate. ReviewResolution and
ReviewAdmission already model candidate resolution and semantic admission;
connecting them to the concrete stable candidate registry remains open.

ReviewPlan classifies the existing revision decision as refusal, exact replay,
or fresh review. ReviewJournal composes this decision with active evidence and
immutable history. General laws establish: replay leaves the entire modeled
world unchanged; fresh review retains all prior entries and installs the next
source/review/payload/effects entry; history revisions remain consecutive with
no gaps or duplicates; unrelated identities are preserved; source correction
keeps history and retracts active evidence. Its native boundary requires the
complete proposed-write equality and uses only the approved atomicity contract.
Exact retry preserves the whole publication for commit, abort or lost receipt.
These modules passed saved interactive reloads before the aggregate.

This is not complete SQL or Rust correspondence. Candidate reservation, item
ownership, graph-edge replacement, graph recomputation and exact SQL effects
must still be connected. Source receipt:
/tmp/mimir-review-write-plan-y3gkapZl.log and .exit.
The earlier read n8bwtaW8 used a nonexistent store path and failed; its output
was retained and the actual crates/core/src/store/learning.rs was then read.

Concurrency is separate from atomicity. The current source acquires advisory
key 671942183 in record_experience/review_experience before reading current
state, but a complete audit of all interfering writers remains open. No new
lock postulate has been declared. No Rust, binary, version, production database
or system configuration changes were made. The full rebuild remains active.

## Database boundary verified; assessment selection checked

The safe 591-module aggregate passed, exit 0:
/tmp/mimir-agda-database-boundary-uDBY7ccA.log and .exit.
Elapsed 60.600s; maximum residency 1,205,103,200 bytes; unchanged 2 GiB cap.
Safe source audit: /tmp/mimir-formal-source-audit-xy04kgu9.json.

The isolated approved PostgreSQL module also passed its separate batch check:
/tmp/mimir-agda-approved-postgresql-vetBrZBn.log and .exit.
The first separate batch attempt failed module-name lookup because the invocation
from spec/ omitted the assumptions/ include root, not because of an invalid
postulate type. Failure receipt: /tmp/mimir-agda-approved-postgresql-GU9F5wwL.log
and .exit. The maintained invocation for this separate local library is, from
spec/: agda -i . -i ../assumptions ../assumptions/Mimir/Assumptions/PostgreSQL.agda.
The safe aggregate stays agda Mimir.agda and never imports an assumption module.
No flags weaken safe application proofs. A checked postulate declaration is
not a proof of PostgreSQL or of the native adapter.

AssessmentSelection subsequently passed its saved interactive reload. Its nine
predicates model the exact three-table join and WHERE conditions used by
lesson_assessment: owner identities, contribution/review identity, current review,
current source revision, project, lesson, scope and rubric. General laws retain
matching rows and exclude stale sources, obsolete reviews and other query scopes.
This reuses standard-library all-filter/filter-accept/filter-reject proofs;
filter implementation is not reproved. The root imports the module. Current safe
source has 592 modules; this latest addition has not had an aggregate check yet.
Do not rerun the full aggregate for every small subsequent edit; interactive
saved checks are the normal development loop, aggregate checks belong at the
next substantive verification boundary.

Native SQL/table correspondence, primary-key uniqueness, numerical aggregation,
candidate/history composition and the Rust rewrite remain unfinished. In
particular, row-selection correctness is not yet proof of the full SQL query.
Source evidence: /tmp/mimir-assessment-transaction-evidence-KkGwVodE.log and .exit.

Additional public-operation audit found the project-deletion path already calls
delete_learning_project, so there is no basis for claiming it simply omits the
learning ledger. It performs multiple separate store operations; whole-operation
atomicity and returned-count correspondence still need analysis. Graph.agda
comments include patterns in the count, while store.delete_project counts
beliefs and service.delete_project adds chunks. No deletion behavior changed.
Evidence: /tmp/mimir-deletion-contract-review-8WKXx1fO.log and .exit;
/tmp/mimir-deletion-effects-uqohNDYH.log and .exit.

All rebuild work remains active. Only the individually approved PostgreSQL
postulate is declared; formatter remains approved but undeclared. No Rust,
installed binary, production database, version or system-configuration change.

## Learning publication composition and approved database boundary

The 590-module safe aggregate passed, exit 0:
/tmp/mimir-agda-learning-publication-YwyXvxhv.log and .exit.
Elapsed 63.913s; maximum residency 1,200,459,968 bytes; 2 GiB cap unchanged.
Source audit: /tmp/mimir-formal-source-audit-61cynwmy.json.

LearningPublication connects existing experience revision cells to their active
contribution selectors. It proves consistency after publication, preservation
of unrelated identities, retraction on source correction, stale-source refusal,
and exact-retry preservation for abort-before-commit, lost receipt and delivered
receipt. These are general laws over arbitrary existing worlds/payloads, not
fixtures. They do not yet include all candidate/history/SQL effects or prove
that Rust implements the transitions.

After that aggregate, the user individually approved the PostgreSQL
transaction-atomicity postulate through the native selector. DatabaseTransaction
is the safe contract: committed means the complete proposed publication, aborted
means none, and acknowledgementLost permits either. Completed observations do
not imply liveness or prevent other concurrent transactions. The new safe
LearningPublication.Native theorem requires the application to establish the
complete proposed-write equality before using atomicity to preserve consistency.
Both saved interactive reloads passed without holes/warnings.

Exactly one postulate has now been introduced:
assumptions/Mimir/Assumptions/PostgreSQL.agda: atomicTransactions.
Its approval and exact declaration are recorded in FORMAL-INVENTORY.json.
The formatter postulate remains approved but not yet introduced.
The separate assumptions library includes the safe spec, never the reverse.
This is a local Agda library definition, not system configuration. The assumption
module passed interactive checking (well-formed declaration, not a proof of the
assumption). Isolation audit /tmp/mimir-assumption-isolation-audit-eejzpx6r.json
found the single approved declaration and no safe imports of assumption modules.
Current safe source has 591 modules; the added boundary/connection await the next
aggregate and the assumption module requires its separate final check.

MCP surface inventory now maps all 34 advertised tool names to their Rust
handler branches and Agda ToolCatalog constructors. The sets agree; this does
not establish schema or behavioral equivalence. Complete source-audit receipt:
/tmp/mimir-public-operation-audit-3cBisCxe.log and .exit.

All approved work remains active. No Rust edits/build/install, version change,
production data changes, or system configuration changes were made.

## Revised proof boundary approved and application composition resumed

The user approved the formal proposal to concentrate on Mimir behavior and
correct dependency use. The full rebuild approval persists. Formatter behavior
is the only individually approved postulate; no postulates have been introduced.
No version/deployment/system changes are included in this stage.

FORMAL-INVENTORY.json now classifies all 50 inventoried files and contains eight
application operation groups with requirements, relevant source/formal modules,
and explicit remaining obligations. Every group remains partial with Rust
correspondence open. Six existing dependency records retain their previous
internal-proof obligations as history, but the active obligations are contracts
and application use. Existing symbol mappings and proof modules are retained.

JudgeBatchConfirmation now composes controller results, typed database evidence
and batch completion. Results are indexed by the ORIGINAL selected pins;
collect preserves their order and membership. A complete result implies an
Acknowledgement.Evidence for every originally selected pin, including matching
experience/project/source revision and a newer review revision. This closes a
model-composition gap; it does not claim that the Rust runner already implements
the indexed contract. The module is --safe, was developed through interactive
goal inspection/refinement, and passed saved reload with no goals or warnings.
It is imported by Mimir.agda. Source audit:
/tmp/mimir-formal-source-audit-05gwfi0d.json (589 files, syntactically clean).

Source comparison re-confirmed the existing implementation gaps: judge/mcp.rs
startup does not call learning_capabilities and validates only three nested
review fields; error translation retains detail locally but sends a generic
message to the model. No Rust repair has yet been made.
Evidence: /tmp/mimir-judge-runtime-map-Z2mYStCN.log and .exit.

Aggregate verification passed, exit 0 (52.786 seconds; maximum residency
1,207,292,648 bytes). The first attempt could not reach the Nix daemon in the
sandbox (environment failure, not a type-check failure):
/tmp/mimir-agda-application-boundary-GXPH7DHG.log and .exit.
The passing authorized cached-Nix invocation is retained at
/tmp/mimir-agda-application-boundary-efqXCjUR.log and .exit, with the existing
2 GiB cap. This verifies the current 589-module model, not the Rust runtime.

## Functional prioritization and dependency boundary — user correction

The user approved postulating Rust formatter behavior and requested a critical
classification of Mimir functionality, explicitly rejecting further effort on
standard parts such as Rust floating-point implementation. This supersedes the
previous plan to complete Zmij internals before application work. No postulate
has yet been added. Approval for the formatter is not approval for every other
assumption below. The full Mimir rebuild remains incomplete; harness work stays
deferred and the version remains 2.1.0.

The earlier approach conflated coverage of Mimir's observable behavior with
reimplementation/proof of its dependencies. Float, JSON, Unicode, hash and byte
implementation work displaced the application obligations. Existing proofs are
retained, but their count is not a measure of completion. Further dependency
internals work is not the default next step.

### Classification

A. Mimir-specific semantics: highest proof priority.
- Experience identity, revision checks, correction history and source provenance.
  One incident must not acquire extra evidential weight through retries or dual
  insertion paths. A revised experience must invalidate/recompute old effects.
- Review/candidate ownership, source coverage, project boundaries, atomic graph
  updates and assessment history. Missing evidence remains unresolved; a
  successful retrieval is not a successful observed use.
- Numerical learning rules: distinguish probability, confidence, correctness and
  usefulness; preserve finite domains, weighting, deduplication, bounds and
  explicit unknown values. Prove Mimir's selected computations against standard
  numerical semantics, not a new implementation of the processor's arithmetic.
- Graph propagation, incoming-evidence completeness, cycles, convergence limits,
  decay and counterfactual projection without mutation. Exact-real summation
  commutativity is not a proof of bitwise floating-point order independence.
- Retrieval selection, project/global/working-memory policy, ranking and limits;
  include the actual learning-context assembly and observed-outcome accounting.

B. Application protocols and data integrity: equally important proof targets,
using explicit infrastructure contracts.
- Judge startup/schema compatibility, provider/tool conversation, model budget,
  malformed replies, error feedback, retry/defer/finish and restart. Completion
  requires durable evidence of the intended review, not the model saying Done.
- Persistence: SQL effects, transaction grouping, stale writes, concurrent
  workers, uncertain commits and idempotent reconciliation. Trusting database
  transaction semantics would not establish that Mimir uses transactions right.
- Documents: canonical identity, chunk/embedding association and cardinality,
  dimensions, replacement atomicity and preservation after provider failure.
- MCP/CLI: exposed schemas match handlers, IDs and errors retain meaning, valid
  requests remain usable independently of the new harness.
- Configuration/migrations: precedence, compatibility, preservation of user
  settings and existing records, interruption recovery and version 2.1.0.
- Process/files/notifications: cleanup owns only its resources; bounded deadlines,
  persistent incident state, retry and recovery reporting; no false delivery
  guarantee after an ambiguous external acknowledgement.

C. Standard dependency implementation: contract boundary, not custom proof
projects. Formatter is approved for assumption; the other contracts are
recommendations, not newly approved postulates.
- Rust numeric primitives and standard collections/string operations.
- Serde JSON/TOML encoding and decoding mechanics, Unicode lookup internals.
- SHA/UUID algorithms, TLS/cryptographic primitives.
- PostgreSQL/driver, OS file/process and runtime/network implementation internals.
Each contract must include its domain and failures. Mimir's argument validation,
rounding-sensitive decisions, SQL/query construction, protocol field mapping,
transaction placement and error handling remain application obligations.
Do not assume that every dependency always succeeds or that a model is correct.
Safe proof modules should take explicit contract records as parameters; they
must not import non-safe postulate modules. Unproved witnesses belong only in
separately identified, personally approved assumption modules. This architecture
is a recommendation here; no formal module/import boundary was changed.

D. Empirical adequacy, with formal handling guarantees.
Model judgments, embedding relevance and real-world probability calibration
need observed evaluation. Prove attribution, numeric update rules and handling
of every permitted response. Do not postulate correctness/usefulness of the
judgment or claim it follows from type checking. Platform integration and static
binary behavior also require the authorized verification after implementation.

### Concrete prioritization evidence

crates/core/src/store/learning.rs:304 and :392 already contain transaction,
identity and revision mechanisms; their whole-operation composition, including
corrections and concurrency, is the useful proof target.
crates/core/src/lib.rs:884 deletes stored document data before requesting new
embeddings, then uses zip without a cardinality check at that call site. These
are application-level data-loss/partial-write risks, not embedding-algorithm
proof obligations. This review did not run a new failure trial.
crates/core/src/inference.rs:167 uses bounded iterative updates, floating sums
and convergence thresholds, and returns current values after a warning if the
limit is reached. Claims of exact order independence/convergence need to be
matched to those actual semantics; this inspection does not establish a
specific reachable wrong result.
crates/cli/src/judge/mcp.rs and runner.rs own compatibility, error translation
and review completion. They are higher priority than numeric byte formatting.

Recommended execution order: judge plus learning lifecycle and persistence;
then numerical/graph/retrieval behavior; then remaining document/configuration,
notification and interface composition; then faithful Rust implementation and
verification against the agreed contracts. No feature is silently removed.
Coverage must track public operation -> transitions/invariants -> safe theorem
-> declared assumptions -> Rust implementation -> verification evidence, with
uncovered obligations explicit. Module totals are not coverage percentages.

Inspection evidence (complete logs plus exit receipts):
/tmp/mimir-functional-categorization-S1iE6F6z.log
/tmp/mimir-functional-inventory-full-AUSgdSSL.log
/tmp/mimir-functional-scope-source-eZANNOWE.log
/tmp/mimir-functional-critical-evidence-w5rIvLFV.log
/tmp/mimir-functional-boundary-evidence-GWs01v6Y.log
The inventory print exceeded a tool response; its complete output was recovered
in the inventory-full log before relying on its focused file listing.

Formal checkpoint before this correction: SequentialTableFill,
ExponentTableCounter and ExponentTableInitialization each passed a saved
interactive reload. Fill.run was made opaque with checked runZero/runStep laws
following an aborted 54.404-second expansion of 633 writes. Current source has
588 formal modules; latest passing aggregate is still 585, not 588. No new
aggregate was run for this documentation review. No Rust edit, build, install,
production-data or system-configuration change occurred in this review.

## Signed exponent-table aggregate passed

The saved ExponentStringTable reload passed, and the 585-module aggregate
passed, exit 0: /tmp/mimir-agda-exponent-table-peU8Apkm.log and .exit.
Elapsed 59.710s, maximum residency 1,109,345,192 bytes; cap unchanged.
Source audit /tmp/mimir-formal-source-audit-l079xzl0.json was syntactically
clean. Exact signed entries, index inversion, byte layout, length recovery
and the returned prefix after the five-byte copy are now composed.

SequentialTableFill is the next proof: a general terminating sequence of
single-cell writes to distinct addresses, with exact final values and
preservation at every other address. Instantiating it with the native signed
counter progression and integer-width bounds remains outstanding. The table
proof is not yet the full native formatter or a repaired installed program.
No Rust rewrite, binary installation, version, configuration or DB change.

## Native exponent-table entry and index composition

Saved checks passed for WordByteConcatenation, ExponentTableFields,
ExponentMagnitudeLayout, ExponentTableEntry and ExponentTableIndex.
ExponentStringTable's final lookup proof has closed interactively and its
saved reload is in progress. It connects all 633 indices with exact signed
exponent entries, length recovery and the returned prefix after the f64
five-byte copy. Native loop initialization and caller bounds remain open.

The interval is derived from the pinned Zmij traits.rs MAX_DIGITS10=17 and
Rust f64 MIN_10_EXP=-307, MAX_10_EXP=308. Primary reference:
https://doc.rust-lang.org/std/primitive.f64.html#associatedconstant.MIN_10_EXP
This gives [-324,308], offset 324, 633 entries. Index inversion and the
absolute-magnitude bound are proved for the entire interval, not enumerated
examples. The length field is at bit 48, matching source operations.

Proof-development notes: simultaneous `with` decisions do not automatically
rewrite a second decision hidden behind a newly exposed definition. Retain
their `in` equalities and rewrite the exposed decisions. Nat bounds inside
signed subtraction require explicit endpoints when inversion is blocked.
The vector tabulation theorem is Vec.lookup∘tabulate (not lookup-tabulate).
One save attempt rejected a stale GiveAction because only four of five goals
had closed; its assertions prevented any file mutation. Saved those four,
then completed the actual remaining lookup obligation. Always check the
save exit before reloading and count successful GiveActions, not attempts.

Latest passing aggregate remains 579; subsequent modules await aggregate
verification. No Rust, installed version, service, configuration or DB change.

## Report composition and exponent packing aggregate passed

JudgeReportReadBack passed its saved interactive reload after placing twelve
existing proof bodies in separate checked opaque blocks. The unchanged
statements and proof expressions now compose without the previous heap exit.
The subsequent 579-module aggregate passed, exit 0:
/tmp/mimir-agda-exponent-packing-K5292Cjc.log and .exit.
Elapsed 115.283s, maximum residency 1,339,112,568 bytes; cap remains 2 GiB.
Audit /tmp/mimir-formal-source-audit-60m16ywu.json was syntactically clean.
Both opacity and cache state differ from the failed aggregate, so this is
verification of the resulting invocation, not an isolated performance experiment.

WordByteConcatenation and ExponentTableFields are the subsequent additions:
the latter proves the four native shift/OR fields, byte order and right-shift
length recovery at bit 48 for arbitrary payload/marker/sign/length bytes.
The actual exponent-range/table lookup and returned-string composition are
still unfinished, as are complete floating semantics and the Rust rewrite.
No postulate, heap increase, Rust, version, deployment or data change.

## Exponent proofs checked; aggregate heap failure under investigation

Saved interactive checks passed for DecimalTriplet, ExponentDigits,
WordUnequalFields, WordByteValue, NativeBytePrepend and ExponentAscii.
BitLogic gained general OR commutativity. PackedExponentDigits subsequently
proved exact canonical ASCII prefix and numeric reconstruction of the native
byte-prepending magnitude; WordBytePadding proved high-zero padding identity.
All modules are safe, with no assumptions added. The 577-file source audit
/tmp/mimir-formal-source-audit-bl0kbw4p.json was syntactically clean.

The 577-module aggregate did NOT pass: exit 251, heap exhausted at the
unchanged 2 GiB cap while rechecking JudgeReportReadBack. Complete evidence:
/tmp/mimir-agda-exponent-foundations-Eyy9Gtuh.log and .exit; elapsed 211.340s,
maximum residency 2,108,139,704 bytes. The common BitLogic extension triggered
rechecking of a broad dependency chain. A focused interactive load likewise
exhausted the heap at diagnosticEmission; its complete log and exit receipt
are /tmp/mimir-formal-interactive-record-composition-B5NGLYwA.log and .exit.
This is a verifier-resource failure, not a successful aggregate verification.

The report's twelve existing emission/round-trip proof bodies are being placed
behind checked opaque boundaries to avoid repeated expansion. Their statements
and proof expressions are unchanged. The replacement persistent process logs
to /tmp/mimir-formal-interactive-record-composition-JQfNI46S.log.
This change awaits saved verification; latest passing aggregate remains 571.
Exponent metadata/sign composition, full formatting and the Rust rewrite remain
unfinished. No Rust edits, deployment, data, version or system changes.

## Scientific significand aggregate passed

The 571-module aggregate passed, exit 0:
/tmp/mimir-agda-scientific-significand-RPfnWlnT.log and .exit.
Maximum residency 1,108,309,560 bytes; elapsed 44.081 seconds.
Source audit /tmp/mimir-formal-source-audit-eqwo2sox.json was clean.
NativePointWindow and NativeScientificPrefix connect the two actual point
stores to the overlapping-prefix model. Sse2ScientificSignificand proves
the exact returned bytes and count + (count > 1) length, including one digit.
Exponent appending, sign preservation, complete numeric formatting and the
conversion caller's range obligations remain outstanding.

Proof-engineering finding: case splitting on a transparent conversion length
expanded large memory terms, producing 93,963-character goals. Checked opaque
blocks for the computed count/source and separately for the write/read laws
reduced the relevant goal to 143 characters. The earlier operation was aborted
through Cmd_abort; the process was retained. All bodies remain checked safe
Agda; no postulate or heap-cap change. Reuse explicit abstraction boundaries
before duplicating large computational terms into dependent case splits.

DecimalTriplet is the next component: decimal reconstruction, bounds and
leading-position facts for the exponent table. No Rust, binary, configuration,
version or production data changes. The rebuild remains incomplete.

## Fixed fractional branch aggregate passed

The 568-module aggregate passed, exit 0:
/tmp/mimir-agda-fixed-writers-z8zD3LR8.log and .exit.
Maximum residency 1,108,334,904 bytes; elapsed 62.217 seconds; unchanged cap.
Source audit /tmp/mimir-formal-source-audit-jryu4661.json was syntactically clean.

NativeShiftPrefix proves prefix-only overlapping copying, preservation of the
suffix and exact separator insertion. Sse2FractionalWriter derives the actual
split from the failed integer branch and proves exact source selection,
returned byte vector, decimal-point address and count+1 output length.
All three fixed-format branch memory compositions are now checked under their
explicit significand range and branch premises. Sign handling, decimal-value
semantics, scientific notation and the floating conversion caller remain open.

Further source inspection confirmed exponent-string table enablement is
not(opt_level="s"); Zmij build.rs maps both Cargo s and z optimizations to that
cfg. Cargo.toml here declares no profile opt-level override. This is source
configuration evidence, not forensic evidence of installed binary build flags.
The table stores its length at bit 48 despite its comment saying byte 7;
the specification must follow the actual shift/read operations, not that comment.
No Rust, installed binary, version, service, configuration or data change.

## Zero-padding writer branches checked

The 566-module aggregate passed, exit 0:
/tmp/mimir-agda-fixed-padding-Pg94o77d.log and .exit.
Maximum residency 1,108,335,232 bytes; elapsed 41.452 seconds; unchanged cap.
Source audit /tmp/mimir-formal-source-audit-dezrpdvv.json was syntactically clean.

NativePointStore proves the exact one-cell update and preservation of every
other cell in a read window. NativeWindowAdjacent now also proves decomposition
of arbitrary reads and appending/prepending stores to an already known range.
Sse2IntegerWriter composes conversion stores, overlapping copy, zero fill and
dot insertion, with exact output vector, length and point address.
Sse2NegativeWriter does the same for fixed exponents -(1+e), e <= 4, shifting
digits right before filling and inserting the point. Sign-prefix preservation
and complete floating numeric semantics remain outstanding.

These are byte-level branch proofs with explicit significand preconditions;
they do not yet establish complete f64 formatting or installed Rust behavior.
The next proof composes prefix-only copying with the unchanged suffix for
the fixed fractional branch. No Rust, deployment, data or version change.

## Initialized copy-source aggregate passed

The 563-module aggregate passed, exit 0:
/tmp/mimir-agda-copy-source-LdA74HAE.log and .exit.
Maximum residency 1,108,295,696 bytes; elapsed 44.833 seconds; cap unchanged.
Source audit /tmp/mimir-formal-source-audit-9h_yv4le.json found no missing safe
pragmas, imports or syntactic escape markers; this is not a coverage measure.

Sse2CopySource proves the actual source offset (sign+1), length and endpoint
select only initialized bytes for all both-boolean combinations and all
significands in the explicit [10^14,10^16) precondition. Arbitrary bounded
overlapping moves read back exactly the selected bytes. No initial-memory
initialization assumption is needed. The caller's significand range remains
an outstanding proof, as do full floating formatting and Rust refinement.
Next: decimal-point overwrite and zero-padding composition.
No installed or Rust behavior changed.

## Native store and copy composition in progress

The 553-module writer-layout aggregate passed, exit 0:
/tmp/mimir-agda-writer-layout-sdm7ZVcW.log and .exit.
Maximum residency 1,108,302,744 bytes; elapsed 37.582 seconds.
The subsequent 556-module native-memory aggregate passed, exit 0:
/tmp/mimir-agda-native-memory-rVM9WUP1.log and .exit.
Maximum residency 1,108,201,632 bytes; elapsed 33.991 seconds.
The 2 GiB cap remains unchanged. Counts are not coverage percentages.

The writer-layout proofs include exact first/second leading digit values,
nonzero-position bounds, minimum output length, subtraction without underflow,
and the 24-byte storage endpoints. NativeWindow and NativeWindowCopy prove
bounded reads/writes, preservation outside writes and overlapping snapshot
copies. NativeWordStore relates initialized cells to exact little-endian words.

Additional saved interactive proofs, not yet in a new aggregate receipt:
NativeWindowDisjoint, Sse2SignificandStore, Sse2StoredConversion,
NativeWindowAdjacent, NativeWindowContained and Sse2SignificandInitialized.
They compose the actual returned ASCII word with both stores, exact numeric
read-back, adjacent-store concatenation and initialized contained reads.
Sse2CopySource is being completed to connect the actual computed length and
skip-one source range to initialized copies. All source is safe; no postulate.
Full interactive evidence remains in
/tmp/mimir-formal-interactive-record-composition-B5NGLYwA.log (session 10899).

The conversion caller still must establish 10^14 <= significand < 10^16.
Complete floating conversion/formatting, whole-system composition and Rust
implementation remain unfinished. No Rust edits, build, install, service,
configuration, production data or version change has occurred here.

The advisory interaction record reported an access/update failure. Scope was
restated from explicit conversational authorization, not inferred from the
record. No scope or permission change was made.

## Exact trailing-zero semantics checked

VectorTrimZeros defines the complete trailing-zero cut relation for arbitrary
natural-valued vectors and proves existence plus uniqueness of its length.
Sse2TrailingZeros connects this relation to digits decoded from the actual
ASCII conversion output: the reported length is the unique such cut.
The 548-module aggregate passed, exit 0:
/tmp/mimir-agda-trailing-zeros-6yWiXwiv.log and .exit.
Maximum residency 1,106,933,768 bytes; elapsed 47.465 seconds; cap unchanged.

The next writer obligations are leading-byte handling and minimum length.
Source inspection confirms f64 fixed decimal exponent range -5..15, buffer
size 24, stored BCD size 16 and the skip-one-byte layout. The floating conversion
caller must still establish significand bounds (including the >=10^14 lower
bound); these are not silently assumed for arbitrary f64 inputs.
Sse2DecimalOutput has since added first/second digit quotient laws and passed
saved interactive checking; the next aggregate will include that addition.
No Rust or installed behavior changes.

## Returned ASCII conversion: saved and aggregate verification passed

The 546-module aggregate passed, exit 0:
/tmp/mimir-agda-ascii-conversion-67ESbEX9.log and .exit.
Maximum residency 1,105,502,440 bytes; elapsed 37.280 seconds; cap unchanged.
Audit /tmp/mimir-formal-source-audit-d72itgxu.json is syntactically clean.

Sse2ToDigits64 now composes actual decimal splitting, shuffle, SIMD arithmetic,
ASCII source constant and movemask length. It proves every returned byte is
an ASCII digit, the length is at most 16 and equals the mask extent, and the
integer decoded from the returned ASCII bytes is exactly the original input
for every input below 10^16. VectorChunksCover establishes all-position
coverage; Sse2ByteRegroup ties each byte to its decimal block.

WordSplatValue is generic over width/count/value. Sse2AsciiConstant proves
source constant arithmetic, u64 bound, two-lane layout and OR equivalence.
The prior heap problem was resolved by explicit trans intermediate and cong
endpoints; the failed inference tried to invert a huge partially inferred
product. The corrected refinement completed in 14ms, and saved reload checked.
No cap increase or postulate. Current session 10899, full interactive log
/tmp/mimir-formal-interactive-record-composition-B5NGLYwA.log.

Next: precise trailing-zero cut, then native write/caller and full floating
formatter. The whole Mimir spec/refinement/Rust rewrite remains unfinished.
No Rust edits, build, install, version, configuration or production data change.

## ASCII numeric equality: elaboration heap failure retained

The source-mask layout, generic replication numeric law, and all-byte ASCII
and movemask bounds have been saved from interactive proofs. A later
asciiConstantValue refinement exhausted the unchanged 2 GiB cap in session
7376 while inferring intermediate values for a large numeric equality.
Full log /tmp/mimir-formal-interactive-record-composition-CnLaVuqb.log and .exit
(exit 251). Cmd_abort was requested but did not finish before exhaustion.
The completed sourceProduct law was saved; asciiConstantValue and maskValue
remain holes. The latest passing aggregate is still 540 modules.
Next elaboration supplies explicit trans/cong intermediates instead of
inverting a partially inferred product. No Rust or installed changes.

## Sixteen decimal digits: split, order, input casts and reconstruction checked

Sse2WideRegroup proves the two-64-bit/four-32-bit correspondence. Sse2SplitOrder
proves every shuffle index matches control byte 27, selected decimal blocks,
and their bounds. Official Rust 1.99 intrinsic source was checked for
_MM_SHUFFLE and _mm_shuffle_epi32 lane selection:
https://doc.rust-lang.org/src/core/stdarch/crates/core_arch/src/x86/sse.rs.html#1022-1024
https://doc.rust-lang.org/src/core/stdarch/crates/core_arch/src/x86/sse2.rs.html#1582-1598

Sse2DecimalInput proves quotient/remainder bounds, lossless 32-bit casting,
zero extension and exact input lane values for every number below 10^16.
Sse2DecimalOutput composes the existing instruction proofs: all sixteen
resulting digits are below 10 and their ordered decimal blocks reconstruct
the original number. The bound is an explicit conversion precondition; the
floating formatter caller still must be proved to establish it.

Saved modules report checked=true with no goals, constraints or warnings in
/tmp/mimir-formal-interactive-record-composition-CnLaVuqb.log (session 7376).
The 540-module aggregate passed, exit 0:
/tmp/mimir-agda-decimal-output-ko3dvZwq.log and .exit.
Maximum residency 1,106,979,184 bytes; elapsed 34.997 seconds; 2 GiB cap unchanged.
Audit /tmp/mimir-formal-source-audit-fd7_ek33.json is syntactically clean.
This count is not a coverage percentage. No postulate or Rust change introduced.

Remaining local composition: byte-lane bounds for ASCII and movemask,
source constant layout, trailing-zero behavior, native write/caller conditions.
The complete floating formatter and whole Mimir specification/refinement/Rust
rewrite remain unfinished. No installed behavior changed.

## Ten-thousand split: saved and aggregate verification passed

Correct block-scoped opaque boundaries resolved the repeated expansion issue.
Sse2TenThousands now proves the actual widening multiply/shift/product/add
sequence, exact extraction of both 32-bit fields, and both field bounds for
every selected 64-bit input lane below 100000000. The numeric multiplication
orientation is derived by commutativity; the instruction operand order remains
the one in Zmij. All definitions retain checked bodies under --safe.

Saved receipt /tmp/mimir-ten-thousands-saved-bZWFwyLR.log. The 536-module
aggregate passed, exit 0: /tmp/mimir-agda-ten-thousands-Wnz1JvRE.log and .exit.
Maximum residency 1,105,014,760 bytes; elapsed 40.057 seconds; unchanged cap.
Audit /tmp/mimir-formal-source-audit-46vvrnn9.json is syntactically clean.
Current interactive session 7376, full log
/tmp/mimir-formal-interactive-record-composition-CnLaVuqb.log.

The next obligation is the two-64-bit/four-32-bit lane relationship and the
source shuffle into decimal order. The complete floating formatter and Mimir
rewrite remain unfinished. No Rust or installed behavior changed.

## Corrected opacity scope after repeated proof-elaboration failures

Agda 2.8 documentation confirms abstract visibility is module-scoped: later
abstract definitions in the same module can unfold earlier abstract bodies.
The previously described blocks therefore did not form the intended internal
composition boundaries. This was an error in proof organization, not evidence
that the mathematical law failed or that a larger heap was required.
https://agda.readthedocs.io/en/v2.8.0/language/abstract-definitions.html
https://agda.readthedocs.io/en/v2.8.0/language/opaque-definitions.html

Sse2TenThousands now uses opaque blocks, whose unfolding sets are per-block.
No unfolding clauses expose the earlier source operations. Bodies, complete
signatures and safe checking remain required; no postulate is introduced.
The arithmetic orientation law and productSum refinements were saved.
The whole module and remaining laws still require checking. The current prior
log is /tmp/mimir-formal-interactive-record-composition-fjnUpq7T.log.

## Packing expression orientation: verified arithmetic definition

Session 43199 exhausted the same cap while instantiating the constant-first
multiple law; its general product laws were saved. Full evidence:
/tmp/mimir-formal-interactive-record-composition-0RjWGnxZ.log and .exit.
The cached verifier library directory was read in
/tmp/mimir-agda-library-dir-2C89vkqk.log. Agda.Builtin.Nat defines multiplication
by recursion on its first operand: suc n * m = m + n * m. Fully normalizing
an unknown product with the large coefficient first therefore expands that
coefficient recursively. This explains why the generic laws check but their
concrete form is problematic under normalization.

The numeric multipleAt conclusion now puts the variable quotient first.
constantProductKnownRight derives that orientation with ordinary proved
commutativity; the modeled SSE2 instruction operand order remains unchanged.
The latest persistent verifier log is
/tmp/mimir-formal-interactive-record-composition-fjnUpq7T.log.
These obligations remain unfinished; no new aggregate success is claimed.

## Large packing coefficient: retained heap exit and preserved progress

The opaque shiftedProduct boundary solved the concrete quotient and bound;
those proofs were saved. evenConstantLeftAt also checked and was saved.
The following direct multipleAt composition exhausted the unchanged 2 GiB cap
in session 65338, exit 251. Full evidence:
/tmp/mimir-formal-interactive-record-composition-RxUHfdMv.log and .exit.
The module now adds a generic opaque constantProduct and its exact-result law
before instantiating the large packing coefficient. These new obligations and
the downstream packing laws are unfinished. No aggregate success is claimed
for this module. No Rust or installed-system state changed.

## Concrete 40-bit shift elaboration: second retained heap exit

The generic shiftConstantAt law passed and was saved. Instantiating the
40-bit operation through a transparent quotient still exhausted 2 GiB in
session 16416, exit 251. Evidence:
/tmp/mimir-formal-interactive-record-composition-hCTUXwpb.log and .exit.
The new shiftedProduct abstraction keeps the exact generic source instruction
sequence and exposes its numeric theorem without repeatedly expanding the
concrete bit circuit. Its proof and the downstream obligations remain open.
This is proof evaluation control; it introduces no axiom or semantic change.
The latest passing aggregate remains 535 modules, not this unfinished module.

## Ten-thousand split: retained heap failure, proof obligations still open

The new Sse2TenThousands module saved its literal conversion, constant value,
widening multiplication by a bounded constant, and input-fit proofs. The direct
quotient refinement then exhausted the unchanged 2 GiB heap, exit 251, in
session 87032. Full output and exit receipt:
/tmp/mimir-formal-interactive-record-composition-gV5Wu13Z.log and .exit.
The four successful refinements were saved before restarting the verifier.

A general shiftConstantAt obligation now precedes instantiation of the large
reciprocal. The same persistent-process workflow is resumed in session 16416,
log /tmp/mimir-formal-interactive-record-composition-hCTUXwpb.log. The current
module is incomplete and not yet imported by Mimir.agda. The latest successful
aggregate remains the 535-module BCD checkpoint above/below in this ledger.
No heap increase, postulate, Rust edit or installed-system change occurred.

## Four-field BCD conversion: aggregate verification passed

VectorChunksLookup proves selection by nested indices agrees with selection
after flattening for arbitrary shapes. The Sse2LaneRegroup fineAt law connects
each 16-bit lane to its containing 32-bit field. Sse2BcdRegister combines the
full-register hundreds stage and existing generic tens-stage laws: each field
below 10000 yields exactly its four decimal bytes, every byte is below 10,
and the four bytes reconstruct the field value.

Saved receipt /tmp/mimir-bcd-register-saved-QOkjXKyL.log. The 535-module
aggregate passed, exit 0: /tmp/mimir-agda-bcd-register-zE8HdtKV.log and .exit.
Maximum residency 1,105,008,824 bytes; elapsed 49.748 seconds; cap unchanged.
Audit /tmp/mimir-formal-source-audit-jn91_ug0.json is syntactically clean.
The 64-bit decimal split/shuffle, full floating formatter, complete Mimir
specification and Rust rewrite remain unfinished. No installed behavior changed.

## Full-register hundreds stage: aggregate verification passed

Sse2HundredsRegister proves exact instruction correspondence for every 32-bit
field in the 128-bit register, including the source constant layout, high/low
multiplication, 16-bit shifts/subtraction, 32-bit field shift and OR. For each
field below 10000, its packed quotient/remainder are exact and both below 100.
Saved receipt /tmp/mimir-hundreds-register-saved-jjWYCncJ.log.
The 533-module aggregate passed, exit 0:
/tmp/mimir-agda-hundreds-register-Ygvy9uE5.log and .exit. Maximum residency
1,107,537,112 bytes; elapsed 45.578 seconds; unchanged 2 GiB cap.
This also rechecks the literal abstraction and dependent tens/four-digit laws.
The next unfinished work connects nested lane indices to the tens-stage laws.
No Rust, installed binary, configuration, service or production data changed.

## Full-register proof development: elaboration control

The direct quotient composition was cancelled using Cmd_abort after 108,590ms;
explicit intermediate equalities were also cancelled after 58,812ms and a
literal-boundary attempt after 82,385ms. The interactive process remained alive.
Full evidence is retained in
/tmp/mimir-formal-interactive-record-composition-gV5Wu13Z.log.
No heap cap or checking flag was increased. One native permission-review
call timed out before delivery; its one permitted retry succeeded.

The exact literal conversion and value law in Sse2Hundreds now form an abstract
boundary; that module rechecked. The effective quotient solution was to prove
binaryConstantAt and shiftProductAt for arbitrary constant operands before
instantiating the actual reciprocal. The saved source profile reports 701ms
for shiftProductAt and 154ms for quotientAt; the saved multipleAt proof takes
19,009ms. This is verifier performance evidence, not runtime performance.
The remainder and packing composition are still in progress. No Rust changed.

## Lane regrouping: aggregate verification passed

VectorChunksFusion proves sequence preservation through nested flattening and
map/zip distribution. Sse2LaneRegroup proves that viewing a 128-bit register
as four 32-bit fields or eight 16-bit lanes preserves both unary and binary
lane operations for arbitrary input registers and lane functions.
Saved receipt /tmp/mimir-regroup-binary-saved-0FpSneun.log.
The 532-module aggregate passed, exit 0:
/tmp/mimir-agda-lane-regroup-5JfX5UCM.log and .exit. Maximum residency
1,105,805,576 bytes; elapsed 48.969 seconds; unchanged 2 GiB cap.
Audit /tmp/mimir-formal-source-audit-k031tvus.json is syntactically clean.

The standard library toList-injective includes a length cast: supply the
length equality, both vectors, and the list equality, then use cast-is-id
at equal lengths. Treating it as ordinary same-length injectivity leaves
the wrong proof obligation. No casts or proof conditions were assumed.
The full-register hundreds composition is the next unfinished obligation.

## SSE2 decimal mask and length: aggregate verification passed

WordLeadingZeros proves the high-end scan, extent/leading-zero partition,
subtraction result, and invariance of extent under high zero extension for
all widths and words. SignedPositiveMask proves that signed positive testing
coincides with nonzero testing below the sign threshold, including all decimal
bytes. Sse2DigitMask composes replicated compare results, high-bit extraction,
zero extension and leading-zero subtraction, for arbitrary register byte counts.
Its result equals the extent of the nonzero-byte flags.

Saved receipt /tmp/mimir-digit-mask-saved-0sh0u6iD.log. The 530-module
aggregate passed, exit 0: /tmp/mimir-agda-digit-mask-7ObmK0Ur.log and .exit.
Maximum residency 1,102,413,432 bytes; elapsed 42.460 seconds; unchanged cap.
Audit /tmp/mimir-formal-source-audit-n6awi2p1.json is syntactically clean.
Full register layout and complete native formatter correspondence are still
unfinished, as are the complete Mimir specification and Rust rewrite.

## ASCII digit conversion: saved and aggregate verification passed

AsciiDigitBits proves bytewise OR with 0x30 equals adding 48 for every decimal
digit byte, lands in [48,58), and is injective on those inputs. AsciiDigitLanes
lifts the actual whole-register OR operation to every selected byte and any
register byte count. Saved receipt /tmp/mimir-ascii-saved-GV1rA54U.log.
The 527-module aggregate passed, exit 0:
/tmp/mimir-agda-ascii-digits-2VIAe6FS.log and .exit. Maximum residency
1,108,384,480 bytes; elapsed 42.395 seconds; unchanged 2 GiB cap.
Audit /tmp/mimir-formal-source-audit-f5egp9i5.json is syntactically clean.

Source interpretation for the next proof: the SSE2 movemask/leading-zero
calculation counts through the last nonzero byte in decimal output order;
it supports trimming trailing decimal zeros, not simply counting the input
integer digits. Read the source byte order before giving this field meaning.
Full SIMD assembly, formatter and Mimir rewrite remain incomplete.

## Four-digit composition: saved and aggregate verification passed

The abstract boundary for Sse2Tens resolved repeated expansion while retaining
its definitions and theorem statements. Sse2FourDigits now proves all four
byte values, their decimal bounds, and exact reconstruction for every 32-bit
input below 10000. Saved receipt /tmp/mimir-four-digits-saved-MyCsyaAg.log.
The 525-module aggregate passed with exit 0:
/tmp/mimir-agda-four-digits-QwkqbJmI.log and .exit. Maximum residency
1,106,811,088 bytes, elapsed 44.210 seconds; unchanged 2 GiB cap.
Audit /tmp/mimir-formal-source-audit-hmwuic83.json found no source escape
markers, missing safe options, or missing root imports at that checkpoint.

This closes the six composition obligations described below. It does not
establish the full SIMD formatter, native correspondence, complete Mimir
behavior, or the Rust rewrite. No installed behavior changed.

## Four-digit composition: retained heap failure and proof-boundary work

The saved `Sse2Tens` stage passed before composition:
`/tmp/mimir-sse2-tens-saved-SDLd0QSl.log`. Its laws cover every lane count and
every selected lane below 100. The subsequent `Sse2FourDigits` refinement
finished its three general decimal algebra laws, then exhausted the unchanged
2 GiB cap while elaborating the first composed digit theorem. Session 18132
terminated with exit 251. Full output remains in
`/tmp/mimir-formal-interactive-record-composition-WoJ9KwLX.log` and `.exit`;
focused evidence `/tmp/mimir-four-digit-heap-evidence-O8phgT8B.log`.

The three successful refinements were saved. The remaining six composition
goals are unfinished. The next change retains all `Sse2Tens` executable
definitions and theorem statements, making its already-proved instruction
sequence abstract outside its module to prevent expansion during composition.
No heap increase, postulate, Rust change or semantic weakening is introduced.
Rechecking this proof boundary and completing composition remain required.

## SSE2 hundreds stage: source-aligned aggregate passed

`Sse2Hundreds` composes actual lane high multiplication, right shift, low
multiplication and subtraction. For every 32-bit input below 10000, its
quotient and remainder are exact, below 100, and retain zero in the unused
high half. `Sse2HundredsPacked` follows the source's left-shift/OR order and
proves exact packed fields and their bounds.

Source-alignment correction before the saved/aggregate claim: the first
scaffold repeated DIV100_SIG and 100 in both 16-bit halves. The actual
`Data::splat32` initialization leaves each high half zero. The final model
uses that exact layout and proves the quotient's high half is zero for every
register, without requiring a valid-input bound. Do not infer an intrinsic's
constant-lane layout from the intrinsic's lane width; read the data initializer.
Source evidence remains in `/tmp/mimir-zmij-source-JkE0ECC1.log`.

Saved receipts: `/tmp/mimir-sse2-hundreds-saved-bvksM09N.log` and
`/tmp/mimir-sse2-packed-saved-raasdgzl.log`.
The 523-module aggregate passed, exit 0:
`/tmp/mimir-agda-sse2-hundreds-CQdQpaoe.log` and `.exit`.
Maximum residency 1,114,023,536 bytes; elapsed 37.329 seconds; cap unchanged.
Audit `/tmp/mimir-formal-source-audit-ndrun55g.json` is syntactically clean.
The full formatter, native Rust correspondence, complete Mimir specification
and Rust rewrite remain unfinished; no installed behavior changed.

## Native field placement and two-lane composition: aggregate passed

`WordFieldOverlay` proves native shift/OR field placement, including canonical
zero extension from a numeric half-word bound. `WordLanePair` proves exact
two-lane extraction, reconstruction and scalar-operation composition.
For the canonical representation proof, use the general two-element vector
eta law and `flattenChunks`; direct simultaneous with-abstraction on the view
and its reconstruction exposed normalized split projections instead of retaining
the intended lane names. No theorem statement was changed.

Saved receipts: `/tmp/mimir-field-overlay-saved-PaxnQuJR.log` and
`/tmp/mimir-lane-pair-saved-7k2Qj5Jj.log`.
The 521-module aggregate passed, exit 0:
`/tmp/mimir-agda-field-pair-MDaKFGhU.log` and `.exit`.
Maximum residency 1,119,766,408 bytes; elapsed 34.856 seconds; cap unchanged.
Audit `/tmp/mimir-formal-source-audit-6ttcfg09.json` is syntactically clean.

Default-target evidence: cached `rustc --print cfg --target
x86_64-unknown-linux-musl` reports little-endian, SSE/SSE2, and no SSE4.1.
Receipt `/tmp/mimir-static-target-cfg-oyvjsJfT.log`, exit 0. The scoped checkout
search found no target-feature/target-cpu/RUSTFLAGS overrides:
`/tmp/mimir-target-feature-config-jiRS48Ur.log` (search exit 1: no matches).
This establishes compiler defaults, not a forensic claim about flags used for
an already-installed binary. No binary was built or installed.

## Borrow subtraction and bitwise field composition: aggregate passed

`WordSubtraction` implements ripple-borrow subtraction and proves conservation
for every input word and incoming borrow. `WordSubtractionValue` derives total
wrapping semantics and ordinary subtraction under a no-underflow condition.
`WordLaneArithmetic` inherits both results for each selected lane.

`WordDisjointOr` reuses `BitMaskClear.Clear` to prove OR equals addition for
non-overlapping bits, with a fitting sum. Zero-padded adjacent fields concatenate
exactly. `WordLaneLogic` proves whole-register bitwise operations agree with
the lane view for every shape, operation and register; no endian agreement
is assumed by the caller.

Saved receipts: `/tmp/mimir-word-subtraction-saved-7ziugtYX.log`,
`/tmp/mimir-subtraction-value-saved-oH5Hxbmc.log`,
`/tmp/mimir-lane-subtraction-saved-1sQXREpy.log`,
`/tmp/mimir-disjoint-or-saved-a5O9r2Ke.log`, and
`/tmp/mimir-lane-logic-saved-BURKLDSW.log`.
The 519-module aggregate passed, exit 0:
`/tmp/mimir-agda-subtract-or-a94UkDpA.log` and `.exit`.
Maximum residency 1,125,077,944 bytes; elapsed 34.113 seconds; cap unchanged.
Audit `/tmp/mimir-formal-source-audit-pefpis1_.json` is syntactically clean.
Full formatter composition, native Rust correspondence, the complete Mimir
specification and Rust rewrite remain unfinished.

## Lane arithmetic and complete shift semantics: aggregate passed

`WordLanes` reuses `VectorChunks` for exact unary, binary and shuffle views.
Every selected output lane is proved equal to the corresponding scalar
operation, with least-significant-lane-first order explicit. Identity and
composition are proved for all shapes and register values.
`WordLaneArithmetic` proves per-lane wrapping addition, low/high multiplication,
both shifts and widening multiplication of the even-numbered half lanes.
`WordShiftLeft` supplies multiplication-modulo semantics for every shift count,
including counts that discard the complete word.

Saved receipts: `/tmp/mimir-word-lanes-saved-UCtsF2O4.log`,
`/tmp/mimir-left-shift-saved-OCsTnr4P.log`, and
`/tmp/mimir-lane-shifts-saved-c5AWPc0f.log`.
The 515-module aggregate passed, exit 0:
`/tmp/mimir-agda-lane-arithmetic-wepqPErW.log` and `.exit`.
Maximum residency 1,142,306,784 bytes; elapsed 40.283 seconds; cap unchanged.
The full formatter, native Rust correspondence, complete Mimir specification
and Rust rewrite remain unfinished; installed Mimir is unchanged.

## Reciprocal packing at actual lane sizes: aggregate passed

`ReciprocalPacking` substitutes a proved fast quotient into both packing
orders and preserves exact field extraction, result bounds, subtraction safety
and intermediate bounds. `DecimalPackedChunks` discharges those premises for
the formatter's 10/100/10,000 divisors and 8/16/32-bit fields. Its laws quantify
over every relevant input, with scaled inputs and subtrahends fitting their
16/32/64-bit enclosing words.

Saved receipts: `/tmp/mimir-reciprocal-packing-saved-16diJVdy.log` and
`/tmp/mimir-packed-chunks-saved-mS9wVOTb.log`.
The 512-module aggregate passed, exit 0:
`/tmp/mimir-agda-packed-chunks-QbPsGI2r.log` and `.exit`.
Maximum residency 1,142,354,144 bytes; elapsed 37.962 seconds; cap unchanged.
Reuse `VectorChunks` for SIMD views: it already proves flatten/chunk inverses
for every width, count and element type. `WordBytes` builds byte order on it.
The full formatter, native correspondence, complete specification and Rust
rewrite remain unfinished.

## Decimal chunks and intermediate packing bounds: aggregate passed

`RoundedReciprocal` derives the exact error of floor(base/divisor)+1 for
arbitrary positive bases and divisors, removing a caller-supplied identity.
`DecimalChunkReciprocal` applies it to the pinned formatter's division by 100
and 10,000 over all inputs below 10,000 and 100,000,000 respectively. Quotients
and remainders are exact and each resulting decimal chunk is in range.

`DecimalPacking` proves the formatter's forward and reverse lane-packing
identities for arbitrary fitting divisors and binary lane radices. Extraction
recovers each original quotient/remainder. Reversed subtraction cannot
underflow. It separately proves final-result, multiplicand, scaled-input,
subtrahend, and coefficient bounds under the stated fitting conditions;
final-result boundedness alone is not used to claim safe intermediates.

Saved receipts: `/tmp/mimir-rounded-reciprocal-saved-LiN4jnva.log`,
`/tmp/mimir-decimal-chunk-saved-huGOfSTx.log`, and
`/tmp/mimir-packing-intermediate-saved-TGnzQ7fN.log`.
The 510-module aggregate passed, exit 0:
`/tmp/mimir-agda-decimal-chunks-VqLaLDGD.log` and `.exit`.
Maximum residency 1,133,626,528 bytes; elapsed 38.041 seconds; cap unchanged.
The complete specification, native implementation refinement and Rust rewrite
remain unfinished. No installed binaries, version or production data changed.

## Word-level reciprocal and final digit: aggregate passed

`WordProductBridge` proves both conversion round trips between fixed-width bit
vectors and bounded arithmetic words, exact two-word encoding, high/low
extraction, multiplication with an added word, and the upper two-word product.
The encoding premises are discharged internally for every input vector.

`WordDivTen` composes the native half-radix/divide-by-five constant with wide
multiplication and high-word extraction. For every positive bit width divisible
by four, all input words below the corresponding quarter-radix have the exact
quotient by ten. The constant fits its word. Final-digit subtraction cannot
underflow, yields a value below ten, and reconstructs the original input with
the computed quotient. The quarter-radix bound is itself expressed and proved
as the corresponding binary power.

Saved receipts: `/tmp/mimir-word-product-saved-d1P3FZM5.log` and
`/tmp/mimir-divten-remainder-saved-t5F6BePd.log`.
The 507-module aggregate passed, exit 0:
`/tmp/mimir-agda-word-divten-s1eySBax.log` and `.exit`.
Maximum residency 1,121,003,984 bytes; elapsed 52.541 seconds; cap unchanged.
Audit `/tmp/mimir-formal-source-audit-cf_zw9ln.json` is syntactically clean.
These are model composition results; native Rust refinement, the complete
formatter, the full Mimir specification and the Rust rewrite remain unfinished.

## Reciprocal division and bit shifts: aggregate passed

`ReciprocalDivision` proves exact scaled reciprocal division for every positive
divisor and base when the accumulated rounding error remains below the base.
`PowerTenReciprocal` derives the reciprocal and error of four for every binary
radix whose positive bit width is divisible by four. Its quotient law covers
all inputs below one quarter of that radix. It also proves the equivalence of
the half-radix/divide-by-five constant used in Zmij. The general proof avoids
enumerating machine inputs or expanding a 64-bit bound.

`WordShiftValue` connects every bit-vector right shift, including shifts beyond
the vector width, to division by the corresponding power of two. It proves
exact quotient/remainder laws for high/low splitting and reconciles the two
existing power representations.
Saved receipts: `/tmp/mimir-reciprocal-saved-oy6UlWO1.log`, the successful
PowerTenReciprocal reload in the retained interactive log, and
`/tmp/mimir-word-shift-saved-lEMOQwzA.log`.

The 505-module aggregate passed, exit 0:
`/tmp/mimir-agda-reciprocal-shift-cPHwojSj.log` and `.exit`.
Maximum residency 1,122,035,920 bytes; elapsed 35.618 seconds; cap unchanged.
Audit `/tmp/mimir-formal-source-audit-w370p5ey.json` is syntactically clean.
The full formatter, native correspondence, complete specification and Rust
rewrite remain unfinished. Installed Mimir remains unchanged.

## Wide multiplication and carry: aggregate passed

`WideProduct` proves exact two-word multiplication with an additional word,
including the bound needed to prevent overflow. `WordCarry` proves that a
wrapped sum's comparison with its first operand detects exactly its carry.
`WideProductHigh` composes these into the upper two words of a two-word by
one-word product and proves that the final high-word addition cannot overflow.
All laws quantify over arbitrary positive radices and all bounded operands.
These are arithmetic model laws; native shifts, casts and formatter composition
remain unfinished.

Saved receipts: `/tmp/mimir-wide-product-saved-i7Tqin9M.log`,
`/tmp/mimir-word-carry-saved-7BV4Cuza.log`, and
`/tmp/mimir-wide-high-saved-E2kzGNvv.log`.
The 502-module aggregate passed, exit 0:
`/tmp/mimir-agda-wide-product-4exvh0nI.log` and `.exit`.
Maximum residency 1,120,255,432 bytes; elapsed 36.189 seconds; cap unchanged.
Audit `/tmp/mimir-formal-source-audit-8ufo93xm.json` found no missing safe
options, root imports or escape markers. This is not a coverage percentage.
The complete specification and Rust rewrite remain unfinished.

## Floating JSON output: pinned implementation identified

`Cargo.lock` contains both Ryu and Zmij, but `serde_json 1.0.154` depends on
`zmij 1.0.23`, and its `Formatter::write_f64` calls
`zmij::Buffer::format_finite`. Do not infer the active formatter merely from
the presence of another formatting crate in the lockfile.
Receipts: `/tmp/mimir-numeric-codec-dependencies-bzvZw67D.log`,
`/tmp/mimir-serde-json-formatting-AaaRrPWS.log`, and complete Zmij source
`/tmp/mimir-zmij-source-JkE0ECC1.log`.
The existing `JsonCompactRecords` codec explicitly excludes floating values;
it must not be presented as a complete outgoing MCP serializer. Wide-product,
decimal selection, digit emission and native correspondence remain open.

## MCP transport and interruption composition: aggregate passed

`McpClientTransport` replaces request-level send/read operations with the
existing byte-send and byte-framing protocols. Every completed execution
projects to an actual request-protocol execution, retaining the complete
handler traces. Successful sends carry exact-byte and flush receipts;
successful reads retain the framing trace, capacity bound and no-LF body law.
Serialization and diagnostic conversion remain explicit, unfinished boundaries.

`EffectsPrefixComposition` decomposes interrupted binds into a partial first
operation or a completed first operation followed by a partial continuation.
`EffectsHandlingPrefix` gives both reflection and reconstruction of interrupted
handler executions. Only completed handlers contribute high-level receipts;
the active handler and exact residual computation remain represented.
The MCP instance inherits the existing bound of 66 abstract request events
for completed and interrupted executions. This is not a wall-clock bound or
a claim about model requests.

Saved receipts: `/tmp/mimir-client-interrupted-saved-S6O10HXD.log` and
`/tmp/mimir-handling-prefix-saved-Qqshf7J3.log`.
`McpClientLineDiagnostic` models the existing read messages and the exact order
of lossy stderr decoding, control removal, 512-scalar truncation and empty-detail
selection. It proves scalar/byte bounds, order preservation and valid Unicode
for every byte input. Saved: `/tmp/mimir-client-line-diagnostic-saved-6TRR2lb4.log`.
Native source receipt: `/tmp/mimir-mcp-client-source-8Vou7cdC.log`.

The 499-module aggregate passed, exit 0:
`/tmp/mimir-agda-client-transport-prefix-lMxLo238.log` and `.exit`.
Audit `/tmp/mimir-formal-source-audit-31pbc5wl.json` is syntactically clean.
Maximum residency 1,090,579,656 bytes; elapsed 34.350 seconds; cap unchanged.
The full specification, native correspondence and Rust rewrite remain incomplete.
No installed binaries, versions, system configuration or production data changed.

## Typed-member whitespace and error composition: aggregate passed

`SerdeSpacedMemberReadBack` connects the nested ignored-value grammar to the
actual typed member reader. Unknown fields leave all known slots unchanged;
known fields use the selected productive reader. Both permit arbitrary legal
whitespace before the colon, and ignored values permit all modeled internal
whitespace. Saved receipt: `/tmp/mimir-spaced-member-saved-vCSZJa0S.log`.

`SerdeFailure` keeps the original diagnostic cursor separate from cleanup.
Its general laws prove incompatibility with successful return and preservation
through mapping, sequencing, productive-reader binding and finalization.
`SerdeMemberFailure` composes those laws through key parsing, colon parsing,
known/unknown value parsing and field selection. A duplicate known field is
refused before its colon or value is read. Saved receipts:
`/tmp/mimir-serde-failure-saved-UDUnoz57.log` and
`/tmp/mimir-member-failure-saved-1RbrmQFN.log`.

Proof-development finding: directly reusing an indexed error receipt across a
change of result carrier fails (`First != Second`); copying its projections
also failed during elaboration. Splitting the receipt into its constructor
fields and rebuilding it proved the unchanged first-error property, without
changing its statement or adding an assumption. `Cmd_give WithoutForce`
exposed the type error hidden by `Cmd_refine`'s generic `Cannot refine` message.
Diagnostic receipt: `/tmp/mimir-serde-failure-direct-error-fkWZgaKx.log`.

The aggregate passed, exit 0:
`/tmp/mimir-agda-typed-member-errors-dhKuTpv4.log` and `.exit`.
Maximum residency 1,072,375,264 bytes; elapsed 48.269 seconds; cap unchanged.
This is model composition, not native Rust equivalence. The full specification
and Rust rewrite remain unfinished; installed Mimir is unchanged.

## Ignored-reader rejection propagation: aggregate passed

`JsonIgnoredFailure` proves that prefixing whitespace or successful transitions
cannot turn a failure into success or change its reason, current/peek position
mode, or unread suffix. Exact suffix and input reconstruction determine the
consumed prefix uniquely. The actual runner inherits failures at the end of
any successful path. General local laws cover EOF, unquoted keys, missing
commas, trailing array/object separators, and string/numeric fault mapping.
These are quantified laws, not selected malformed-input fixtures.

Saved receipt: `/tmp/mimir-failure-scalar-saved-EyZ5uEHp.log`.
The aggregate including this module passed, exit 0:
`/tmp/mimir-agda-ignored-rejection-0OiuNU1N.log` and `.exit`.
Maximum residency 1,080,573,832 bytes; elapsed 31.826 seconds; cap unchanged.
This does not yet establish complete native-parser equivalence. No Rust or
installed Mimir changes. Typed-member whitespace composition is in progress.

## Nested ignored values with whitespace: aggregate passed

`JsonIgnoredWhitespacePath` proves that each legal whitespace byte prefixes
the first actual transition and preserves its continuation. Terminal states
are deliberately excluded: they do not consume the unread suffix.
`JsonIgnoredKeyWhitespace` composes ignored-string parsing and the real colon
reader, including arbitrary legal whitespace before the colon.
`JsonIgnoredSpacedSyntax` and `JsonIgnoredSpacedReadBack.complete` cover finite
nested arrays and objects with whitespace around values, commas, keys, colons
and closing delimiters. The proof composes actual runner transitions, retains
the exact suffix, and passes the structural termination checker.

Saved receipts: `/tmp/mimir-spaced-syntax-saved-f2vUl04x.log` and
`/tmp/mimir-spaced-readback-saved-lT6TWfY9.log`.
The first readback reload exposed a layout error in saved interactive `let`
expressions; moving `let` to its own indented line repaired source layout.
No theorem or transition was weakened.

The 491-module aggregate passed, exit 0:
`/tmp/mimir-agda-spaced-ignored-values-77X8g0ev.log` and `.exit`.
Syntactic audit: `/tmp/mimir-formal-source-audit-2db5h0_w.json`.
Maximum residency 1,078,836,512 bytes; elapsed 35.306 seconds; cap unchanged.
This is a successful-input theorem, not a complete error/native-equivalence
proof or a coverage percentage. Rejection behavior, other Mimir components,
global refinement and the Rust rewrite remain unfinished.

## Nested compact ignored-value theorem: saved check passed

`JsonIgnoredContainerPath` saved-checks opening/closing delimiters, commas,
first-member transitions and ignored object keys, for arbitrary parent frames:
`/tmp/mimir-container-path-saved-FLbJgmEn.log`.
`JsonIgnoredValueSyntax` defines finite recursive values with the full numeric
lexeme syntax and the actual permissive ignored-string grammar.
`JsonIgnoredValueReadBack.complete` proves that the actual runner consumes each
such compact spelling and leaves exactly the supplied stopped suffix. Its
mutual structural recursion and all goals passed saved checking, with no
termination escape: `/tmp/mimir-nested-value-saved-NaALstNB.log`.

The spelling flag `first` and protocol flag `acceptComma` have opposite
meanings. Their correspondence is explicitly `acceptComma = not first`;
passing the same boolean would make first-member/comma composition wrong.
This was caught while inspecting the general proof goals, before Rust work.

The 487-module aggregate passed, exit 0:
`/tmp/mimir-agda-nested-ignored-values-6m5l5sLU.log` and `.exit`.
Audit `/tmp/mimir-formal-source-audit-uoppn492.json` is syntactically clean.
Maximum residency 1,094,695,704 bytes; elapsed 31.322 seconds; cap unchanged.
Inter-token whitespace and error-side/native
equivalence remain separate open obligations; compact completeness is not
being substituted for complete JSON behavior or whole-Mimir correctness.

## Nested ignored-value paths in progress

`JsonIgnoredPath` saved-checks successful transition segments, composition,
continuation into actual runner executions, and exact suffix preservation.
Receipt: `/tmp/mimir-ignored-path-saved-Jiyp4084.log`.
Numeric dispatch has been generalized to arbitrary enclosing frames and saved
checked (`/tmp/mimir-number-frames-saved-WgcbHGge.log`).
`JsonIgnoredScalarPath` saved-checks null, booleans, ignored strings and numeric
lexemes returning to the same arbitrary frame stack, with the suffix retained:
`/tmp/mimir-scalar-path-saved-mD9LhDpm.log`.
These finished modules are root-imported. Container delimiter/key proofs are
currently under development; this group is not yet aggregate-verified and
does not yet establish arbitrary nested-container completeness.

## Ignored numeric byte values: aggregate passed

`JsonIgnoredNumberWireReadBack.ignored` proves success of the actual ignored
value runner for any byte input whose character view spells a numeric lexeme
with a stopped suffix. The proof derives the numeric start from that spelling,
covers the minus and all digit dispatch cases for arbitrary trailing input,
transports the character parser's success to bytes, and composes the actual
runner execution. It introduces no numeric bounds or conversion, and preserves
the exact byte suffix. Saved receipt:
`/tmp/mimir-number-ignored-saved-9HlNHCI1.log`.

The 482-module aggregate passed, exit 0:
`/tmp/mimir-agda-ignored-number-bytes-zh5vlkPk.log` and `.exit`.
Audit `/tmp/mimir-formal-source-audit-b0taamch.json` is syntactically clean.
Maximum residency 1,115,042,144 bytes, elapsed 38.487 seconds; cap unchanged.
Nested-container skip completeness is next. Error-side/native equivalence,
the wider system specification and the Rust rewrite remain incomplete.

## Ignored-number character grammar: aggregate passed

`JsonIgnoredNumberReadBack` composes the actual digit scanner, leading-zero
guard, optional minus, fractional part, and signed exponent transitions.
`JsonIgnoredNumberSyntax.complete` proves successful scanning of every lexeme
in an independent structured numeric grammar, with an exact stopped suffix.
Digit lists have arbitrary finite lengths; the grammar does not bound or
evaluate significands or exponents. Saved syntax receipt:
`/tmp/mimir-number-syntax-saved-6zcSSZ9T.log`.

The 481-module aggregate passed, exit 0:
`/tmp/mimir-agda-ignored-number-syntax-Mb0nyZRb.log` and `.exit`.
Audit `/tmp/mimir-formal-source-audit-cce0_c8m.json` is syntactically clean.
Maximum residency 1,071,582,056 bytes; elapsed 33.749 seconds; unchanged 2 GiB
heap cap. Byte transport and ignored-value control integration are next;
the character theorem alone does not establish those boundaries, error-side
equivalence, native correspondence or whole-Mimir correctness. Rust rewrite
and production changes remain unstarted.

## Unknown-field and scalar-skip proof group: aggregate passed

The aggregate now passes with exit 0:
`/tmp/mimir-agda-unknown-string-readback-ZzuWylGV.log` and `.exit`.
Maximum residency 1,338,702,616 bytes, elapsed 52.639 seconds, unchanged 2 GiB
heap cap. Audit `/tmp/mimir-formal-source-audit-6cccd6n5.json` covers 479 formal
files, all safe and root-imported, with no source escape markers. This is not
a behavioral coverage percentage.

`JsonIgnoredReadBack` proves exact suffix preservation for null, both boolean
values and every valid body of the existing ignored-string grammar, using
the actual executable scanner and its execution determinism. The string proof
retains that grammar's intentional lack of decoded UTF-8/surrogate validation.
Saved receipt: `/tmp/mimir-ignored-string-saved-receipt-rG6hwJiC.log`.
Unknown object members preserve all known slots conditional on the actual
payload skip; scalar laws now discharge some of those payload obligations.
General numeric and nested-container skip completeness remain open. No claim
of complete parser/native equivalence, whole-Mimir correctness or Rust repair.

## Unknown-field extension and renewed aggregate heap failure

`SerdeUnknownMemberReadBack` proves unchanged known-field slots for an unknown
key whenever the actual ignored reader succeeds, with its exact trailing input.
`SerdeObjectReadBack.Written.skipped` lifts this into mixed complete records;
`SerdeRawEmission.weaken` now preserves the new case. All three saved modules
checked successfully; the last receipt is
`/tmp/mimir-raw-emission-saved-MU4m8n4p.log`.

The subsequent aggregate **failed**, exit 251, at `JudgeReportReadBack`:
`/tmp/mimir-agda-unknown-member-lGXOWlvs.log` and `.exit`. Maximum residency
2,108,314,400 bytes exceeded the unchanged 2 GiB cap. The previous successful
aggregate does not cover these edits. The report proof is being decomposed
further with a typed reference-field helper, keeping its theorem unchanged.
That split also exhausted the interactive checker in `written`, exit 251;
the full BPOszkWb log and its `.exit` preserve this second failure. The checker
was restarted into `/tmp/mimir-formal-interactive-record-composition-qKfhh9LZ.log`
with the same cap. Proof goals are being isolated to avoid attributing an
unverified benefit to the decomposition.
The reference helper and incremental tail refinements succeeded interactively,
but their combined saved expression also exhausted the heap in `written`
(qKfhh9LZ log, exit 251). Each optional prefix field now has an explicit
intermediate lemma under development. The replacement persistent checker log
is `/tmp/mimir-formal-interactive-record-composition-CILXsqDw.log`.
The separated saved check reached `diagnosticEmission` and exhausted the heap
there (CILXsqDw, exit 251). Its implicit type/schema/reader/value/support
arguments have now been made explicit for the next interactive verification.
Current checker: `/tmp/mimir-formal-interactive-record-composition-WoJ9KwLX.log`.
The saved report check now **passes**, `checked=true`, no goals/errors:
`/tmp/mimir-report-explicit-saved-receipt-ReC6DHaK.log`. It took 62.655 seconds;
`diagnosticEmission` took 14.449 seconds and `written` 291 ms. Explicit
arguments and the earlier typed decomposition are both present; this is not
an isolated causal benchmark. The theorem, accepted domain and 2 GiB cap are
unchanged. Aggregate verification of this revision is still pending.

`JsonIgnoredReadBack` additionally has a saved successful interactive check for
general execution-to-read receipts and null/boolean preservation of any suffix.
It is not yet aggregate-verified. Its source contains no postulates; complete
interactive output remains in the BPOszkWb log. Arbitrary ignored payloads,
noncanonical parser behavior and all wider obligations remain incomplete.
No Rust, installed binary, configuration, version or production data changed.

## Guarded read receipt preserves the written record

`JudgeParsedReadBack` proves that successful executable decoding returns a
loaded receipt containing the same raw guarded read, and transfers the original
filesystem execution without adding or replacing events. `JudgeRecordReadBack`
instantiates this for all three typed writer variants and concrete named readers.
Its explicit premise is that the guarded read bytes equal the concrete writer
bytes. Metadata/user/guard provenance is retained by equality of the complete
raw read receipt; this does not assert filesystem write/read coherence without
an actual matching read observation.

The saved checks and 477-module aggregate passed, exit 0:
`/tmp/mimir-agda-guarded-record-readback-Mml39XpZ.log` and `.exit`.
Audit `/tmp/mimir-formal-source-audit-ldswgs6l.json` is syntactically clean.
Maximum residency 1,076,266,992 bytes, total memory 1807 MiB, elapsed 48.760
seconds, unchanged 2 GiB cap. Saved concrete receipt summary:
`/tmp/mimir-record-receipt-saved-state-zxuDdlSx.log`.
Unknown-field compatibility and independent noncanonical acceptance/error
equivalence remain open, as do native correspondence, other full-system
components and Rust implementation. No Rust or production changes.

## Complete canonical judge-file byte read-back

All nine persisted record families now have concrete raw-byte round-trip proofs:
source, deferred review, failure diagnostic, confirmed review, event, report,
trace, incident and diagnostics container. `SerdeDocumentReadBack` composes a
successful child read with the actual end-of-document check;
`JudgeStateDocumentReadBack` instantiates all three persisted names at the
existing depth allowance 127 and proves exact canonical-byte read-back with
empty remainder. Existing Unicode validity, native numeric bounds and the
explicit `sizeMaximum ≤ u64Maximum` premise are retained. No extra domain
restrictions, postulates or behavior changes were introduced.

The 475-module aggregate passed with exit 0:
`/tmp/mimir-agda-judge-file-readback-BD7i6NFG.log` and `.exit`.
Audit `/tmp/mimir-formal-source-audit-29drmvzf.json` reports all safe flags and
root imports, with no source escape markers. Maximum residency 917,936,528
bytes, total memory 1777 MiB, elapsed 41.600 seconds, unchanged 2 GiB heap cap.
Saved incident and file-boundary reload receipts are
`/tmp/mimir-incident-saved-state-C7zVTzY9.log` and
`/tmp/mimir-file-readback-saved-state-OWTwzaeH.log`; full proof interactions are
retained in the BPOszkWb log below.

Next is composition with guarded filesystem-read receipts: an actual raw read
of the serializer bytes must return the same record with unchanged metadata
and event provenance. This does not assume that arbitrary filesystem replies
equal a prior write. Independent acceptance/error equivalence, native
correspondence, full-Mimir coverage and the Rust implementation remain open.
No Rust, binaries, version, migrations, service/configuration or production
data changes accompany these proofs.

## Report elaboration heap limit and typed decomposition

The saved report reload exhausted the unchanged 2 GiB heap while checking
`written`, exit 251. The full retained log is
`/tmp/mimir-formal-interactive-record-composition-yVNcPmdk.log` and `.exit`;
focused evidence is `/tmp/mimir-report-heap-evidence-PWWgqAEX.log`.
The earlier interactive closure of its goals is not a successful saved-source
verification. No Rust source or runtime behavior changed.

The combined fifteen-field emission proof is being split into explicitly typed
ending, counter and prefix proofs. These retain the exact existing schema,
readers, values and serializer witnesses. The final round-trip statement is
unchanged. This aims to bound elaboration of implicit arguments; the cause has
not been isolated from accumulated checker state. The crashed process was
restarted with the same 2 GiB cap and compacting GC, logging to
`/tmp/mimir-formal-interactive-record-composition-BPOszkWb.log`.
The decomposed report proof subsequently passed its saved-source reload:
checked=true, no open goals or diagnostics, recorded in
`/tmp/mimir-report-decomposed-saved-state-Z7uOWz5Z.log` and the full BPOszkWb
interactive log. Reload time was 62.161 seconds, with `written` taking 48.493
seconds. The module is now root-imported; a new aggregate check is still due.
This verifies the decomposed theorem under the cap, without isolating the
effect of decomposition from the fresh process.

## Nested traces, diagnostics and report composition in progress

`SerdeObjectVectorReadBack`, `JudgeTraceReadBack`, and
`JudgeDiagnosticsReadBack` passed saved-source interactive checks and are root
imports. Evidence remains in the full interactive log named below; saved
trace/diagnostics check summaries are
`/tmp/mimir-trace-saved-state-l2FK3NGj.log` and
`/tmp/mimir-diagnostics-saved-state-80tInhfQ.log`.
The generic vector bridge proves equality between uniform and witnessed array
support rather than assuming serializer proof arguments coincide.
Trace and diagnostics proofs quantify over all admitted records and arbitrary
suffixes, accounting explicitly for nested reader depth. Aggregate verification
of these newer additions is pending.

The report proof closed all six interactive goals and was saved; its final
saved-source reload is still running. Its emitted-field composition took about
80 seconds interactively, under the unchanged heap cap. This is checker time,
not an estimate of total task completion. Incident and file-boundary proofs are
unfinished scaffolds, not completed modules. The last complete aggregate is the
468-module snapshot recorded below. Full behavioral coverage, native
correspondence and faithful Rust implementation are still unfinished.

## Optional raw fields and complete event read-back

Saved interactive checks passed for `SerdeRawEmission`, its builders,
`SerdeOptionCodecReadBack`, and `JudgeEventReadBack`. All are imported by the
aggregate. The 468-module aggregate, also including the subsequently completed
`SerdeValidatedVectorReadBack`, passed with exit 0:
`/tmp/mimir-agda-event-vector-readback-BkDIz24U.log` and `.exit`.
Source audit `/tmp/mimir-formal-source-audit-hetingoc.json` found no missing safe
flags, root imports or source escapes. Maximum residency 917,886,256 bytes,
total memory 1718 MiB, elapsed 59.794 seconds, unchanged 2 GiB heap limit.
The full interactive evidence is
`/tmp/mimir-formal-interactive-record-composition-yVNcPmdk.log`;
the saved event reload reported checked=true with no goals or diagnostics
(`/tmp/mimir-event-reload-state-W429ZwwP.log`).

Raw emission connects schema-ordered emitted/omitted fields to actual member
reader results and default resolution, retaining schema uniqueness. Optional
codec proofs cover non-null canonical numbers, strings and objects. Builder
variants keep serializer validity separate from numeric reader bounds; their
support witnesses match the existing serializers, including uniform optional
numeric fields. The event theorem covers every existing optional-field
combination, valid text and bounded number, with arbitrary trailing bytes.
It uses the same native-width premise as source records and the existing raw
event reader and compact writer. No specification behavior was weakened.

`SerdeValidatedVectorReadBack` is saved, checked and aggregate-imported. It
composes arbitrary arrays while retaining separate All witnesses for writer
validity and reader admission, element order and arbitrary trailing bytes.
Report, incident, trace and diagnostics-container read-back,
full-system specification closure, native correspondence and Rust work remain
open. No Rust, version, installed binary, configuration or production-data edits.

## Confirmed, source-failure and diagnostic raw-byte round trips

Saved and checked `JudgeConfirmedReadBack`, `JudgeSourceReadBack` and
`JudgeDiagnosticReadBack`. Each theorem uses the exact concrete compact writer
and corresponding raw reader, for every admitted record and arbitrary suffix.
All schemas use positive recursion allowance. Text is quantified over the
existing Unicode-valid Rust domain, with no extra text restrictions.

Source offsets use the explicit native-width premise
`sizeMaximum ≤ u64Maximum`, in addition to the existing per-field size bounds.
The numeric lexer is u64-bounded, so a theorem over an arbitrary larger model
maximum would be false. This does not restrict the actual 64-bit native domain;
instantiating platform bounds and proving native correspondence remains required.
Confirmed and diagnostic timestamps use exactly their existing u64 bounds.

The 463-module aggregate passed, exit 0:
`/tmp/mimir-agda-flat-record-readback-giaSfNEI.log` and `.exit`.
Audit: `/tmp/mimir-formal-source-audit-pq76cyu0.json` (safe, complete import graph,
no source escapes). Same 2 GiB cap and compacting GC; maximum residency
917,939,280 bytes, total memory 1679 MiB, elapsed 50.741 seconds.
The remaining report/incident/event/trace/diagnostics-container byte round trips
still require optional/default and nested-record composition. Full-system
specification closure and faithful Rust implementation are not complete.
No Rust, version, installation, configuration or production-data changes.

## Complete canonical-object composition and deferred-record read-back

`JsonObjectReadBack` proves compact object spelling with arbitrary valid names,
values, fields and suffixes. `SerdeObjectReadBack.Written` retains selected field
indices, absence before assignment and value-reader evidence. Its induction and
parser theorem compose all members, default resolution and delimiters into an
actual modeled record read. This retains the exact field/reader obligations;
it does not assume the final parser succeeds.

`JudgeDeferredReadBack` constructs those obligations for every deferred-review
record whose revision is in the native i64 range. The theorem uses the exact
`Wire.deferred`/`Serialize.deferred` bytes and the raw `P.deferred` reader, with
arbitrary suffix and any positive recursion allowance. UUID identity and signed
revision are preserved. The new general `mapProductive` law allowed the final
composition to stay abstract. Its interactive refinement completed in 5.056s;
the saved proof checked without goals/metas. The earlier heap interruption is
resolved for this proof, without increasing the cap or weakening a theorem.
Fresh process state and compacting GC changed too, so allocation causality was
not independently isolated.

Aggregate passed (exit 0), 460 imported safe modules:
`/tmp/mimir-agda-deferred-readback-5waggwYs.log` and `.exit`.
Audit: `/tmp/mimir-formal-source-audit-3rpu6mli.json`.
Maximum residency 1,072,123,320 bytes, total 1810 MiB, elapsed 45.873s.
A subsequent confirmed-record scaffold is outside this receipt and unfinished.
Other concrete judge records, full behavioral coverage and Rust remain open.
No postulates, Rust changes, installed changes or production data writes.

## Deferred-record composition heap interruption (2026-10-29 local)

The persistent interactive checker exited 251 at its 2 GiB heap cap while
refining the final `JudgeDeferredReadBack.roundTrip` term using a result-level
`Compose.map`. Full evidence is retained in
`/tmp/mimir-formal-interactive-record-bounds-BRgyV89W.log`.
The preceding five successful interactive refinements were saved; the final
round-trip obligation remained open. This is not a successful record proof.

The relevant definitional boundary is `Flow.Productive.result
(Flow.mapProductive change parsed)`: it cannot reduce until the productive
parser is exposed. Applying only the result-level mapping law to a concrete
record reader may force that expansion. A general productive-mapping law is
being proved first so the concrete reader can stay abstract during composition.
This is a proof-engineering diagnosis, not an isolated measurement of the
allocation cause; the long-lived checker also retained earlier proof state.
The replacement interactive process keeps the 2 GiB cap and enables compacting
GC already used for aggregate checks. No specification law or Rust behavior
was weakened or changed.

## Concrete UUID lists and object-member composition (2026-10-29 local)

`JsonArrayReadBack` connects compact serializer bytes to the list-reader
composition. `JudgeUUIDVectorReadBack` instantiates this for arbitrary UUID lists,
any suffix, and any positive recursion allowance in the actual modeled judge
UUID-vector reader. No selected-ID bounds or UUID version restrictions are added.

`SerdeMemberReadBack` proves canonical known-member parsing, including arbitrary
Unicode-valid names, exact key/value boundaries, colon consumption and assignment
to an absent selected slot. `SerdeMapReadBack` composes member reads through the
map loop, default resolution and object-container closure. These are general
composition laws; complete concrete judge-record raw-byte round trips are still
being built. `SerdeReadBackComposition.andThen` supplies the shared bind law.

All saved modules checked without goals/metas. The 457-module aggregate passed
with exit 0: `/tmp/mimir-agda-member-readback-DBGEHgZK.log` and `.exit`.
Source audit: `/tmp/mimir-formal-source-audit-luzf2khn.json`.
The unchanged 2 GiB heap cap with compacting GC gave 1,007,774,664 bytes maximum
residency, 1799 MiB total memory, and 56.570 seconds elapsed.
Two subsequent object-serialization/composition modules were scaffolded while
that aggregate ran; they were not imported by it and are not covered by this
receipt. No Rust or installed/production changes were made.

## Optional and vector read-back composition (2026-10-29 local)

`SerdeOptionReadBack` proves null and successful non-null child reads preserve
their exact suffix. `SerdeLoopReadBack` composes successful transitions using
the existing execution completeness theorem. `SerdeVectorReadBack` proves
arbitrary-length encoded lists return all values in source order, including
comma handling, the opening/closing delimiters, and the recursion allowance.
Its explicit premises require the element encoder to start with a non-space,
non-closing byte and the element parser to round-trip before list delimiters.
`SerdeReadBackComposition.container` composes successful container finalization.
Applying these general laws to the concrete compact judge record encoders is
still ongoing; no whole-record raw-byte round-trip is claimed here.

All saved modules checked interactively without remaining goals/metas.
Aggregate check passed, exit 0:
`/tmp/mimir-agda-vector-readback-gZwsGefq.log` and `.exit`.
Source audit: `/tmp/mimir-formal-source-audit-k5g3i4io.json` (453 modules,
all safe, all imported, no source escape markers). The check retained the
2 GiB cap and compacting GC, used 921,205,560 bytes maximum residency,
1756 MiB total memory, and 55.011 seconds elapsed. No postulates, Rust edits,
version changes, installed changes, or production database changes.

## Signed scalar read-back proof (2026-10-29 local)

The saved `JudgeSignedReadBack` theorem now proves actual modeled raw-reader
read-back for every in-range signed 64-bit integer, including both endpoints,
with an arbitrary numeric-stopped suffix. It derives unsigned magnitude bounds
from the signed range and proves signed wrapping at arbitrary bit widths.
The positive and negative paths compose character parsing, byte transport,
number dispatch, whitespace handling, and scalar validation. No postulates or
Rust changes were introduced. Whole-record composition remains unfinished.

Aggregate `agda Mimir.agda +RTS -M2G -c -s -RTS` passed (exit 0).
Complete output: `/tmp/mimir-agda-signed-readback-glCkIx9T.log` and `.exit`.
Source audit: `/tmp/mimir-formal-source-audit-xjm4a2yq.json` (450 modules).
The aggregate used 981,440,048 bytes maximum residency, 1827 MiB total memory,
and 107.566 seconds elapsed. These checks establish model typing and the stated
laws, not native Rust refinement or full-system coverage.

# Complete Mimir formalization and Rust correspondence

Status: active, incomplete. User authorization on 2026-10-29 covers the complete
formal specification followed by faithful Rust implementation, without further
stage approvals. Harness work is deferred in agent-harness/docs/HARNESS-DEFERRED.md.
Version remains 2.1.0. Production installation is not evidence of correspondence.

## Binding development constraints

Complete the behavioral specification before Rust changes. Do not use a
patch/test/fail/patch development cycle for Mimir. Proof development uses the
persistent Agda interaction process. Every ordinary module must use --safe.
No postulate is authorized; any proposed postulate requires the user's personal
approval and a separate module. Parameterized laws must expose their premises;
an assumed result must never be described as proved. Existing source changes
in this checkout are retained, including the earlier 2.1.0 learning extension.

## Completeness criteria

Every component needs its input language, persistent and transient state,
admitted and refused transitions, emitted effects, failure and recovery behavior,
compatibility rules, and quantified properties. Every Rust branch and protocol
operation needs a corresponding specification obligation. A named constructor
alone is not behavioral coverage. A checked abstract model alone is not Rust
refinement. External participants are represented by explicit input events,
including malformed replies, failure, timeout, cancellation, and lost receipts.

## Coverage ledger

All rows remain incomplete until their detailed operation ledger, definitions,
proofs, and correspondence have been checked. Existing modules are starting
material, not declarations that a row is complete.

| Component | Rust source | Existing formal material | Required completion |
|---|---|---|---|
| Values and numeric semantics | core/graph.rs, inference.rs, assessment.rs | Types, Inference, Beta, Assessment | All domains, finite-float conversion, rounding, overflow, bounds, aggregation |
| Graph, provenance, retrieval and intervention | core/lib.rs, store.rs | Graph, Evidence, Session | Every operation, ranking/ties, paging, scope, edge effects, deletion, evidence and concurrent updates |
| Documents and embeddings | core/documents.rs, embed.rs | Documents | Parsing/chunk identity, backend protocols, dimensions, batching, failure and consistency |
| Configuration and credentials | core/config.rs, password.rs, tls.rs | Connection | Complete grammars, precedence, file policy, TLS negotiation and failure paths |
| Database and migrations | core/db.rs, store.rs, store/learning.rs, migrations | LearningContracts (partial) | SQL effects, atomicity boundaries, all migrations, locks, retries, commit ambiguity and recovery |
| Learning and source records | core/learning.rs, learning_sources.rs | Learning, LearningContracts | Complete schemas, source selection/quotations, coverage, identities, revisions, all validation/refusal outcomes |
| Assessments | core/assessment.rs, store/learning.rs | Assessment | Evidence eligibility, independent contributions, retraction, history, all numerical and scope rules |
| MCP | mcp/main.rs, learning.rs | Startup, Graph (partial) | Framing, JSON grammar, schemas, every tool, initialization, errors, notifications, disconnection |
| CLI and hooks | cli/main.rs | Session, Startup (partial) | Every command/subcommand/flag, configuration creation, exit/output protocols, hook delivery |
| Judge orchestration | cli/judge/runner.rs, mod.rs, state.rs | Judge (partial) | All states, selection, budgets, retries, revisions, model/tool interleavings, durable records, recovery |
| Judge adapters | cli/judge/api.rs, harness.rs, mcp.rs, process.rs, evidence.rs | Judge (partial) | Wire protocols, parsing, tool schemas, source feedback, subprocess lifetime, cancellation, partial output |
| Notifications | notifications/*, cli/judge/notification.rs, digest.rs | Judge (partial) | Outbox, SMTP, OAuth, retries, deduplication, digest, expiry, failure, persistence |
| Composition and executable correspondence | all four crates | none complete | Global state/effects, all interleavings, refinement relations, complete operation mapping |

## Known failure to cover

The source integration admitted JSON-encoded legacy source text. The judge can
return decoded quotations that violate literal source containment. The harness
text-v2 repair applied only prospectively. Retained failures recorded at
2026-10-28T23:33 and 23:36 contain legacy sources; one has since been reviewed,
the latter remains unreviewed in the observed snapshot. Current Codex MCP
connection also uses an older schema; a fresh installed 2.1.0 process reads the
typed contract. These are separate observations. No further Mimir repair has
been implemented in this formalization stage.

## Checked additions during the rebuild

Additional checked aggregate (275 formal files including the root):
`/tmp/mimir-agda-provider-concrete-Fua6507N.log`, exit 0; audit
`/tmp/mimir-provider-concrete-audit-e8vxvnxf.json` reports every formal module
imported, safe flags present, and no forbidden escape markers. This is model
verification, not Rust refinement. The later handshake additions require a new
aggregate check.

Earlier aggregate receipt (267 formal files including the root):
`/tmp/mimir-agda-judge-provider-j5ApEL3z.log`, exit 0. The import/safe/hole audit
is `/tmp/mimir-judge-provider-audit-1ymubu5a.json`, with no missing imports,
unsafe modules or unfinished markers. The earlier audit
`/tmp/mimir-judge-provider-audit-g1_q62we.json` used an overly narrow import
pattern and mistook identifier-final question marks/comments for holes; it is
retained as failed audit evidence, not a specification failure.
Earlier successful intermediate aggregate receipts not previously entered here:
`/tmp/mimir-agda-parser-safety-glCh39RI.log` (226 files),
`/tmp/mimir-agda-checksum-composed-7K6nYdjd.log` (249 files), and
`/tmp/mimir-agda-checksum-parser-4HUM67DX.log` (255 files), all exit 0.
After the server restart no Agda process remained. Proof work resumed in
`/tmp/mimir-formal-interactive-resumed-hOmyJ6RX.log` using the same 2 GiB heap
limit; the preceding successful interactive receipts remain in the composition
log. No Rust or installed-binary change accompanies these checks.

These are checked specification components, not a completion claim for any
coverage-ledger row and not a proof of correspondence with Rust.

- `WinnowPosition`, `WinnowLines`: source-compatible byte/scalar position
  calculation, EOF clamping, nonempty diagnostic slices and existence of the
  selected line for every input and offset. Complete formatted error output and
  native machine arithmetic correspondence remain open.
- `UnicodeCursorBytes`: exact admitted Unicode encoding, byte-offset bounds,
  cursor conservation and strict-decode/re-encode preservation.
- `MigrationFileParsing`, `MigrationLoadContract`, `MigrationFileRuntime`:
  strict UTF-8 embedded-content loading, concrete migration parsing/checksums,
  first-failure decomposition, and a composed proof that load failure returns
  without connection, locking, import or SQL effects. File selection/sorting is
  still outside the ordered-file input contract.
- `JudgeControllerAccounting`: exhaustive accounting for the actual review
  controller transition function, exact controller preservation under the
  accounting wrapper, conserved budgets for arbitrary finite input sequences,
  unchanged account on stop, and retention of the existing batch account when
  starting another selected revision. This connects the earlier independent
  controller and accounting models; provider wire composition remains open.
- `JudgeTraceBarrier`: exhaustive transition and arbitrary finite-run proofs
  that each model/tool/receipt request resumes a stored continuation on a trace
  acknowledgement and has an earlier matching trace request in the run. Stop,
  trace failure, unsolicited replies and late replies are included. This is a
  controller protocol theorem, not a claim that an external filesystem lies
  outside the modeled failure domain.
- `SelectiveTraversal`, `ProviderResponse`, `ProviderCollection`,
  `ProviderReplay`: three provider response envelope decoders, ordered call
  extraction with independent soundness/completeness, duplicate-ID refusal,
  bounded admitted calls and preservation of failed arguments under their
  original ID/name. All accepted OpenAI replay items, Anthropic content blocks,
  and chat assistant messages retain their original values, including reasoning
  and signature fields. Argument JSON decoding remains an explicit normal-return
  parameter at this boundary; panic/nonreturn and byte-level transport composition
  remain open. The structured fault messages are not yet an exact reproduction
  of every legacy anyhow string. OpenAI/Anthropic permit empty function names at
  envelope decoding, whereas chat rejects them; the existing queue model has a
  stronger nonempty-name admission condition and needs an explicit adapter.
  Source receipt: `/tmp/mimir-provider-wire-u1vqz63x.log` (exit 0).
- `SerdeNumericOrdinary`, `JsonOrdinary`: general proofs over every input that
  disabled overflow checks cannot produce the modeled native arithmetic-panic
  branch, composed through numeric transport, atoms, nested containers and the
  complete decoder. This is a profile-specific parser theorem, not a claim
  about allocation failures or arbitrary compiler configurations.
- `JsonDiagnosticCode`, `JsonControlDiagnostics`, `JsonDiagnostics`: ordinary
  JSON failures have renderable reasons under either overflow profile; prefix
  consumption and cleanup retain the first diagnostic. Native panics remain
  separate. `JsonReleaseDocument` combines complete input consumption, concrete
  schema conversion, nonpanic outcomes and diagnostic evidence.
- `ProviderArguments` instantiates the response, replay and queue-admission
  contracts with the concrete admitted-Unicode/UTF-8/JSON decoder. Its syntax
  faults preserve the exact parser message and location; no supplied decoder
  remains in this instance. Invalid non-scalar Agda text is explicitly refused,
  and admitted Rust text is proved to select the concrete parsing path.
- `ProviderQueueAdmission` proves accepted response envelopes satisfy the
  corresponding queue policy. `ProviderQueue` now makes name policy explicit:
  chat requires nonempty names; OpenAI/Anthropic defer name interpretation to
  tool decoding. The previous strict `step` remains a specialization, with its
  existing laws intact, and budget laws also quantify over both policies.
  Empty names are neither renamed nor lost. This closes the admission mismatch
  noted above without changing Rust. Exact legacy fault-string correspondence,
  outgoing request serialization and full controller/provider composition remain.

- `SourceText`: total source splitting, independent bounds predicate,
  selection completeness, exact reconstruction, decidable literal containment.
- `SourceSchema`: source-record field constraints, UTF-8 byte limits,
  timestamp constraints, reference uniqueness and count limit.
- `SourceProtocol`: revision-bound exact source selection with Unicode-scalar
  offsets; actor and provenance preservation; valid legacy literal quotations
  remain accepted. Internal scalar offsets avoid splitting UTF-8 characters.
- `SourceReview`: coverage-reference validation, quotations, actor identity,
  fresh extracted IDs, assessment-or-unresolved accounting, legacy/source
  contribution exclusion. Numeric and full item schemas are separate conjuncts.
- `Password`: an independent escape grammar, parser soundness, completeness and
  determinism; line lookup with first-match soundness/completeness; explicit
  credential precedence and file failures.
- `ConfigurationIO`: configuration creation state/effect protocol, exclusive
  creation, partial-write failure, absorbing completion, successful-write
  requirement, source-independent error rendering. TOML/schema mapping remains.
- `Validation`: error-bearing decisions with proof of validity or invalidity,
  first-failure preservation, field paths, identical model/diagnostic faults.
- `Text`: Unicode White_Space set and UTF-8 byte-length accounting.
- `Binary64`: exact rational interpretation of finite binary64 input bits,
  including subnormals, with explicit nonfinite inputs. Rounded arithmetic is
  deliberately not treated as exact rational arithmetic.
- `NumericValidation`, `LearningSchema`: numeric axis and interval validation,
  learning item and prediction constraints, evidence/reference requirements,
  observed-source requirements, and zero weight for unresolved/unobserved axes.
- `ToolCatalog`: current MCP tool-name enumeration only; per-tool behavior and
  wire protocols remain open.
- `CommitProtocol`: definite refusal versus lost receipt, durable acknowledgement,
  exact-retry idempotence and stale-source refusal, connected to the revision model.
- `JudgeReview`: selected-review control transitions, trace barrier, bounded
  correction requests, exact fault feedback, read-after-uncertain-commit, and
  independent database confirmation. Confirmed results now carry checked
  identity/project/source/review evidence rather than a bare acknowledgement.
  Queued calls have distinct transitions which do not charge provider budget.
  Batch selection, candidate deferral, global composition and termination remain open.
- `Framing`: bounded byte buffers, exact completed frame emission, partial-frame
  rejection on EOF/timeout, absorbing transport failure.
- `RpcReply`: JSON-RPC version/identifier handling, bounded notifications,
  preserved application errors, and nonwrapping request-ID allocation.
- `Migrations`: the nine embedded migration identities/dependencies and lifecycle,
  rollback paths, explicit commit uncertainty and atomic schema/receipt publication.
  Concrete SQL semantics, dependency validation and legacy receipt import remain open.
- `DocumentStore`: chunk/vector shape and count alignment, coupled projections,
  idempotent clearing, partition counts, preservation of other documents,
  and atomic replacement outcomes. Physical SQL refinement remains open.
- `Markdown`: raw LF/CRLF line splitting, current heading syntax, stack-based
  parent selection, chunk construction, preserved metadata and nonempty output.
  The allocation supply is explicit; random UUID uniqueness is not postulated.
- `EmbeddingBatch`: index-based response alignment with exact shape, no silent
  truncation, every input position consumed exactly once, and completeness for
  the independently stated alignment relation. Scalar decoding remains separate.
- `Dyadic`: a general bridge between the rational interpretation of finite
  binary64 words and their common integer scale, including subnormals and sign.
  Threshold, base and exponent remain symbolic throughout the proof, avoiding
  normalization of enormous concrete powers. This does not prove rounded arithmetic.
- `Unsigned`, `ConfigurationValues`, `ConfigurationInput`, `ConfigurationPath`:
  bounded decimal input grammar, ordered overrides, default port bound,
  backend-setting interactions, and environment path precedence. TOML decoding
  and native-path evaluation remain separate obligations.
- `TLS`: option pairing/refusal, negotiation events, verification policy
  preservation over every reachable state, no plaintext for required TLS modes,
  and no downgrade after a handshake failure. Certificate parsing/building and
  transport-library correspondence remain open.
- `Collections`, `LearningCandidates`, `ReviewSchema`: constructive collection
  decisions, candidate schemas and belief-only references, canonical contradiction
  keys, assessment-key uniqueness, and typed/legacy overlap exclusion. These
  establish structural validation, not serialized-size or database validity.
- `ExperienceSchema`: experience fields and source/evidence correspondence;
  composition of extraction integrity and source-indexed assessment validation.
- `OptionalTraversal`: successful traversal retains cardinality, establishes
  output predicates, and preserves inputs when every element is unchanged.
- `ReviewResolution`: checked candidate resolution, exact contribution counts,
  all assessment targets resolved, quotation/coverage preservation, and
  revalidation of the resulting review before it can be prepared for storage.
  Candidate aliases are not assumed distinct. Registry and transaction protocols
  remain separate obligations.
- `Retention`, `LearningCorrections`: source-record and extracted-quotation
  retention across successive corrections; mutable interpretation fields do not
  change quotation identity. The same exact source tuples survive each step.
- `CandidateRegistry`: exact declaration reuse, retired-identity refusal,
  checked allocation collisions, old-entry preservation and abort preservation.
  Atomic graph/table publication and SQL correspondence remain open.
- `ItemOwners`: successful reservation establishes the requested owner;
  existing provenance is immutable, other item slots are unchanged, and a
  repeated identical claim is idempotent.
- `JudgeAccounting`: separate request/attempt conservation and bounds over finite
  traces, including concatenated batch traces.
- `ProviderQueue`: call/result order, per-call correlation, batch call validation,
  absorbing termination, bounded accounting carried by every returned state,
  and no provider request or provider-fuel consumption while draining a queue.
- `JudgeTools`, `JudgeQueueAdapter`: exact allowed operation names and arguments,
  complete accepted-name decoding, typed read/review classification, and queued
  controller dispatch without a provider charge. The complete composed run,
  wire-provider payloads and subprocess lifecycle remain open.
- `JudgeAcknowledgement`, `JudgeReceipt`: database evidence carried into the
  controller, precise malformed-observation diagnostics, stop precedence and
  late-receipt absorption.
- `ReviewObservation`: exact identity/project/revision acknowledgement rules,
  pending-batch validation, and revision-sensitive deferred-review predicates.
  Snapshot admission checks positive source revision, nonnegative review and
  acknowledgement counters, i64 bounds, and acknowledgement no later than source.
- `SemanticKey`, `LearningKeys`, `LearningRevision`: finite numeric comparison
  keys with literal text preserved, explicit experience/review projections, and
  typed-key retry laws. These keys do not serialize or rewrite stored payloads.
- `RevisionBounds`: admitted review transitions preserve a parameterized storage
  bound; the concrete adapter uses the signed-i64 maximum.
- `LearningTargets`: exact project ownership and persistent-memory requirements
  for every target, including explicit refusal of global/missing targets.
- `DecimalLexer`, `ParsedPart`, `JsonNumber`, `JsonNumberCompleteness`: maximal
  ASCII digit prefixes, exact fragment composition, JSON numeric grammar,
  parser soundness and completeness. Floating conversion and full JSON framing
  remain separate, open obligations.
- `JsonObjects`, `StructuredValue`, `RecordDecoding`: last-write object
  normalization versus typed duplicate rejection, unknown-field policies,
  typed integer bounds, required/defaulted/nullable fields, indexed array
  failures, and preservation of valid decoded values through validation.
- `SourceWire`, `CandidateWire`: concrete field names and enum spellings,
  canonical structured encoding/decoding round trips for arbitrary records,
  exact source text preservation, and acceptance of every valid encoded record.
  These operate after tokenization; raw UTF-8/JSON and numeric conversion remain.
- `ReviewAdmission`: composition of source integrity, correction retention,
  materialization/revalidation, exact-project durable targets and evidence.
  Admitted reviews preserve assessment count and have no unresolved target.
  Allocation, ownership reservation, CAS, wire-size and physical publication
  are explicitly separate obligations, not covered by this semantic admission.
- `FaultWire`: exact indexed diagnostic path, validation code and message
  structured round trips. Faults store character sequences; literal helper
  constructors avoid assuming a primitive String/List inverse theorem.
- `McpErrors`, `JudgeErrorAdapter`: compatible code/message envelopes with typed
  refusal details, exact corrective feedback, distinct candidate failures, and
  receipt inspection for unclassified review errors. A legacy error code alone
  establishes neither invalid arguments nor absence of effects. Server-side
  no-change certification and client-side claims remain explicitly distinct.
- `BatchReport`: exact selected-batch receipt accounting; completion requires
  acknowledgement evidence for every selected revision, not model prose.
- `DeferredReviews`, `PendingSelection`, `CandidateDeferral`: fresh-read evidence
  for every retained or removed deferral, pending/excluded selection checks,
  and the existing conflict/error eligibility distinctions. Deferral persistence
  requires the same unreviewed source revision still to exist in scope.
- `NotificationIncident`, `Saturating`: duplicate failure retry preservation,
  recovery only after a delivered failure, and bounded nonwrapping deadlines.
- `Effects`: exact request/reply traces, interrupted prefixes, deterministic
  results for a fixed trace, composition, and quantified effect-count bounds.
- `NotificationDelivery`: build, reserve, SMTP and final-save protocol. Every
  eligible run reaching SMTP has a durable reservation receipt; reporting sent
  requires SMTP acceptance and a durable final receipt. Uncertain writes stop
  the invocation. Crash/restart composition and physical adapters remain open.
- `AtomicFile`: exclusive creation, write, file sync, rename and directory sync
  receipts; cleanup requires successful temporary-file creation. Directory-sync
  failure after rename is uncertain, not an unchanged-file result. Abstract
  frame preservation and acknowledged recovery do not prove OS correspondence.
- `CharacterRules`, `OAuthCache`: C0/C1 controls, bounded token language,
  ASCII case-insensitive bearer type, cache identity/token validation, forced
  refresh, rotation retention, bounded expiry and save-before-use. Raw JSON,
  identity hashing and HTTP correspondence remain open.
- `SMTPAuth`: exact authentication recovery decisions, at most two SMTP attempts
  over both complete and interrupted runs, and no refresh after a rejected
  freshly refreshed token or a failed cache invalidation.
- `BoundedBytes`, `OAuthHTTP`: exact streamed-byte retention, independent checks
  of declared and actual size, terminal oversized/transport/timeout handling,
  HTTP response classification, and decoding only after complete bounded input.
  Token-response semantic validation follows decoding. Request formation,
  raw JSON decoding and concrete HTTP-library correspondence remain open.
- `TextOrder`, `DigestDelivery`: existing day-shape/body limits, disabled and
  already-covered handling, hourly retry reservation, unchanged cursor before
  delivery, exact success receipts, and monotonic cursor advancement. The
  scalar/UTF-8 ordering bridge remains a codec obligation.
- `NotificationSchema`: source/code alphabets, incident key, summary and details
  validation, including the LF exception for details and indexed diagnostics.
- `TrimLaws`: equivalence between nonblank text and nonempty trimmed text for
  arbitrary scalar sequences, with reversal and concatenation laws.
- `TextFields`, `EmailAddress`, `WhitespaceWords`: maximal delimiter splitting,
  full input retention, sound/complete simple-address admission, and whole-word
  scope recognition with both boundaries. These preserve the application's
  existing address rule; they do not introduce an RFC mailbox parser.
- `NotificationConfig`: disabled-config semantics, host/port/TLS/address and
  timing constraints, password/OAuth/anonymous credential exclusions, Google
  scope and tenant restrictions, Microsoft tenant and whole-word scope rules.
  Detailed credential fault rendering and TOML/wire correspondence remain open.
- `UnsignedWire`, `OAuthWire`: bounded integer/byte conversion and complete
  structured record round trips for OAuth cache and refresh replies, including
  optional tokens and distinct unknown-field policies. Raw JSON remains open.
- `Radix`, `Bits`: arbitrary-width positional bounds, uniqueness and both
  conversion round trips, with opaque checked conversion boundaries for byte
  instantiation. These do not use the standard library's foreign Word8 module.
- `UTF8Byte`, `UTF8Packet`, `UTF8Text`: exhaustive byte-prefix classification,
  exact continuation assembly, canonical scalar checks, packet completeness,
  full-sequence byte reconstruction and acceptance of every encoded scalar
  sequence. The recursion bound comes from consumed bytes; there is no exposed
  arbitrary-fuel failure. Numeric construction and the Char-model bridge are
  covered by the following modules; full JSON string parsing remains open.
  UTF-8 encoding rules were checked against RFC 3629 sections 3–4:
  <https://www.rfc-editor.org/rfc/rfc3629.html>.
- `UnicodeScalar`, `UnicodeText`: construction from every admitted scalar
  number and numeric round trip; a checked bridge to the earlier Char model,
  scalar-sequence uniqueness and exact text preservation. Scalar admission is
  explicit. No primitive Char/fromNat inverse is postulated. UTF-8 byte-length
  correspondence and ordering correspondence remain open. JSON strings and
  escaping are covered by the modules below, with Rust correspondence still open.

- `UTF16Escape`: exhaustive first-unit classification, valid surrogate-pair
  acceptance, rejection soundness and exact scalar arithmetic. Every admitted
  pair constructs canonical UTF-8 through the scalar encoder. No surrogate
  or external-character inverse is postulated.
- `HexEscape`: both ASCII letter cases, four-byte reconstruction, exact numeric
  unit interpretation and parser completeness for arbitrary digits and suffixes.
  Failure evidence distinguishes truncation from a proven non-hex byte; consumed
  length follows serde_json 1.0.154 SliceRead.
- `JsonEscape`, `JsonEscapeParser`: independent short/BMP/surrogate-pair grammar,
  exact numeric interpretation, complete escape parsing and uniqueness of the
  admitted spelling and suffix. General acceptance and preservation proofs cover
  arbitrary valid escapes and remaining bytes.
- `ByteCursor`: parser failures retain consumed bytes and remaining input with
  exact reconstruction; offsets are proved to remain within supplied input.
- `JsonString`, `JsonStringParser`: lexical bodies with mixed literal bytes and
  escapes, input-length-bounded scanning, final assembled UTF-8 validation,
  completeness and decoded scalar preservation. Validation happens at the closing
  quote, matching the inspected serde_json precedence: earlier escape/control
  failure wins over invalid raw UTF-8. Source line/column rendering, Rust adapter
  correspondence and surrounding JSON values remain open.
  `UnicodeScalar` now also proves irrelevance of its validity evidence; decoded
  bytes cannot change merely because a different validity proof was supplied.

- `JsonLiteral`, `JsonStringWriter`: actual UTF-8 byte values are connected to
  JSON literal admission; serialization uses the standard short escapes,
  lowercase hexadecimal for other C0 controls, and verbatim UTF-8 otherwise.
  Every scalar sequence has a checked serializer/parser round trip preserving
  all numeric scalar values and the remaining input. `HexEscape.byteUnitPrefix`
  proves the two leading zero digits for byte-valued hexadecimal escapes.
- `ByteText`: reversible byte/Latin-1-character representation for connecting
  lexical parsers. The primitive character-number equation is proved by finite
  decision over all 256 byte values, not postulated. This is not a UTF-8 decoder
  and does not assume an inverse for arbitrary Unicode character construction.

- `BytePart`, `JsonNumberWire`, `JsonNumberSuffix`: exact lexical-prefix
  transport to bytes; number acceptance at end of input and before all JSON
  whitespace, comma, array-end and object-end delimiters; trailing bytes are
  preserved. Lexical numeric admission does not establish rounded numeric
  conversion, which remains unfinished.

- `JsonWhitespace`: exactly the four JSON whitespace bytes, with maximal-prefix
  reconstruction, stopping evidence and general scan completeness.
- `JsonSurface`: lossless recursive grammar retaining formatting, member order,
  duplicate keys and the default nesting-depth admission rule. The complete
  recursive decoder is composed below; correspondence with this independent
  grammar remains unfinished.

- `RoundQuotient`: nearest-even integer rounding for every nonnegative
  numerator and positive denominator, including global nearestness against
  every candidate integer, exact multiples, the half-unit error bound, and
  preservation of integral lower/upper bounds.
  Finite-exponent quantization is now composed below; complete runtime numeric correspondence remains unfinished.

- `BinaryGrid`: symbolic fraction-width proofs of strict ordering within
  exponents, across exponent boundaries and across arbitrary exponent gaps;
  equal nonnegative grid values have the same exponent and fraction. This
  does not identify signed zero representations or prove hardware arithmetic.

- `Significand`: value-preserving normalization of rounded significands,
  one-step exponent carry and subnormal-to-normal promotion, with bounded
  exponent outcomes. Input interval bounds come from `RoundQuotient`.
- `ExponentRange`: constructive first-interval selection by exact rational
  cross-products, with strict lower/inclusive upper bounds and explicit
  beyond-maximum classification. No rounded logarithm selects the interval.
- `GridNearest`: nearestness of the normalized normal/subnormal result against
  every point on the unbounded nonnegative binary grid, plus its scaled
  half-unit error bound. Finite-exponent and signed reference composition is
  described below; full runtime arithmetic correspondence remains unfinished.

- `FiniteQuantization`, `QuantizationLaws`: finite exponent admission with a
  proved carry shape, overflow sentinel, nearestness across the admitted grid,
  exact representable-input preservation, and no overflow for inputs below an
  admitted finite candidate. The sentinel is mapped to infinity, not treated
  as an additional finite value.
- `BinaryArithmetic`, `FloatWords`, `Binary64Arithmetic`: reference signed
  addition/subtraction/multiplication/division with subnormal rounding, signed
  zero, infinities and NaN classes; a separate total raw-word classification
  retains NaN payload/sign bits. Finite word encoding and observation preserve
  exponents, fractions and common units. The bridge instantiates binary64.
  Hardware/compiler correspondence and NaN result-payload rules remain open.
- `SerdeFloatParts`: the default serde_json staged cast/table-scaling algorithm,
  including repeated rounded division by 1e308, range rejection, signed output,
  and early zero completion. Positive/negative execution traces are unique;
  the negative loop is total, its result is independent of termination fuel,
  and its number of divisions is bounded. Digit accumulation and exponent
  overflow parsing are composed in `SerdeNumeric`; compiled literal-table
  correspondence remains open.
- `SignedMachine`: separate wrapping and saturating signed arithmetic for
  arbitrary widths, with range preservation, exactness for in-range inputs,
  and wrapping idempotence. `SerdeNumeric` composes the parser counters with
  explicit checked-panic and wrapping policies.

- `SequenceCursor`, `ByteCursorTransport`, `SerdeNumeric`, `SerdeNumericWire`:
  streaming integer/fraction/exponent accumulation, checked u64/i32 digit
  bounds, exponent saturation, precision truncation, integer-vs-float dispatch,
  and exact success/error byte consumption. Native counter overflow has both
  checked-panic and wrapping policies; no implicit release-profile assumption
  removes the panic behavior from the model.
- `FinalizingCursor`, `JsonControls`, `JsonFlow`: serde_json container
  finalization, first-error precedence and original error location, even when
  cleanup advances the cursor. Native arithmetic panic bypasses this normal
  finalization path. Token/colon/comma/end controls retain distinct error codes.
- `CursorProgress`, `SerdeNumericProgress`, `JsonCollection`, `JsonAtoms`:
  scalar progress and a total collection visitor whose recursive input measure
  decreases after every successful child. No arbitrary iteration limit is
  substituted for input consumption.
- `JsonTree`, `JsonTreeBounds`, `JsonTreeParser`: recursive parsing with a
  structural nesting certificate, derived depth bounds, and the default
  127-container allowance. The intermediate tree retains duplicate object
  members before map normalization.
- `ByteKeyOrder`, `OrderedObject`, `JsonStoredValue`: canonical decoded-UTF-8
  keys, sorted object storage, insertion-preserved invariants and unrelated
  lookups, and last-occurrence-wins semantics. Recursive normalization preserves
  valid keys and stored child invariants.
- `JsonCompletion`, `JsonDecode`: composed decoding carries nesting and ordered
  storage certificates and proves successful document parsing consumes every
  byte. General syntax soundness/completeness, direct typed visitor composition,
  and actual Rust/library correspondence remain unfinished.
- `JsonPosition`, `NatDecimal`, `JsonErrorDisplay`: source-byte line/column
  calculation agrees with the independent last-newline slice calculation;
  peek positions clamp to input length. Decimal output is canonical and has
  an exact parser round trip. Error rendering retains the original location
  and message through container cleanup; native panic is not a JSON error.
- `JsonNumericValue`: parser integer variants enter schema validation without
  conversion; finite floating values retain sign, exponent/fraction and exact
  common units. The Unicode text/schema connection remains open.
- `ReadLine`: unbounded server line scanning, first-newline completeness and
  uniqueness, byte conservation, newline retention, final nonempty EOF line,
  and UTF-8 admission before JSON. This differs from the bounded client framing
  module and does not silently impose a new server limit.
- `McpEnvelope`: actual server extraction, absent-versus-null IDs, defaulted
  parameters, method dispatch and notification response suppression. Dispatch
  is independent of reply suppression; the current server ignores the version
  field.
- `ScalarText`, `McpInput`: Unicode trimming preserves the existing text
  representation relation. Ingress composes line framing, UTF-8 validation,
  trimming, complete JSON parsing and request extraction without treating
  invalid UTF-8 as a JSON parse error.
- `McpExchange`, `McpRuntime`: tool execution and formatting precede notification
  suppression; replies append a newline, write and flush in order. Failed
  partial writes and failed flushes terminate without retry. State transitions
  use the actual composed parser result, prevent concurrent reads during an
  exchange, and have no outgoing effects after exit. The handler and serializer
  replies are explicit boundaries, not implementations or proved receipts.
- `FiniteBooleanRange`, `ScalarCharacterCheck`, all seventeen
  `ScalarCharacter.Plane*` modules and `ScalarCharacter`: constructive exhaustive
  coverage of the complete Unicode scalar domain, proving the primitive
  scalar-to-character conversion preserves its number. Invalid surrogate
  numbers are excluded by the same explicit scalar predicate used by decoding.
  Each plane is checked in full; these are not regression samples. No postulate
  supplies the character inverse. Range evaluation uses the safe Agda strictness
  primitive and its equality law to avoid repeated interval arithmetic.
- `UTF8ScalarIdentity`, `DecodedText`, `DecodedKey`: canonical UTF-8 packets are
  uniquely determined by their scalar numbers. Decoded text is valid and has
  an exact text round trip; byte-key equality and schema-text equality agree
  in both directions. Every valid schema text can be encoded as a witnessed key.
- `JsonStoredValue` now retains decoded witnesses for keys, in addition to byte
  bounds. `JsonSchemaValue`, `JsonSchemaLookup`, `SchemaDocument` compose total
  value translation, preservation of field lookup, and typed decoder evidence.
  Syntax errors, schema errors and arithmetic panics stay separate. Successful
  typed decoding carries complete input consumption.
- `DecodedTextByteLength`: schema byte-length limits equal the actual encoded
  UTF-8 length for every decoded scalar sequence. The numeric width helper in
  `Text` was extracted to make its character/scalar correspondence explicit;
  the width calculation itself is unchanged.
- `StablePartition`, `PriorityFields`, `AgentFieldOrder`: priority selection
  preserves every key/value entry, and ordinary object order is unchanged.
  Full correspondence to the recursive Rust `AgentJson` serializer remains open.
- `JsonIntegerWriter`: canonical integer spelling has exact numeric meaning and
  belongs to the independent JSON number grammar, including negative minimum
  magnitudes. Floating formatting is separate.
- `Judge.Watch` now proves threshold behavior for arbitrary thresholds and
  counters, replacing the threshold-3 example with soundness/completeness and
  below/at/above-threshold laws.
- `MigrationFinalization`: the source's import/apply error takes precedence over
  an unlock error. A malformed embedded receipt exits before explicit unlock;
  transaction drop queues rollback only before commit entry. Queuing rollback
  is not a database acknowledgement.
- `MigrationDriver` replaces the inaccurate lifecycle in `Migrations`; the
  manifest and abstract atomic publication laws remain there. The driver has
  separate embedded-load, connection, lock, receipt-decode, import, validation,
  ledger-read, transaction, and finalization paths. It preserves the first
  apply/import error across unlock failure, does not close an unowned connection,
  and does not await a rollback that the source only queues. The iteration uses
  one immutable applied snapshot. Success requires the complete transaction
  receipt sequence. Pure parsing, dependency ordering and SQL execution are
  still explicit boundaries rather than assumed-correct implementations.
- `EffectRestriction`, `EffectDecomposition`, `EffectExpansion`: allowed effects
  are preserved by composition and finite prefixes; every completed expanded
  execution decomposes into its abstract operations and exact concrete traces.
  These laws connect specifications; they do not establish Rust correspondence.
- `MigrationLedgerWrite`, `MigrationComposition`: pinned Kryzhen 2.0.3's
  `record_applied` creates a nested savepoint when passed Mimir's transaction.
  Its canonical-row insert, schema-association insert and savepoint release are
  explicit. Neither nested success nor failure commits or rolls back the outer
  transaction. The driver expands its ledger operation through this protocol.
- `MigrationValidation`: duplicate-name and checksum admission are executable
  decisions with independent first-error witnesses and soundness/completeness
  laws. `ExactBytes` validates fixed-width byte arrays without truncation or
  padding.
- `FiniteTable`, `MigrationLedger`: finite support is explicit, with pointwise
  equality instead of an extensionality postulate. Canonical inserts preserve
  existing metadata/checksums, both ledger inserts are idempotent, and schema
  associations retain their canonical-row references. These are row semantics;
  SQL interpretation/correspondence remains open.
- `MigrationRows`: instantiates name/checksum admission with actual textual
  names and 32-byte checksums. Loading rejects invalid lengths and has
  soundness/completeness laws over every row. Native row extraction remains
  outside this decoder.
- `MigrationHistory`: legacy sqlx admission verifies each database row against
  the last-wins receipt index, then checks that every earlier receipt version
  required by a present version is present. Both passes carry rejection or
  acceptance evidence. `MigrationImport` preserves receipt order, advances the
  reconstructed predecessor even across skipped canonical rows, and drops the
  legacy table only after importing the selected entries. It does not pretend
  that import is one atomic transaction.
- `MigrationBootstrap`: captures current schema/search path, handles legacy
  and absent version ledgers, runs self-migrations with their version stamps,
  restores search path, and conditionally backfills schema associations.
  `MigrationComposition` now expands `ensure_schema` through this protocol.
  The source's absent-version-ledger branch creates and stamps the ledger in
  two separate statements, so a failure can leave an unstamped ledger. Retry
  behavior after that partial state remains a recovery obligation, not a
  verified production incident or an implemented repair.
- `ReadySelection`, `TopologicalSchedule`: a total reference planner selects
  the smallest ready name while conserving all items, proves every emitted
  item's dependencies precede it, and proves that a blocked suffix has no
  valid ordering. Its decreasing bound cannot produce a fuel-exhaustion result.
  Correspondence to the efficient source Kahn implementation remains open.
- `DependencyCount`: zero unmet dependencies is equivalent to readiness;
  duplicate requirements contribute duplicate edges. Completing a fresh name
  removes exactly its multiplicity, without counter underflow, and cannot
  disable an already-ready item. `MigrationDependencies` checks dangling
  references and proves that hash iteration order cannot change admission,
  although it can select a different first diagnostic.
- `LowerHex`: fixed two-digit lowercase output for every byte, with exact
  radix value and injectivity over arbitrary byte sequences. Its finite digit
  proof covers all 16-by-16 digit pairs; it is not a sample-based regression test.
- `MigrationImportValues`: instantiates legacy admission with integer versions,
  literal names/checksum hex, and retained receipt descriptions/filenames. The
  imported row retains the embedded script and canonical checksum while
  rebuilding its predecessor and description. Database descriptions do not
  participate in admission. `MigrationRuntime` composes the driver, bootstrap,
  importer and nested/standalone ledger writes with these concrete values.
  The row decoder now proves that its loaded key domain is exactly the input
  row-name set, including last-wins loading of repeated names. This justifies
  the import snapshot's name projection without assuming HashMap iteration order.
- `MigrationQuoted`: soundness, grammar completeness and uniqueness of the
  custom header string decoder. Only quote/backslash escapes are decoded;
  other backslashes remain literal. Unknown escapes are processed with an
  explicitly decreasing recursion, with no unchecked termination directive.
  `MigrationHeader` proves first-wins field interpretation and its required
  single-string fields. `MigrationImplicit` preserves all non-dependency
  metadata and existing dependencies while appending missing predecessors;
  repeated application is idempotent. Full header/file parsing, body slicing,
  checksum calculation and diagnostic formatting remain open.
- `SubstringScan`, `WhitespaceCut`, `MigrationSlices`: first-match uniqueness,
  exact input conservation, shebang consumption, and the source's SQL-body
  delimiter/whitespace rules. Body slicing is now explicit; the remaining
  parser obligations include complete header lexing, backtracking/repetition,
  key character classification, checksum calculation and diagnostics.
- `BacktrackingParser`, `MigrationSyntax`: exact-consumption composition of
  ordered alternatives, checkpoint-restoring repetition/separated lists, the
  complete migration-header/file control grammar, required-field cut failures,
  and final EOF. Successful file parsing consumes all input. The alphanumeric
  predicate and SHA-256 remain explicit parameters, not proved implementations.
- `ParserSafety`, `MigrationParserSafety`: compositional progress and failure
  classification, instantiated over every migration grammar component. For
  every input, file parsing succeeds or returns an ordinary recoverable/cut
  error; incomplete-stream, repetition-stall, and separator-stall outcomes are
  unreachable. This establishes the source assertion's relevant progress
  condition for the modeled grammar, not Rust/compiler correspondence.
- `UpperBoundary`, `UnicodeSkipSearch`, `UnicodeSkipBounds`: first-strictly-
  greater boundary uniqueness; exact offset-loop relation, soundness and
  completeness; selected-header bounds, nonnegative previous-endpoint
  subtraction, positive run lengths, final-index bounds, and bounds on every
  cumulative addition, including the stopping comparison's addition.
  `RustUnicodeData`, `RustUnicode`, `RustUnicodeBounds` instantiate those
  obligations over all 51/43 headers and 1519/291 offsets in Rust 1.99.0's
  Unicode 17.0.0 alphabetic/numeric tables. `MigrationKeySyntax` supplies the
  resulting classifier to the migration grammar. The raw tables were copied
  by `scripts/formal/extract-rust-unicode.py`; the source digest and extraction
  receipt are retained in `/tmp/mimir-unicode-extract-21ZsmaVA.log` (exit 0).
  The extractor is not a proof oracle. Packed-word/binary-search machine
  correspondence remains open; the lookup currently uses a certified reference
  boundary search. SHA-256 remains an explicit input to this parser instance.
- `ModularWord`, `BitLogic`, `WordEncoding`, `WordAddition`, `WordShifts`:
  symbolic unsigned wrapping arithmetic, all-bit choose/majority identities,
  numeric encoding, ripple-carry conservation and exact wrapping addition,
  associativity/commutativity, and invertible width-preserving rotations.
  `SHA256Round`, `SHA256Schedule`, `SHA256Compression` prove the two/four-round
  software layouts, four-lane schedule recurrence, arbitrary grouped-round
  fold, and feed-forward composition. `SHA256Core` instantiates 32-bit words
  and the exact 64 round/eight initial constants from pinned sha2 0.10.9.
  `VectorChunks`, `WordBytes` prove both directions of exact byte/word framing.
  `FixedBlocks`, `VectorFill`, `SHA256Padding` preserve all input and prove
  the full padding-marker/zero-fill/length-field layout for every admitted
  remainder, including the two-block branch. `SHA256Hash` composes a complete
  byte-level reference hash and proves grouped/scalar pipeline equivalence.
  Remaining correspondence includes native bit shifts/rotates, packed lane
  details, CPU feature dispatch, checked-profile length overflow, incremental
  buffering, and valid Unicode text admission at the migration-parser bridge.
  These are not claims of collision resistance or compiled-code verification.
  Source and extraction evidence: `/tmp/mimir-sha256-source-kiz9kyp5.log`,
  `/tmp/mimir-sha256-buffer-source-58v3om89.log`, and
  `/tmp/mimir-sha256-extract-EDQlvNY3.log` (each with exit 0 receipt).
- `TextPredicatePreservation`, `UnicodeChecksum`, `UnicodeParser`,
  `UnicodeParserSafety`, `MigrationChecksumSyntax`, `MigrationChecksumSafety`:
  slicing/trimming preserve arbitrary character predicates, validity evidence
  survives cursor advancement and checkpoint restoration, and checksum output
  is independent of the chosen admission proof. The concrete migration parser
  now composes Unicode classification, admitted scalar text, UTF-8 and SHA-256
  without a supplied checksum oracle. All admitted inputs satisfy the ordinary-
  failure/progress and full-success consumption laws. Header parsing and its
  safety laws are shared with the prior parameterized parser. Runtime panic/
  machine correspondence, filesystem loading and rendered diagnostics remain.

The pinned Kryzhen source inspection is retained in
`/tmp/mimir-kryzhen-migration-source-HASQbxY1.log` (exit 0). It also identifies
remaining obligations inside `ensure_schema`: legacy migrator-ledger replacement,
self-migrations, search-path restoration, and one-time schema-association backfill.
Legacy sqlx import validates receipt checksums and prefix history, then imports
rows in receipt order and finally drops the legacy table; it is not one global
transaction. These details must be included before claiming database coverage.
Additional parser/type/file source is retained in
`/tmp/mimir-kryzhen-parser-source-9XGpPKeW.log` (exit 0). The source searches for
shebangs without requiring a line boundary, splits bodies at `\n-- #!`, trims
body whitespace, and computes SHA-256 of the trimmed script. Its lexical
backtracking and fatal missing-field behavior remain separate obligations.
The lockfile selects Winnow **0.6.26** for Kryzhen, despite also containing
0.7.15 and 1.0.4. Its actual alternative/repetition implementations and the
existing Rust 1.99.0 Unicode source are retained in
`/tmp/mimir-parser-dependencies-4QM4bkoV.log` (exit 0). That compiler's Unicode
tables are version 17.0.0. No dependency or compiler version was changed.
Alternatives reset before the next branch; repeat resets a recoverable failed
iteration; separated lists also roll back a separator whose following item
fails recoverably. Fatal errors do not take those recovery paths.

Unicode proof evidence is retained in the interactive composition log. Two
monolithic attempts were explicitly aborted after 242.7 and 253.7 seconds;
neither was a completed proof. Plane 0 then checked in 52.1 seconds, and the
other sixteen complete plane checks were retained independently. The first
Boolean aggregation was aborted after those facts checked. The final universal
coverage theorem checked in 556.0 seconds, with no warnings, goals or constraints
reported by its load. Its cost includes 522.2 seconds elaborating the first
sixteen planes and 33.0 seconds for the final plane's use. Do not edit these
finite facts casually or repeat their normalization as an unrecorded diagnostic.

Independent checks are in `/tmp/mimir-independent-checks-HM2K52CM/` and
`/tmp/mimir-independent-checks-ZHUlKOXx/`. The former checked the generalized judge
laws and stable partition; a reserved binder in the priority module was then
corrected and that module checked. `AgentFieldOrder` hit the independent
checker's 1 GiB heap cap. The unchanged module subsequently checked in the
existing 2 GiB interactive checker in 1.222 seconds. Both heap allowance and
process/cache state differed, so the result does not isolate a single cause.

Exact formatting dependency found in this checkout: serde_json 1.0.154 uses
`zmij` 1.0.23 for finite f64 output, not its separately present `ryu` dependency.
The pinned source is retained in `/tmp/mimir-zmij-source-20261029.log`.
The transaction-drop inspection uses tokio-postgres 0.7.18, retained in
`/tmp/mimir-transaction-source-SXcPlCZB.log`.

The composed aggregate passed with exit 0:
`/tmp/mimir-agda-composed-YzmXjTpx.log` and its `.exit` receipt. The sandbox-only
attempt failed before checking because it could not reach the Nix daemon;
`/tmp/mimir-agda-composed-2k9f7g8V.log` retains that failure. The subsequent
native-permission invocation used the same existing environment and a 2 GiB
heap cap. The source audit in `/tmp/mimir-formal-boundary-audit-bun4ccxz.json`
finds all 162 formal modules imported by the aggregate and no unsafe options,
postulates or unfinished proof markers. This supersedes an audit that failed
to recognize `open import`; no source modules were missing. These checks verify
the current partial specification, not completeness of Mimir behavior or Rust
correspondence. Work remains active.

The subsequent Unicode/schema aggregate also passed, with exit 0 retained in
`/tmp/mimir-agda-unicode-composed-zTSubU9C.log` and its `.exit` receipt. The source
audit `/tmp/mimir-unicode-source-audit-sqjnxwxo.json` covered 194 imported safe
modules with no postulates or unfinished proof markers. The migration additions
above were checked individually afterward and require a fresh aggregate check.

The migration composition aggregate passed with exit 0 in
`/tmp/mimir-agda-migration-composed-DvahHbV4.log` and its `.exit` receipt.
`/tmp/mimir-migration-source-audit-f1_rel3l.json` covers all 212 modules at that
point: every module imported by the aggregate, safe options throughout, and
no postulates or unfinished proof markers. `MigrationImport` and `LowerHex`
were added and checked afterward; final aggregate checking remains required.

The next aggregate, including concrete import composition and the header/string/
implicit-dependency additions, passed with exit 0:
`/tmp/mimir-agda-migration-parser-MthimCKn.log` and its `.exit` receipt.
`/tmp/mimir-migration-parser-audit-ltp9mgvs.json` records all 219 modules imported,
safe options, and no postulates or unfinished proof markers. This remains a
partial behavioral specification; no Rust changes were made by this rebuild.

Current checker: `/tmp/mimir-formal-interactive-json-composition-20261029.log`,
with a 2 GiB cap. The earlier `capture` checker and fresh `json-controls`
checker exhausted 1 GiB after visiting the combined module declarations. The
2 GiB diagnostic exposed an unconstrained token-list binder; specifying its
byte-list type resolved that constraint, and the combined control module then
checked in 1.441 seconds. Neither the binder correction alone nor the larger
heap alone has been isolated as the cause of resource recovery. Earlier
`rounding`/`finite` heap failures and the generic `capturePoint` correction are
retained in their logs. All currently completed additions above check without
warnings or unresolved goals; this is not runtime correspondence verification.

The Cargo book documents checked-overflow panic behavior and distinct default
[development/release profiles](https://doc.rust-lang.org/cargo/reference/profiles.html#overflow-checks).
The specification therefore parameterizes native arithmetic overflow checks.
The Rust standard library implements string equality and ordering through
[their bytes](https://doc.rust-lang.org/src/core/str/traits.rs.html), so object
key ordering is modeled directly on decoded UTF-8 byte codes.

Resolved dependency inspection: `/tmp/mimir-serde-features-Am7DbnM6.log` and
its exit-0 receipt show only serde_json `default` and `std` features. In
particular `float_roundtrip` is not enabled. Numeric conversion must therefore
model the actual staged casts/scaling in the default `f64_from_parts`, rather
than silently substituting an ideal exact-decimal rounding operation. No Cargo
features or dependencies were changed during this inspection.

Additional concrete defect found while specifying notification persistence:
`notifications/src/state.rs::write_named` currently attempts `remove_file(temp)`
after any closure failure, including failed exclusive creation. It does not
establish that this invocation created the path it removes. The formal protocol
requires ownership from successful exclusive creation before cleanup. No Rust
repair has yet been applied. No uniqueness assumption about random temporary
names is used to dismiss this path.

`Unsigned` now also proves completeness: every in-range value in its independent
decimal grammar is accepted. Prefix monotonicity establishes that a valid final
value cannot encounter intermediate overflow. This covers arbitrary inputs and
bounds, not selected port examples.

Persistent interactive checker: `/tmp/mimir-formal-interactive-rounding-20261029.log`.
The offsets checker exhausted its 1 GiB heap while loading `Dyadic` for a grid
nearestness proof. That failed load is retained with exit 251. Integer power
laws were moved unchanged to `BinaryPowerLaws` and re-exported by `Dyadic`, so
integer-only grid proofs no longer depend on the rational bridge. In a fresh
checker under the same cap, the changed `Dyadic` checked in 14.5 seconds with
no goals or warnings. This does not establish that extraction alone caused the
memory improvement; the fresh process is another changed condition.
The codecs, unicode and escapes checkers exhausted their bounded heaps during
surrogate-offset elaboration. Declaration diagnostics localized the problem to
concrete offset conversion. A symbolic opaque offset conversion and its value
law now check before concrete instantiation; the full UTF16 module checked in
769 ms, with no goals or constraints. No memory-limit increase was used.
The preceding errors-named checker exhausted its 1 GiB heap while checking a
new shared radix module and exited 251. That module was not verified by that
attempt. The replacement retains the cap and adds declaration diagnostics;
implicit numeric bounds were made explicit before resuming its proof.
`Radix` subsequently checked in 709 ms, including positional uniqueness and
both round trips. The same process later exhausted its heap checking concrete
UTF-8 byte instantiations and exited 251. The checked `Bits` conversions and
their laws were placed in an Agda `abstract` block before resuming, to prevent
repeated arithmetic expansion at that boundary. No memory-cap increase or
postulate was used. This checker's success must be observed, not inferred from
the refactoring.
The opaque-boundary byte check subsequently passed in 9.739 seconds including
dependency loading. Packet completeness checked in 1.112 seconds, and full
sequence completeness checked in 811 ms, with no goals or warnings reported.
The current checker uses a 1 GiB heap limit and definition profiling. Two earlier
checker processes were terminated after concrete binary64 normalization consumed
approximately 20 GiB and 12 GiB respectively. Their terminations are not successful
verification. The symbolic bridge checked in 14.6 seconds under the bound.
The original pipeline's exit status did not capture the killed checker; see
`/tmp/mimir-formal-interactive-nix-20261029.log.termination`. Current pipelines
retain status with `pipefail` as well as full output.
The bounded checker later exhausted its 1 GiB heap while elaborating a deeply
nested dependent `with` chain in review admission (exit 251, retained in the
bounded log). Replacing the chain with typed result composition preserved the
obligations and checked successfully: 22.8 seconds including dependencies,
13 ms attributed to the admission definition. No heap-limit increase was used.
The intermediate nonterminal checker exited on closed input without checking;
its exit 0 is not verification evidence. The current terminal process retains
input and uses the same heap bound and profiling.
The composed checker also reached its heap bound while reducing equality of
the concrete MCP error code in a round-trip proof (exit 251 retained in its
log). Generalizing the envelope laws over the integer error code and checking
the symbolic lemmas before instantiating -32000 checked in 16.0 seconds under
the unchanged bound. Future arithmetic proofs should use symbolic parameters
before instantiating constants; do not repeat concrete normalization blowups.
An aggregate `agda Mimir.agda` check passed with exit 0 after the RPC/runner
additions: `/tmp/mimir-agda-aggregate-oqlM3wi3.log` and its `.exit` receipt.
Subsequent modules checked individually; final aggregate checking remains
required after all changes. No postulates have been introduced. No Rust
edits have been made in this rebuild stage.

Additional numerical gap found by inspection: `Scores::from_totals` validates
finite input totals, but input finiteness alone does not establish finiteness
of intermediate sums/products. This is a proof gap, not an established reachable
production failure: callers aggregate rows constrained to unit-bounded weights.
Reachability and rounded accumulation bounds must be proved before deciding
whether any numerical implementation change is necessary. The previous rational
bounds alone do not establish that result. Reference for the floating type:
https://doc.rust-lang.org/std/primitive.f64.html.

Historical migration SQL is immutable: checksum verification runs at startup.
In particular, the exact-mean claim in migration 005's description is stronger
than what its floating operations establish. Correct documentation and prove
actual numeric compatibility without rewriting a released migration's contents.

Document inspection found two concrete implementation gaps: `load_document`
deletes prior chunks before requesting embeddings, so a provider failure can
destroy the prior loaded document; its `zip` can also store fewer rows than its
returned chunk count. The new replacement contract preserves old data on
preparation/transaction failure and validates full cardinality before publication.
The existing `Documents` module also contains unimplemented summary proposals
and previously claimed a false parent/path equivalence. The misleading comment
is corrected; those proposals are explicitly excluded from current API coverage.

Retry comparison must follow typed Rust `PartialEq`, not serialized JSON byte
equality. In particular, validated floating fields consider negative and positive
zero equal even though their bit patterns and serialized spellings can differ.
The existing abstract revision contract therefore needs a canonical semantic
payload projection when related to concrete typed requests. Source text, actor,
and provenance fields still compare exactly. Do not turn this observation into
normalization of stored source text or rewriting released data.

Wire syntax reference: [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259.html).
Its number grammar does not accept NaN/Infinity or a leading plus. Configuration
unsigned parsing deliberately has a different grammar allowing a leading plus;
it cannot be reused unchanged as a JSON number parser. Duplicate object handling
must also distinguish `serde_json::Value` normalization from direct typed decoding.

The old abstract correction transition set `acknowledged` to the preceding
source revision even if that revision had never been reviewed. SQL preserves
the actual last acknowledged revision. `LearningContracts.Revision.correct`
now preserves that value; every admitted cell carries `acknowledged ≤ current`,
and the pending-after-correction proof follows from this invariant. Its project
field now uses literal text rather than a hypothetical numeric interning map.
The commit/retry proofs checked again after these corrections. Concrete loading
must validate the state invariant; it is not assumed for malformed stored data.


Judge startup compatibility (formal work; Rust unchanged):
`LearningCapabilities` defines and validates the existing learning contract and
assessment model versions, source coverage, typed learning items, revision-owned
assessments, and unchanged legacy graph probability semantics. Its wire round
trip quantifies over bounded version values. It does not change the application
version (2.1.0), and does not impose judge startup on standalone graph clients.
`McpToolAdvertisement` selects the first exact tool name and checks named schema
paths. `JudgeToolCatalogue` retains original tool definitions, separates host-only
operations from model tools, validates the existing optional tools if advertised,
and checks typed-review fields including source coverage and assessments.
`JudgeHandshake` checks initialization, notification acknowledgement, catalogue,
and learning capabilities in that order. Every successful execution has exactly
that effect sequence; every completed or interrupted execution has at most four
abstract protocol effects. Ready values carry the actual accepted catalogue and
capability replies with their admission proofs. Rejection cannot become readiness.
These proofs do not establish subprocess, network, JSON-line or OS behavior.

Source inspection (`/tmp/mimir-judge-mcp-current-wd23mgkd.log`, exit 0) found that
current judge startup never calls the already-available `learning_capabilities`
tool and only checks three nested review fields. It cannot establish typed
learning compatibility from those checks. The formal startup adds that check;
Rust implementation and integration with the transport remain outstanding.
Full JSON Schema compatibility, rather than selected named field types, is also
not yet established by the catalogue proofs.

Client transport formalization (not yet Rust refinement): `McpClientWire`
connects concrete outer JSON decoding to the JSON-RPC envelope. Missing IDs
remain distinct from explicit null IDs, unsigned IDs are range checked, and
present error values take precedence over results without losing the original
value. Tool result decoding requires one text item containing a valid embedded
JSON document. Independent `ToolEvidence` is proved necessary and sufficient;
malformed JSON preserves its exact parser fault and source text.
`McpClientRequest` composes sending, concrete line decoding, and notification
handling. The counter advances before sending and cannot wrap. An invariant
relates remaining allowance to notifications already observed. Every completed
or interrupted request has at most 66 abstract events (one send and at most
65 line reads); a failed send stops without reading or resending. This is not
a time bound or a proof of the write/flush implementation.
`McpClientLine` defines the lower byte framing and clock-check protocol. A body
at the limit is accepted only if the next byte is LF; non-LF overflow, timeout,
and EOF before LF cannot become successful frames. EOF requests stderr settling
and a snapshot. Every complete or interrupted line has at most limit+1 timed
byte-read requests. `McpClientLineLaws` proves an independent event grammar:
successful bodies are exactly the bytes received, in order, before the first LF;
every read follows a nonexpired clock check with the derived timeout duration.
Every returned buffer has no LF and fits its configured capacity. Clock samples
and timed-read receipts are explicit external inputs; this does not assert that
Tokio always returns by an exact wall-clock instant. Stderr rendering, outgoing
serialization/write/flush, and full refinement between line and request effects
remain open. Client EOF behavior is intentionally distinct from the server
`ReadLine`, which accepts a final nonempty fragment.

The 283-file aggregate passed with exit 0 in
`/tmp/mimir-agda-client-TVif2agu.log`. It predates the following error-wire
modules and the generalization of the missing/null ID laws; those need the
next aggregate check. All new line laws checked without goals or warnings.

`McpErrorWire` preserves bounded integer codes, exact message text and optional
structured data through the JSON-value boundary. Codes outside the i64 range,
noninteger codes, and missing codes follow the existing fallback behavior.
Its round-trip laws quantify over every admitted code and error value. Typed
refusals remain distinct from legacy errors; the latter cannot establish that
a review made no database changes. `McpErrorDelivery` connects this decoder to
the existing judge error adapter and controller. Validation paths/messages
reach subsequent model feedback unchanged after the explicit log receipts;
candidate conflict and candidate-reference faults retain separate dispatches.
The i64 instance is explicit. Raw JSON serialization, server construction of
these richer error envelopes, and Rust correspondence remain unfinished.

`WriteAllFlush` models observed partial writes, zero writes, invalid reported
counts, errors, timeout, cancellation and flush receipts. All transitions
preserve the original byte sequence as an observed prefix and pending suffix.
Finite traces are bounded by the original byte length plus one; failed and
completed states cannot continue. Successful completion retains exactly the
original bytes and has a successful flush receipt in its trace. Failure does
not imply that a peer received nothing or that a remote operation was undone.
`McpSendBytes` adds the client body limit, newline suffix and deadline check.
An independent successful-trace relation proves every delivered result passed
the strict body-length check and nonexpired clock check before one transmission
attempt, with its actual write/flush trace retained. These modules start at the
serialized-byte boundary. Complete value serialization and correspondence to
the Tokio implementation remain separate, unfinished obligations.

Handshake aggregate: `/tmp/mimir-agda-handshake-ZtxR4h89.log`, exit 0, 279 formal files. Import/safety audit: `/tmp/mimir-handshake-audit-4xkcsclw.json`. No missing imports, unsafe flags or escape markers were found. Individual handshake checking reported no goals or warnings.

The 287-file aggregate passed with exit 0: `/tmp/mimir-agda-client-send-oTnW2fkd.log`. Audit `/tmp/mimir-client-send-audit-o6ex_gcg.json` reports all modules imported and safe, with no escape markers. No Rust implementation changes or installations have been made in this rebuild.

`DiagnosticText` specifies control-character removal followed by a character
count limit. It proves order-preserving subsequence, absence of control
characters, scalar-count and UTF-8-byte bounds, exact preservation of already
admitted text, and idempotence. The byte ceiling is four times the character
limit; a character limit is not silently reinterpreted as a byte limit.
Rust 1.99.0 `char::is_control` uses C0 and C1 ranges explicitly. Its source,
`Utf8Chunks`, and `String::from_utf8_lossy` are retained with SHA-256 identifiers
in `/tmp/mimir-lossy-rust-source-0awccp3g.log` (exit 0). Lossy decoding and source
excerpt offsets still require separate formal completion.

`UTF8LossyTail` supplies a total bounded continuation reader with an independent
grammar, sound byte reconstruction, completeness, and complete/interrupted
length laws. Invalid following bytes remain unconsumed. `UTF8LossyGroup` uses
the pinned Rust leading-byte and restricted second-byte ranges; every group
consumes one to four bytes, and invalid groups consume at most three.
`UTF8LossyBytes` partitions every finite input using its actual byte length as
fuel, conserves all original bytes in order, and renders one U+FFFD byte sequence
per invalid group while retaining valid-group bytes. Rendered length is at
most three times input length. The bridge proving that every valid group is a
canonical scalar, equivalence to Rust coalesced chunks, and excerpt offsets
are still open. These partition proofs do not substitute for those obligations.

The 291-file grouping aggregate passed with exit 0 in
`/tmp/mimir-agda-lossy-groups-NHs8iRB9.log`. Subsequent `UTF8ByteRanges` proves
all six numeric ranges directly from the classifier prefix bits, with no byte
fixtures. `UTF8ByteDecode` proves the equivalent numeric decision procedure and
inverts accepted ranges into the actual payload words and their byte equalities.
These two modules checked individually without goals or warnings; they still
require the next aggregate check. Canonical scalar bounds for assembled lossy
groups remain the next obligation.

The 293-file byte-range aggregate passed in
`/tmp/mimir-agda-byte-ranges-Fp2i1kU0.log` (exit 0); audit
`/tmp/mimir-byte-ranges-audit-dvyieocw.json` found no missing imports, safe flags,
or forbidden escape markers. Subsequent `UTF8PacketValue` establishes exact
word assembly and numeric values without changing the shared packet decoder.
`UTF8CanonicalBounds` proves shortest form, surrogate exclusion and Unicode
maximum bounds under explicit word-value conditions. `UTF8LossyPayload` and
`UTF8LossyConditions` derive those conditions from the actual accepted byte
ranges. `UTF8LossyCanonical` therefore constructs a canonical scalar for every
accepted group with its exact original byte encoding. `UTF8LossyValid` proves
every complete lossy output is valid UTF-8, including the output replacement
literal. `UTF8LossyText` connects those bytes to checked Char conversion and
retains the byte-size bound. These modules checked individually without goals
or warnings. The reverse direction (canonical inputs are never replaced),
Rust chunk-coalescing equivalence, excerpt offsets, and the next aggregate
check remain open.

Reverse canonicality proof development hit the 2 GiB heap cap while loading
`UTF8CanonicalNecessity`. The terminated interactive checker retained its full
output in `/tmp/mimir-formal-interactive-resumed-hOmyJ6RX.log` and exit 251 in
the adjacent receipt. This load is not verification. The replacement checker
keeps the same cap and retains declaration diagnostics in
`/tmp/mimir-formal-interactive-canonical-bMrEFnXC.log`; the expensive obligation
must be isolated before another broad check. No Rust changes are involved.

That failed load has now been resolved without increasing the heap allowance.
Declaration diagnostics isolated `fourMinimum`; an aborted diagnostic load
spent 35.585 seconds in that declaration. Moving the contradiction lemma to
`NatSeparation` and making its arguments explicit did not by themselves resolve
the expensive load. Replacing dependent `with` abstractions with explicit
decision functions preserved all premises and conclusions. The resulting full
`UTF8CanonicalNecessity` load checked in 14.725 seconds, with 11 ms attributed
to `fourMinimum`, no goals and no warnings. The retained log includes the
aborted attempts; they are not successful checks.
`UTF8LossyGroupComplete` proves completeness of the independent group grammar.
`UTF8LossyAdmission` derives the actual byte checks from canonicality, and
`UTF8LossyPacket` constructs an admitted group for every canonical packet and
arbitrary following suffix. `UTF8LossyIdentity` proves partition uniqueness and
that every already-valid byte sequence passes through unchanged. The text
bridge now proves exact preservation of every admitted source string as well.
No postulates or test fixtures were introduced. These individual checks still
require aggregate verification; Rust chunk-coalescing correspondence and source
excerpt offsets remain open.

The 306-file identity aggregate subsequently passed with exit 0 in
`/tmp/mimir-agda-lossy-identity-BM2qztzT.log`. `SourceWindow` proves exact byte
selection, conservation, input bounds and equivalence of saturation followed by
clamping under the explicit source-length machine bound. `SourceLineOffset`
connects line skipping to the first-newline grammar, handles absent lines at
EOF, and bounds the byte offset. `SourceFailure` composes those operations with
the concrete parser diagnostic and lossy text conversion, preserving stage,
source size, message and error origin through parser cleanup. The source window
is bounded by 32 KiB; its lossy UTF-8 rendering is bounded by 96 KiB. Those are
different limits in the existing implementation, not a configuration change.

`UTF8LossyChunks` proves coalescing against an independent grammar, grammar
completeness and uniqueness, original-byte conservation, and exact agreement
between chunk rendering and packet rendering. `UTF8ChunkValidity` proves each
valid chunk slice is UTF-8 and each nonempty invalid slice has one through three
bytes. The source grouping and coalescing obligations are now composed; native
Rust pointer/slice execution and compiled implementation correspondence remain
open. The new modules checked interactively; final warning cleanup and aggregate
verification follow. No Rust, installed binary, service, production database,
version, or configuration was changed.

The 311-file source/chunk aggregate passed with exit 0 in
`/tmp/mimir-agda-source-chunks-oTupQJ7G.log`. Subsequent `JudgeStateRecords`
captures report, incident, diagnostic event and trace fields with explicit clock
and downcast inputs. `JudgeConfirmationLedger` proves append-only confirmation
updates, exact affected/selected identity provenance, timestamp provenance and
preservation of uniqueness when the loaded ledger is unique.
`JudgeIncident` constructs write plans with transition evidence for every status
branch. `JudgeIncidentEvidence.newlyAdded` proves a new confirmation requires a
complete report, consistent completion counts, and membership in both selections.
Idle marks an incident recovered without adding confirmation evidence, matching
the current source. Identifier uniqueness and concrete UUID conversion are not
assumed by these parameterized models.

`UnsignedMachine` distinguishes checked overflow from release wrapping for
persisted counters. `JudgeTraceEvent` retains budget observations when an event
is omitted, preserves unrelated metadata, and bounds each call and interruption
prefix to one serialization. `LastElement` proves exact last-element removal.
`JudgeTraceTrim` proves prefix retention, preservation of unrelated trace fields,
and at most one serialization per input event plus the final check. Explicit
outcomes include serialization failure, oversized metadata and arithmetic panic.
The serialization operation carries its complete input record and returned bytes;
composition with a concrete JSON encoder is still open. The effect bound is not
a wall-clock latency bound. Trace lookup/retention, record wire schemas and
filesystem composition remain unfinished. These modules checked interactively
without goals or warnings; aggregate verification follows.

The 319-file incident/trim aggregate passed with exit 0 in
`/tmp/mimir-agda-incident-trim-H8NbH4ox.log`; audit
`/tmp/mimir-incident-trim-audit-atdp21yt.json` found no missing imports, safe
flags or forbidden source escape markers. `FirstListMatch` now proves exact
first-match selection, uniqueness without an input uniqueness premise, and
preservation of other entries on removal. `JudgeTraceSelection` distinguishes
running-only event lookup from status-independent finish lookup.
`JudgeTraceRetention` models single-entry eviction and the source index-zero
fallback. Pin/new-ID preservation is proved for eligible eviction; it is not
claimed for the fallback. Capacity restoration requires an input at most one
entry over the limit. Loaded arbitrary oversized histories and UUID collisions
are not assumed away.

`JudgeTraceStart` composes reading, per-running-trace clock observations, UUID
generation, creation time, conditional pin lookup, retention and write. It
proves old running statuses are removed while identities/order/length survive,
and success requires a final write acknowledgement. `JudgeTraceMutation`
composes selection, append and trimming for recording and finishing, including
missing-record and arithmetic/serialization failures. Both successful mutation
paths require a final write acknowledgement. Concrete storage durability and
record encoding remain separate unfinished obligations.

UUID source inspection is retained with hashes in
`/tmp/mimir-uuid-1.28-source-1J1Hhx9c.log` and
`/tmp/mimir-uuid-errors-source-DvQskcIX.log`. The locked version is 1.28.0.
Serde JSON uses the string visitor, canonical lowercase hyphenated encoding,
and string-only deserialization; the generic UUID byte/sequence visitor is not
the JSON `deserialize_str` path. The existing checked `JsonStringWriter` is
being reused, not replaced. `ByteHex` proves byte round trips and injectivity;
`HexBytes` proves fixed-count parser soundness/completeness, exact output length
and suffix-preserving round trips. `UUIDGroups` covers all 128-bit values,
including nil and non-v4 values. `UUIDHyphenated` proves canonical 36-byte
output and exact round trips for arbitrary trailing suffixes.

Two proof loads exhausted the unchanged 2 GiB checker cap: `ByteHex.roundTrip`
in `/tmp/mimir-formal-interactive-canonical-bMrEFnXC.log` (exit 251), and
`UUIDHexClassifier.native` in
`/tmp/mimir-formal-interactive-uuid-VSrx9290.log` (exit 251). Neither is a
successful check. Factoring digit spelling from the dependent byte round-trip
split resolved the former (full load 15.125 seconds, round-trip declaration
12 ms). Factoring arithmetic calculations from the branch selector resolved
the latter. `UUIDHexClassifier.nativeCorrect` then checked over every possible
byte, establishing equality with the hex grammar for wrapping subtraction and
OR-0x20 classification. The current checker log is
`/tmp/mimir-formal-interactive-hex-f06t3TWW.log`, with the same heap limit.
Full UUID wrapper parsing/error rendering, concrete record schemas/encoding,
filesystem composition and Rust implementation remain unfinished.

The 330-file trace/UUID aggregate passed with exit 0 in
`/tmp/mimir-agda-trace-uuid-RUsquePp.log`; audit
`/tmp/mimir-trace-uuid-audit-mhre9s4z.json` found no missing root imports,
safe flags or forbidden source escape markers. Subsequent `UUIDParse` models
all four accepted formats and retains the actual original/inner failure slice.
`UUIDHyphenatedGrammar` and `UUIDParseGrammar` prove soundness against independent
grammars. `UUIDParseComplete` proves the converse for all admitted spellings,
including mixed-case hexadecimal and case-insensitive URN letters.
`UUIDAcceptance` derives an acceptance decision, rejection equivalence,
unique decoded identity, canonical encoding injectivity and stable normalization.
No UUID version, non-nil or collision-free generation premise is introduced.

`ASCIIText` constructs canonical UTF-8 witnesses without changing any byte.
Its initial dependent `with` expansion exhausted the unchanged 2 GiB heap cap
in `/tmp/mimir-formal-interactive-hex-f06t3TWW.log` (exit 251); that load failed.
An abstract, fully proved byte constructor and a separate generic prepend lemma
avoid the expansion. The replacement checker keeps the same cap and retains
output in `/tmp/mimir-formal-interactive-json-4hoD2pS0.log`.
`UUIDJson` proves that every canonical UUID byte is an unescaped JSON literal,
that serialization emits exactly 38 bytes including quotes, and that the JSON
parser composed with the UUID parser recovers every UUID and preserves arbitrary
following input. These modules checked interactively without goals or warnings.
Detailed UUID error rendering, concrete judge record codecs, filesystem
composition and compiled Rust correspondence remain unfinished. No Rust,
installed binary, service, production database, version or configuration changed.

The 337-file UUID/JSON aggregate passed with exit 0 in
`/tmp/mimir-agda-uuid-json-NfpRQa9G.log`; audit
`/tmp/mimir-uuid-json-audit-bcyp__qb.json` found no missing root imports, safe
flags or source escape markers. `UUIDSchema` subsequently connects schema text
and UUID byte parsing and proves canonical round trips and encoding injectivity.
`JudgeStateWire` specifies all nine persisted record encodings, declaration
order and exact serde omission conditions. A present empty optional string is
retained; omission is distinct from an empty present value.

Locked Serde source inspection (serde/serde_derive 1.0.229 and serde_json
1.0.154) is retained with hashes in
`/tmp/mimir-serde-struct-source-lOk1GaOC.log`. `deserialize_struct` accepts
positional JSON arrays as well as objects. Derived sequence visitors apply
field defaults only after input exhaustion and reject extra elements; map
visitors ignore unknown keys and reject repeated known keys. An object-only
decoder would fail to preserve existing accepted state representations.
`SerdeSequence` and `SerdeStruct` prove soundness and completeness against
independent typed admission relations. Map error ordering/wording is not
claimed: native state reads collapse all serde failures to `invalid state
report`. Parsing ignored raw JSON, source/runtime correspondence and the
concrete serializer byte stream still require composition.

`JudgeStatePrimitives` checks machine-width unsigned and signed field ranges
and UUID decoding. `JudgeStateDecode` supplies every actual record descriptor,
including nested records and each missing-field default. `SerdeEmission`
proves the general object round-trip rule: every emitted member needs a codec
receipt, every omitted member needs the declared default equality, and unique
schema names prevent overwrite. All of those modules checked without goals or
warnings. `JudgeStateBounds`, omission builders and concrete nested round-trip
proofs are being composed; their completion and next aggregate check remain
pending. The overall specification and Rust rebuild remain incomplete.

The concrete nested round-trip obligations are now discharged interactively.
`JudgeStateBounds` expresses only the native numeric field widths, including
nested records. `SerdeEmissionBuilders` covers conditional omission, nested
arrays and present-empty values. `JudgeStateRoundTrip` proves exact recovery
of every field in SourceFailure, DeferredReview, FailureDiagnostic, Report,
ConfirmedReview, FailureIncident, DiagnosticEvent, DiagnosticTrace and
Diagnostics for every value within those numeric widths. It imposes no status,
history-size, uniqueness-of-UUID or event-count premise. Each schema's field
names are proved unique. The final module load checked in 3.752 seconds without
goals or warnings in `/tmp/mimir-formal-interactive-json-4hoD2pS0.log`.
Aggregate verification follows. Exact byte serialization, raw ignored-value
parsing, decoded numeric-domain evidence, filesystem composition and compiled
Rust correspondence remain open.

The 347-file state-codec aggregate passed with exit 0 in
`/tmp/mimir-agda-state-codecs-itxyG0xS.log`; audit
`/tmp/mimir-state-codecs-audit-dza1ajtg.json` found no missing root imports,
safe flags or forbidden source escapes. `SerdeObtained` records the origin of
every decoded field. `JudgeStateFieldLaws` and `JudgeStateReadBounds` prove the
converse numeric-domain guarantee for all nine records: every accepted object
or positional array yields native-width values, including defaults and nested
collections. No extra loaded-history restrictions are imposed.

`JsonTextWriter` proves scalar-to-record text preservation.
`JsonCompactRecords` constructs compact surface JSON for the integer/string/
container subset used by these records and proves exact structural byte
accounting, including every separator and delimiter. `JudgeStateText` states
Rust String's Unicode-scalar domain without content restrictions;
`JsonRecordSupport` and `JudgeStateSerialize` construct encodings for every
record. `JsonCompactIdentity` proves that emitted bytes and counts do not
depend on the chosen admission proofs. Floating-value serialization is not
included in this integer-record subset and remains a separate full-JSON
obligation. The schema-level signed-positive representation versus the byte
parser's unsigned-positive representation still needs explicit composition.

`JudgeTraceConcrete` executes event append using the concrete serializer and
proves exact request/byte receipts, the one-serialization bound, actual-byte
fit acceptance and preservation of valid text. `EffectsInterpret` supplies a
general proof-indexed concrete responder with full execution/receipt evidence.
`JudgeTrimConcrete` uses it to execute every trimming pass with the concrete
record serializer, preserving text through prefix removal and proving at most
one serialization per initial event plus the final check. These modules checked
interactively without goals or warnings. Next aggregate verification is pending.
Full raw-byte decoder composition, native serializer/compiler correspondence,
filesystem persistence, the remaining Mimir subsystems and the Rust rebuild
are still unfinished; installed binaries and production state are unchanged.

The 359-file concrete-state aggregate passed with exit 0 in
`/tmp/mimir-agda-concrete-state-Q0TGQvqF.log`; audit
`/tmp/mimir-concrete-state-audit-rxycfw3a.json` found no missing imports,
missing safe flags or source escape markers. The aggregate also rechecked
dependents of the generalized Unicode-validity proof. Persistence inspection
continues against the existing state source; Rust 1.99.0 Unix path sources and
hashes are retained in `/tmp/mimir-rust-path-source-g2HdRshc.log`.

The filesystem continuation adds `BitMaskClear`, `UnixMetadata` and
`UnixMetadataLaws`: arbitrary-width numeric AND/zero equivalence with independent
selected-bit predicates, the existing metadata policies, and equivalence to the
native numeric permission expressions. `JudgeFilesystem` records the exact
request flags and distinguishes native failures, explicit closes and lock
contention. `JudgeDirectory` retains actual inspected metadata and proves the
successful directory/parent receipt order; parent creation remains strict while
state-directory creation tolerates AlreadyExists. `EffectsComposition` proves
execution decomposition and result-map inversion. `JudgeLock` covers early
closes, contention and unlock-then-close, with a necessary successful-lock
receipt. `JudgeRead` closes after every read result, bounds accepted bytes and
retains the exact decoder input. `JudgeWrite` includes temporary/directory
descriptor closure, exclusive-creation ownership, all commit acknowledgements
and uncertainty after rename. It specifies the intended cleanup correction;
the faulty Rust cleanup is still unchanged.

The initial aggregate failed with unresolved implicit metadata fields in six
numeric-equivalence helper applications (retained log
`/tmp/mimir-agda-filesystem-0ncdPmXn.log`, exit 42). Interactive goal inspection
identified unconstrained metadata fields; explicitly passing the original
metadata resolved them. The corrected 368-file aggregate passed with exit 0 in
`/tmp/mimir-agda-filesystem-3kc5Hdxe.log`. Source audit
`/tmp/mimir-filesystem-audit-f9mdiwjq.json` reports no missing imports, missing
safe flags or escape markers. These checks do not establish native OS/compiler
correspondence. Concrete Unix paths/ancestors, low-level read/write refinement,
byte-decoder integration and the remaining full-Mimir obligations remain open.
No Rust, installed binary, configuration or production-data change was made.

`UnixPath` preserves raw OS bytes through lossless separator splitting and
leading root/current-directory classification. `UnixPathParts` proves that
split components contain no separator and that exact empty/dot/parent/normal
classification agrees with independent lexical rules. `UnixPathLaws` proves
absolute-path joins and replacement. `JudgeStatePath` specifies explicit-path,
XDG_STATE_HOME and HOME precedence, exact environment/cwd requests, absolute
selection and parent-component rejection. A successful cwd reply carries its
absolute-path contract as input evidence; native validation is still an adapter
obligation, not a postulate. `UnixPathParent` tracks original byte endpoints and
uses a strictly decreasing length proof for ancestor recursion, without a fuel
cutoff. `UnixPathAncestry` proves prefix preservation, the complete parent chain,
the original-byte-length-plus-one ancestor bound and independence from the
termination witness. Correspondence of the forward endpoint algorithm to the
native double-ended Rust iterator remains open.

`ASCIIPath` proves exact code-point/byte identity for admitted filename literals.
`JudgePersistence` instantiates lock/read protocols with concrete native paths,
ancestor sequences, judge filenames, limits and canonical UUID temporary names.
The 376-file aggregate passed with exit 0 in
`/tmp/mimir-agda-paths-GUrkbE8f.log`; source audit
`/tmp/mimir-path-audit-53_5zvwi.json` is clean. No runtime rebuild or installation
has occurred. Next persistence work is the native partial-read/write boundary;
the prior `WriteAllFlush` finite-trace bound concerns its abstract reply model,
not arbitrary interrupted native system calls.

The 378-file aggregate passed with exit 0 in
`/tmp/mimir-agda-native-io-wRaDsLdp.log`; audit
`/tmp/mimir-native-io-audit-bb7byqto.json` is clean. `NativeWriteAll` proves
byte conservation, exact completed bytes and a bound on noninterrupted progress
events, while constructing arbitrary finite interruption sequences.
`NativeTake` models both read interfaces, their capacity/remaining-budget
guards, zero-budget suppression and consumption even with buffered-read errors.
Rust 1.99.0 I/O sources/hashes are in
`/tmp/mimir-rust-io-source-sdip6lun.log` and
`/tmp/mimir-rust-take-source-sc_adl_e.log`. UUID-v4 source/hashes are in
`/tmp/mimir-uuid-v4-source-gjua416t.log`; its random-source failure panics, and no
uniqueness guarantee may be assumed. `EffectsHandling`, `JudgeWriteReceipt`
and `JudgeFilesystemDisplay` subsequently checked individually; their aggregate
check remains pending. The inventory now links 49 judge-state definitions to
their partial models and lists open correspondence/composition obligations.

Agda workflow correction, prompted by the user: I did not follow the skill's
required proof-driving loop. The persistent process had been used mainly for
Cmd_load and occasional Cmd_metas, with proofs drafted outside the interactive
goal environment. I also added three unused closed permission-mask assertions
proved by refl, contrary to the skill. Safe checking does not excuse these
workflow violations. Those three assertions are removed; executable mask
definitions and universal numeric permission laws are unchanged. A syntactic
audit found fourteen candidates, including existing modules, in
`/tmp/mimir-agda-closed-refl-audit-hra8_1v6.json`; this is a candidate scan, not a
complete semantic audit. Replacements must preserve intended laws and quantify
over the actual relevant domain, rather than add an unused parameter.

The configuration and MCP-default assertions have been generalized over every
configuration/fallback. Their goals were inspected with Cmd_goal_type_context,
normalized with Cmd_compute, refined with Cmd_refine, then reloaded and checked
for remaining metas. Retry assertions are being replaced by a necessary and
sufficient rule over all revision states, using Agda-generated Cmd_make_case
clauses. Graph-label, root-depth and zero-decay-mean corrections are in progress.
The same retained interactive log contains these commands and their results.
Future proof development MUST use the skill's goal/context/search/refinement
workflow for every nontrivial theorem; Cmd_load-only development is not compliant.

The workflow corrections now check individually without goals or warnings.
Retry permission is necessary and sufficient for a corrected revision; graph
weight/propagation predicates are equivalent to an independent label relation;
the defeat-target theorem applies to arbitrary containing graphs and reachable
sources. Root depth is equivalent to an empty section path. Zero-decay mean is
proved for every evidence state, with its nonzero-denominator witness constructed
by transport rather than assumed. These corrections used actual goal/context,
case-splitting and refinement commands in the retained interactive process.
They do not retroactively make prior proof development compliant. Source audit
`/tmp/mimir-proof-workflow-audit-dvpkwd46.json` covers 381 formal files and finds
no missing safe flags/imports, escape markers or remaining syntactic closed-refl
candidates. The latter is a limited syntactic scan, not a full semantic audit.
The 381-file aggregate is running; full behavior coverage and Rust correspondence
remain unfinished.

The 381-file aggregate passed with exit 0 in `/tmp/mimir-agda-workflow-G9hYP5Lr.log`. This checks the corrected statements and the three previously pending modules; full-spec completion and runtime refinement are not established.

The continuation adds a general AND/OR overwrite law for every bit/word width,
exact UUID version/variant byte laws preserving all other bits, and UUID random
input/endianness protocols with complete successful/failed entropy receipts.
These were developed by inspecting goals and refining/case-splitting in the
persistent interactive process. `UUIDV4` explicitly leaves correspondence to
the native single 128-bit mask expression open; its verified byte-level laws
must not be described as that adapter proof. `JudgeNamedWrite` composition is
in progress. No Rust implementation, binary, configuration, or production-data
change has been made.

`JudgeNamedWrite` composes size admission, observed entropy, concrete temporary
and target paths, and the ownership-corrected filesystem write. Its completed
success proof reconstructs the entropy bytes plus every successful filesystem
receipt; its failure laws prohibit subsequent effects after serialization,
size-admission, and entropy failures. All terms were accepted through interactive
refinement; the saved module is being rechecked as `JudgeRecordWrite` imports it.
`JudgeRecordWrite` ties each of the three filenames to its actual persisted
record, Unicode/native numeric input domain, and concrete compact serializer.
Its wrapper proofs and the new aggregate remain pending. Native UUID mask
correspondence, decoder composition, allocation and runtime adapters remain open.

The saved named-write proof did not finish verification: the persistent checker
exhausted its 2 GiB heap, exit 251, after checking declarations while loading
`JudgeRecordWrite`. Full retained evidence is
`/tmp/mimir-formal-interactive-json-4hoD2pS0.log` and its `.exit` receipt.
Diagnostics exposed large expansions of concrete filename bytes through nested
dependent with-clauses. The repair factors the same success relation through an
arbitrary-path `EmbeddedCommit` theorem and a separate entropy-prepend theorem;
no success condition or effect is removed. A replacement persistent checker
retains the 2 GiB cap and logs to
`/tmp/mimir-formal-interactive-json-DmbbuqMw.log`. These replacement proofs and
saved-module verification are still pending. No higher heap, Rust trial/build,
or installed-service change was used.

The restructured arbitrary-path proof and its concrete entropy/name application
both check without goals or warnings at the unchanged 2 GiB cap. Saved
`JudgeRecordWrite` also checks, including exact serializer byte count and
successful-write size/receipt laws. The 386-file aggregate passed with exit 0
in `/tmp/mimir-agda-record-write-e4YgL0sg.log`; source audit
`/tmp/mimir-record-write-audit-asj6qi0r.json` finds no missing imports, missing
safe flags, escape markers or syntactic closed-refl candidates. Native UUID
mask/source correspondence and the other full-rebuild obligations remain open.
The checked filename/serializer composition covers the three persisted-record
call families, not arbitrary unused generic write-helper instantiations.
No Rust rewrite, build, install, service/configuration or production-data change
has occurred. The 100–300 additional active-hour ETA supplied on request is a
low-confidence planning estimate, not a measured or dependable completion bound.

Raw saved-record decoding cannot be implemented by parsing a generic JSON Value
and then decoding the struct: serde_json 1.0.154 `deserialize_ignored_any` calls
its distinct `ignore_value` path. Retained dependency source/hashes are in
`/tmp/mimir-serde-ignore-source-te80zo0B.log` (exit 0). Ignored numbers are
scanned without numeric conversion/range checks; ignored strings consume any
four hex digits after u without surrogate validation and skip literal byte runs
without UTF-8 validation. Ignored containers use an explicit scratch stack,
without the ordinary recursion counter. Known duplicate fields must also be
preserved for rejection, so Stored.normalize is inappropriate for this path.
`JsonIgnoredEscape` checks universal parse completeness for all short escapes,
all hex digit quadruples and all suffixes. `JsonIgnoredString` retains an
independent accepted-byte grammar, exact successful suffixes and exact failure
consumption; completeness has been constructed interactively and the saved
module reload is pending. The remaining ignored-number/container scanner and
schema-directed raw record decoding are not implemented yet. The last aggregate
is the 386-file record-write receipt above; the two ignored-parser modules are
newer and require later aggregate verification.

The five ignored-parser modules now pass aggregate verification (391 formal
files), exit 0 in `/tmp/mimir-agda-ignored-parser-65kTFcXC.log`, at the unchanged
2 GiB cap. `JsonIgnoredNumber` proves digit-prefix/suffix and consumption laws;
full lexical equivalence remains open. `JsonIgnoredStep` describes iterative
value/key/container-boundary transitions with a proof that every continuing
step consumes input. `JsonIgnoredRun` constructs a terminating execution for
every input and proves transition faithfulness, determinism, completeness with
respect to that transition relation, and independence from any sufficiently
large internal recursion measure. These are universal proofs driven through
interactive contexts, case splits and accepted refinements, then saved/reloaded.
The transition relation itself still needs native-source correspondence and
accepted-grammar/error-law proofs. No claim of complete Rust refinement follows
from execution faithfulness alone. Schema-directed raw-record decoding remains
open. No Rust, installed binaries, version, configuration, services or production
data changed.

`JsonIgnoredNumberComplete` now checks a universal theorem over the independent
RFC 8259 number grammar: every admitted sign/whole/fraction/exponent, with
arbitrary digit lengths and every JSON-delimited suffix, is accepted. Its byte
bridge, `JsonIgnoredNumberWire`, also checks and proves exact consumed number
bytes, exact retained suffix bytes, and incompatibility of witnessed success
with any failure. There is no magnitude premise. Both saved modules report
checked=true with no metas/errors/warnings in the retained interactive log.
These two modules are newer than the 391-file aggregate receipt; later aggregate
verification is still required. Full invalid-input soundness and native-source
correspondence remain open. The corrected 391-file source-audit receipt is
`/tmp/mimir-ignored-parser-audit-0qdgrxti.json`; its predecessor falsely omitted
root `open import` clauses and was corrected without changing formal imports.

The 393-file aggregate (including both ignored-number completeness modules)
passed with exit 0 in `/tmp/mimir-agda-number-completeness-kAYNUJAi.log` at the
unchanged 2 GiB cap. Newer saved modules `SerdeFlow`, `SerdeSlots`, and
`SerdeMember` individually check with no goals/errors/warnings. `SerdeFlow`
preserves syntax versus visitor failures, their original and cleanup cursors,
and panic bypass. `SerdeSlots` retains explicit known-field presence (including
supplied optional nulls), proves lookup/update/duplicate/default resolution
laws, and shares existing field metadata instead of duplicating schemas.
`SerdeMember` consumes the raw decoded key and selects a known typed reader or
the ignored-value scanner; duplicate rejection precedes the colon/value read,
as confirmed in the retained serde_derive source. Its selection/duplicate laws
are universal. `SerdeLoop` is under development for terminating stateful visitor
execution; no current aggregate receipt covers these new typed-parser modules.
No Rust implementation, installed binary, version, service/configuration or
production data has changed. Complete parser acceptance/error equivalence,
native correspondence, full component coverage and the Rust rewrite remain open.

The 399-file typed-visitor aggregate passed, exit 0, in
`/tmp/mimir-agda-typed-visitors-EgSzIbv4.log`. The retained source audit
`/tmp/mimir-typed-visitors-audit-sxu1lz2i.json` found no missing safe flags,
missing root imports, or escape markers. This includes `SerdeLoop`,
`SerdeMap`, and `SerdePositional`: a terminating cursor-exact execution with
measure independence; source-order map members and default resolution; and
positional field defaults, supplied-failure precedence and panic propagation.
The positional defaults match explicit serde(default) attributes on the
persisted record fields, not a generic assumption about all Option fields.
Retained derive sequence source is
`/tmp/mimir-serde-sequence-source-pbkv9ge_.log`.
Typed scalar/recursive record readers, independent full grammar/error
correspondence and Rust refinement remain incomplete. New proof development
continues after this aggregate receipt.

Typed decoding now has individually checked scalar success invariants,
container cleanup/error precedence, remaining-depth selection for both struct
forms, vector boundary ordering, optional-null child bypass, and concrete
integer-reader range theorems (`SerdeSuccess`, `SerdeScalar`,
`SerdeContainer`, `SerdeRecord`, `SerdeVector`, `SerdeOption`,
`JudgeStateAtoms`). They were developed using the retained interactive
context/case/refine workflow and saved-module reloads. `JudgeStateRaw` is being
checked to connect the nine concrete schemas to those readers. These additions
are newer than the 399-file aggregate receipt and need aggregate verification.
The dependency dispatcher/source snapshot with SHA256 is retained in
`/tmp/mimir-serde-typed-dispatch-3w1df3yf.log`.

Native error-position attachment remains a specific correspondence obligation:
serde generated visitor errors can initially have no position, and
`deserialize_struct` calls `fix_position` after end_map/end_seq cleanup. The
current logical first-error origin and final cleanup cursor must not be
mistaken for a completed model of that formatted diagnostic position. Native
private-state reads erase serde diagnostics, but source-level correspondence
must still distinguish those observations. No change to Rust, installed
binaries, version, configuration, services or production data occurred.

The 412-file aggregate passed with exit 0 in
`/tmp/mimir-agda-record-read-VYTIMZc4.log`, retaining the same 2 GiB heap limit.
Audit `/tmp/mimir-record-read-audit-k10dv54c.json` found no missing safe flags,
root imports or escape markers. This covers the nine concrete raw record
readers and the complete-document suffix check. `EffectMap` proves both
directions of exact trace preservation under pure result mapping.
`JudgeParsedRead` composes the executable typed parser with guarded bounded
byte reads, keeps decoder panics distinct from invalid-report failures, and
proves that every successful record retains the actual raw-read receipt.
`JudgeRecordRead` fixes the three names, limits and ancestor paths and proves
complete document consumption and byte bounds for successful receipts.
All new proof terms were developed through the persistent interactive process,
then saved and reloaded without goals, errors or warnings. The first attempt
to split a decoder-result equality was stuck because its computed left side
was not an independent variable; a generalized result/equality helper resolved
the proof without an axiom or weakened statement.

These are specification composition proofs. Full typed-field invariants,
independent grammar/error correspondence, native adapter correspondence and
all remaining coverage-ledger components remain incomplete. No Rust changes,
build, installation, migration, version, service, configuration or production
data changes were made in this continuation.

The 421-file reader-invariant aggregate passed, exit 0, in
`/tmp/mimir-agda-reader-invariants-OEts5J4t.log`. Audit
`/tmp/mimir-formal-source-audit-c8zgakct.json` found no missing safe flags,
root imports or escape markers. The reusable audit script is
`/tmp/mimir-formal-source-audit.py`; it is a syntactic audit, not a semantic
completeness test. `SerdeSlotInvariant`, `SerdeMemberInvariant`,
`SerdeLoopInvariant`, `SerdeMapInvariant`, `SerdePositionalInvariant`,
`SerdeParserInvariant`, `SerdeRecordInvariant`, `SerdeVectorInvariant` and
`SerdeOptionInvariant` prove propagation of explicitly supplied child/default
predicates through both struct forms, list accumulation/reversal, optional
nulls, whitespace and closing cleanup. These are conditional universal laws;
they do not assume or establish the concrete judge field obligations. Those
obligations are the next work. `SerdeSuccess.trivial` supplies only the unit
predicate used for syntax controls; it is not used as a substitute for a field
predicate. A positional proof initially left inferred parser-result arguments
unsolved; spelling out those result arguments discharged the constraints.
A local vector module alias collided with the validation alias and was renamed
before proof development. All saved modules were reloaded cleanly using the
same persistent interaction process. Rust implementation and native
correspondence remain unchanged and incomplete.

Concrete raw-reader numeric invariants now cover all nine judge record families
in `JudgeRawLeafBounds` and `JudgeRawCompositeBounds`. Child and default
obligations are discharged for every field, including nested optional records,
lists, signed revisions, u64 timestamps and target-sized counters. The bound
predicates are the existing `JudgeStateBounds`; no extra semantic limits on
loaded histories or source offsets were introduced. Unit predicates on text and
UUID fields mean only that those fields have no numeric bound in this theorem;
they do not establish Unicode validity or replace that separate obligation.
`SerdeSuccessTransfer`, `JudgeRawInvariant` and `SerdeDocumentInvariant` provide
composition. These saved modules individually checked without remaining goals,
errors or warnings using the persistent goal/context/case/refine workflow.

The first read-receipt composition was accepted interactively but its saved
module reload exhausted the unchanged 2 GiB heap after declaration checking.
The 427-file aggregate also failed with exit 251, retained in
`/tmp/mimir-agda-record-bounds-bpVb9S7h.log`; this is not a passing receipt.
The preceding source audit `/tmp/mimir-formal-source-audit-3qpakqb3.json` was
syntactically clean but does not override that failure. The interactive failure
is retained in `/tmp/mimir-formal-interactive-json-DmbbuqMw.log` and its exit
receipt. Document-level bounds and receipt transfer are being separated to
isolate the expansion, preserving the same propositions. The replacement
persistent checker retains the same cap and logs to
`/tmp/mimir-formal-interactive-record-bounds-BRgyV89W.log`. This repair and a new
aggregate check remain pending. No Rust, installed binaries, version, database,
service or configuration changes were made.

The separated document/receipt modules now check, and the 428-file aggregate
passed with exit 0 in `/tmp/mimir-agda-record-bounds-private-Nb4UtNgP.log`.
The intermediate aggregate `/tmp/mimir-agda-record-bounds-restructured-GdfX9Ap3.log`
also failed at the unchanged 2 GiB cap, despite successful individual reloads.
Making implementation-only module aliases private in the five new proof modules
reduced their generated interfaces: `JudgeDocumentBounds` from 475,420 to
168,774 bytes, `JudgeRawCompositeBounds` from 447,863 to 264,676 bytes, and
`JudgeRawLeafBounds` from 262,393 to 163,751 bytes. The original size inventory is
`/tmp/mimir-agda-interface-sizes-fgl93nch.json`. The proof propositions and terms
were preserved. This combination of changes resolved the aggregate failure;
it does not establish an isolated cause for every earlier heap failure.

`JudgeRecordBounds` now refers directly to the original loaded receipt instead
of exporting another chain of instantiated module aliases. Its byte projection
needed explicit overflow-check, size-maximum and name parameters: these are
unused by the underlying raw-byte record and cannot be inferred from it. The
interactive unresolved metas were inspected, the projection type queried,
and those parameters supplied before the clean saved reload. The clean
428-file source audit before the final alias change is
`/tmp/mimir-formal-source-audit-caoc8527.json`. Subsequent Unicode proof work
starts with `SerdeValidateInvariant`, which is not covered by this aggregate.
All nine numeric field obligations now transfer to complete documents and
successful guarded read receipts. Unicode text validity, full independent
acceptance/error equivalence, native correspondence, remaining components and
Rust implementation are still open.

The 432-file aggregate passed with exit 0 in
`/tmp/mimir-agda-record-text-7zRGdmt4.log`, retaining the same 2 GiB limit.
Audit `/tmp/mimir-formal-source-audit-tq5w5obm.json` finds all formal modules
imported, all safe flags present, and no escape markers. `SerdeValidateInvariant`
transfers predicates from parsed inputs through validation, with explicit
failure/panic branches. `SerdeScalarUnicode` derives Unicode validity from
decoded scalar strings, preserving the evidence through whitespace and typed
validation; it does not assume every Char-based text is valid. The text adapter
in `JudgeRawInvariant`, the seven record families in `JudgeRawText`, and
`JudgeRecordText` propagate that property through every textual field, explicit
default, optional record/text and nested list to the original successful
filesystem-read receipt. The two remaining record families contain UUIDs and
numeric fields only. These definitions add no content or text-length policy.
All proof terms were developed through interactive goal/context/case/refine
commands and saved reloads without goals, errors or warnings. Implementation
aliases remain private to avoid unnecessary exported scope expansion.

The existing `JudgeStateRoundTrip` uses the intermediate structured-value
decoder. Its laws do not establish byte-level serialization/raw-reader round
trips; that composition, independent grammar/error equivalence and native
correspondence remain open. No Rust, installation, migration, version, service,
configuration or production data changes accompany this receipt.
# Unsigned byte-reader round trips

The 444-module aggregate passed, exit 0, in
`/tmp/mimir-agda-unsigned-readback-MPBuHhzh.log`, with the unchanged 2 GiB
cap and compacting GC. The source audit
`/tmp/mimir-formal-source-audit-njqot634.json` found no missing safe flags,
aggregate imports or escape markers. Every saved new module checked in the
persistent interactive process with no remaining obligations.

`JudgeUnsignedReadBack.Parser.roundTrip` now connects canonical unsigned JSON
bytes to `JudgeStateAtoms.Parser.readUint` for every value within both the
chosen field maximum and u64, preserving the exact suffix. Its suffix must
stop numeric parsing (EOF or a first character that is neither a digit, dot
nor exponent marker). The bound is a real premise, not a sampled test.
`SerdeIntegerReadBack` proves bounded accumulation cannot overflow on the way
to an in-range final result; `SerdeUnsignedReadBack` handles canonical leading
zero rules and all decimal encodings. `ByteReadBack` and
`SerdeUnsignedWireReadBack` connect the reversible byte bridge and actual
canonical writer. `SerdeNumberStart` proves numeric dispatch and absence of
leading whitespace. `SerdeNumberReadBack` and `SerdeReadBackComposition`
preserve success through typed dispatch, whitespace and validation.
`SequenceReadBack` supplies a result-indexed value/suffix receipt.

A direct rewrite through dependent `Productive` proofs produced an ill-typed
with-abstraction. The correction proves composition for arbitrary parser
results/products first, then instantiates it; it does not weaken the law or
assume parser correctness. Pattern-matching clauses also avoid unconstrained
lambda inference metas in the receipt helpers. Failed attempts and subsequent
goal-driven corrections remain in the persistent interaction log.

Signed integer read-back, whole-record byte round trips, native Rust
correspondence and the other coverage-ledger components remain unfinished.
No Rust edits, builds, installations, migrations, version changes, service or
configuration changes, or production data changes were made.

# Raw string reader round trips and aggregate memory evidence

`SerdeReadBack`, `JudgeTextReadBack` and `JudgeUUIDReadBack` establish
canonical string and UUID read-back laws for arbitrary valid text/UUID values
and arbitrary suffixes through the modeled raw field readers. The value and
unconsumed suffix are both preserved. These are not yet record byte round trips
or native Rust correspondence. All three saved modules checked individually
through the persistent goal/context/refinement workflow, without postulates.

The 435-module aggregate first exhausted the unchanged 2 GiB heap cap:
`/tmp/mimir-agda-string-readback-hPlbc1MA.log`, exit 251. Its source audit,
`/tmp/mimir-formal-source-audit-j0pi8m3e.json`, was syntactically clean.
The subsequent aggregate invocation with compacting garbage collection and
statistics (`+RTS -M2G -c -s -RTS`) passed, exit 0, in
`/tmp/mimir-agda-readback-compacting-AfyaQpaY.log`. It reported 866,634,712
bytes maximum residency and 1525 MiB total memory in use. The heap cap was
not raised. This establishes that invocation passed; cache state also differs,
so this is not an isolated causal proof that compaction alone fixed the failure.
Future aggregate checks retain complete logs and the same cap.

Integer field and whole-record byte round trips remain open. Integer suffixes
require an explicit stopping condition: a following digit, decimal point or
exponent marker can legitimately extend a JSON number. No Rust, installed
binary, version, service, configuration or production data was changed.



### 2026-10-31 01:29 UTC — interface and storage composition checkpoint

Approved stage remains the detailed Agda behavioral specification, due before
2026-10-31 07:03:56 UTC. Rust, deployment, installed binaries and system
configuration remain excluded. No postulates were added.

Focused interactive checks now cover ConfigurationSchema/ConfigurationProtocol,
EmbeddingBackend/EmbeddingLifecycle, MigrationSchema, CLI/HookProtocol,
StorageSemantics, ConnectionProtocol, ServiceStartup, McpRuntimeComposition,
LearningStateWire and JudgeScopedTools, in addition to the earlier application
request/encoding/dispatch and MCP composition modules. MigrationSchema reuses
the existing Migrations manifest. Aggregate and source/coverage audits remain
pending; these focused checks are not a completion claim.

StorageSemantics binds inference reads and primitive writes to ApplicationStore.
Learning reads derive grounding from physical live GROUNDS joins; publication
preserves chunks, both vector stores and grounding on commit/abort/unknown
acknowledgement (general checked theorem, constructed interactively). Sweep
grace conversion now occurs after the nonempty-defeat, belief and clock reads.
Remote embedding dimensions are backend-specific; only local BGE is 768.
Native edge insertion explicitly rejects empty MATCH results, so the suspected
missing-endpoint conformance issue was disproved by store.rs inspection.

JudgeBatchReadback now retains first failure diagnostics/source evidence while
reading every selected revision. JudgeScopedTools specifies all twelve allowed
tools, host reviewer identity, input scope and post-result filtering, including
host-only visibility reads. Remaining work: complete judge runner/host/provider
and notification/digest composition; bind configuration/runtime details and
remaining physical receipt boundaries; finish local embedding shape/concurrency
constraints; audit CLI presentation/parser boundaries; verify the aggregate and
update the full coverage inventory. Existing known native conformance gaps
(mixed-edge reachability, document replacement atomicity, remote embedding row
alignment) remain explicit and are not weakened to match the current Rust.


### 2026-10-31 02:47 UTC — composition checkpoint (unfinished)

The eight-hour specification-only stage remains active; deadline 07:03:56 UTC.
Rust, installed binaries, version 2.1.0 and system configuration are unchanged.
No new postulates have been added.

Focused interactive checks passed for JudgeBackendComposition, JudgeServiceBinding,
JudgeWorkflowComposition and JudgeHostProtocol before the latest persistence
bindings; JudgePersistenceComposition, JudgeStateOperations, NotificationRuntime,
NotificationWire, OAuthComposition, NotificationStorage and JudgeNotification also
passed focused checks. The host is being rechecked with concrete finalization
and incident/status receipts; these latest links are not yet claimed checked.
The interactive checker now has a 4 GiB process heap after repeated 2 GiB
exhaustion. This changes only that verification process, not system configuration.
Full transcript: /tmp/mimir-formal-interactive-record-composition-Uy7DXGal.log.

The aggregate development load passed the migration naming correction and
reached McpServiceProcess, where two implicit configuration arguments were
underdetermined. They are now explicit; the aggregate must be rerun. Remaining:
notification/provider/file and daily-digest composition; MCP child lifecycle and
selection/readback bindings; remaining storage/service bindings; full source
coverage reconciliation; final aggregate batch verification.

Additional specification/native discrepancy found: notification temporary-file
cleanup, like the judge writer, unconditionally attempts removal after failed
exclusive creation. The required shared JudgeWrite contract only permits cleanup
of a successfully created temporary file. No Rust repair is part of this stage.

### 2026-10-31 03:25 UTC continuation checkpoint

The judge host composition checked successfully after binding owned MCP startup,
handshake, every scoped-call request ID/deadline, and completion cleanup.
EmbeddingService, OAuthRefreshRaw/OAuthResponseBinding and NotificationWire also
checked. The subsequent NotificationMail check exhausted the 8 GiB process heap
(exit 251); it is inconclusive, not a proof failure or successful verification.
Full retained log: `/tmp/mimir-formal-interactive-record-composition-1MOgdrAX.log`.
The verifier is restarting without diagnostic profiling and with a 16 GiB
process heap (about 50 GiB available); no system configuration is changed.

Current additions awaiting checks include GroundingStorageBinding,
InferenceStorageBinding, NotificationFileBinding/Mail/Composition. Remaining
work: service effect binding, CLI startup/dispatch integration, digest/watch
composition, coverage inventory update and final aggregate verification.
No Rust, installed binary, version or production-data changes. No new postulates.

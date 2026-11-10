# Recovery must reach the intended result

`Mimir.Recovery` defines one goal for an operation: its final shared world and
complete semantic reply equal the independently stated intended outcome for the
original invocation. An operation supplies a pure `intended` function and an
`expectedReply` function. It cannot supply a different goal or an observation
that ignores inconvenient writes.

The application instance uses all of `ApplicationStore.World`: the graph,
learning sources and history, document chunks, belief vectors, chunk vectors
and grounding links. Comparing the whole world also requires unrelated data to
remain as the intended function describes. Removing a belief while leaving its
vector behind cannot satisfy a deletion intent that removes both.

The reply is the complete semantic tool result, including its success or
correction indication. Transport request IDs belong to the MCP exchange rather
than the saved operation outcome. A tool cannot satisfy the goal merely by
returning a plausible reply while leaving the wrong stored state, or by changing
the state correctly while returning the wrong result.

The invocation retains the original input and starting world. They stay fixed
across interruptions and retries. For example, a write that committed before
its acknowledgement was lost must return its original created identity on a
completed retry. Replacing the starting world with the partially changed world
would conceal a duplicate write or a changed reply; the recovery theorem must
use the original invocation throughout.

Identity allocation, project ownership, selected configuration and other facts
needed by an intent must be explicit in that operation's input or starting
world. They are not guessed by the goal. PostgreSQL's identity allocation is an
external dependency. This interface does not attempt to prove UUID uniqueness.
The execution semantics must separately establish any admission, transaction,
ownership and concurrency assumptions used by a concrete operation.

A malformed request can have a correction outcome whose intended world is the
unchanged original world. Its expected reply must describe the problem and the
correction required by the interaction contract. An error message alone does
not excuse unintended writes.

This is the goal definition from #71. The shared execution relation from #72
requires both the existing script transcript and physical changes justified by
each statement's semantics. Its result is indexed by the actual returned value;
merely ending a transcript does not classify a business outcome as successful.

Interruption includes every execution prefix, including stopping before the
first statement or losing the final operation reply. It also includes a
statement that changed the database before its own reply reached the caller.
That reply is not counted as observed. The database instance reuses the existing
transaction contract: after a lost acknowledgement, either the old state or
the committed state remains possible. Neither is silently treated as rollback.
The same generic definition applies to every operation; an operation cannot
choose a shorter list of interruption points.

`Recoverable` now requires the script, physical statement semantics, independent
intent, convergence proof and progress proof together. Convergence uses the
shared interruption and completion relations and the fixed goal. It cannot
substitute a weaker predicate. The proof covers a completed retry after every
interrupted world that the statement semantics permits.

Progress has no configurable readiness test. Every admitted input and represented
starting world must have a lawful completed execution. Combining that witness
with convergence establishes that it reaches the intended state and reply. An
operation that always says it is unavailable cannot satisfy this contract for
an intent that requires a write. This is an existence claim under the declared
dependency semantics, not a guarantee that a real external service will answer.
It adds no deadline or retry quota.

The input type must contain the actual admitted request and its required
context. A concrete operation table must still cover every public request;
using an empty input type cannot establish that coverage. Malformed inputs need
the separately specified correction path rather than being silently excluded.

Concrete instances and exclusive dispatcher entry remain #74 and #76. These
foundations do not yet remove raw dispatch. The native comparison tests must
consume the same intended outcomes and statement boundaries, and the later
disposition work must require evidence before reporting an integrity failure.

The remaining human judgment is whether each intended outcome expresses what
the user actually wants. An identity function can still be the wrong intent.
Review and the native differential tests must check that meaning; this module
does not claim that a type can discover it automatically.

`Single.single` is the proved entry for one committed statement. Its statement
supplies the physical state/reply function, an independently reviewed intent,
and evidence that a confirmed execution realizes that intent. Construction
also requires idempotence of the complete state and reply. Having one SQL
statement is not evidence that it is safe to repeat.

For example, an append that creates another row on each retry cannot supply
that proof. A deletion that leaves the state unchanged on retry but returns a
different affected-row count also lacks the required reply stability unless
its original result is retained and read back. The constructor does not bypass
this obligation for generated identifiers or counts.

The proof uses the shared generic interruption relation. A statement can leave
only the original state or its atomic publication. A general coverage theorem
maps every existing PostgreSQL atomicity receipt, including both possible
states after lost acknowledgement, into those interruption states. An abort
or uncertain acknowledgement never becomes a confirmed completed result.
After a completed retry, idempotence establishes the original intended state
and complete reply. Progress supplies the confirmed execution witness under
the declared dependency semantics.

A read that preserves the world and computes a specified answer has a general
idempotence proof and enters through the same constructor. This does not yet
remove raw scripts from the dispatcher; the concrete operation table and its
exclusive entry remain #74 and #76. Native adapters must still establish that
each statement's physical meaning matches its implementation.

## Intended-outcome test contract (version 1)

This is the data boundary for #89. The executable adapters are tracked by
existing #152. A test must compute an expected observation by calling the real
reviewed pure functions listed below, then compare it with the complete native
observation. Neither a second Rust implementation of the expected behaviour,
execution of the operation's script, nor a validator that merely accepts an
observed world against a goal is an intended-outcome evaluator.

The machine-readable envelope and complete family inventory are in
[the version 1 schema](intended-outcome-contract.schema.json). Existing public
and model decoders validate the complete row payloads; the schema does not copy
their domain rules. The coverage check requires every advertised tool, the
internal writes below, the CLI statistics and core pattern reads, and every
top-level/nested shared World field.
This is contract-inventory coverage; it does not claim that the #152 executable
adapters have been implemented or checked.

The input contains these fields:

| Field | Meaning |
| --- | --- |
| `contract_version` | The integer `1`. Unknown versions fail input validation. |
| `entrypoint` | `mcp`, `cli`, or `library`, identifying the actual entry under test. |
| `request` | The actual operation name and its original public arguments. Preserve optional-field omission, explicit null, local keys and the operation token. |
| `initial_world` | The complete finite database snapshot before the first attempt, using the world representation below. |
| `current_settings` | The actual semantic configuration observed by the entrypoint. Include model/vector identity and the user-owned retention policy where used; exclude credentials. |
| `observations` | Ordered, execution-bound external observations described below. These supply external facts, never expected answers. |

There is no input field for an expected world, expected result, success flag,
goal, desired vector, or caller-selected allocation. The operation is selected
from the closed application catalogue. The evaluator's dependencies use the
installed standard parsing, timestamp, UUID and numeric conversion boundaries;
this contract adds no parser, formatter or UUID-uniqueness proof.

The output has exactly three parts:

* `world`: the full expected final world, in the same representation as
  `initial_world`;
* `body_result`: `{"kind":"returned","value":...}` containing the complete
  raw concrete result, or `{"kind":"not_entered"}` when admission stopped
  before entering the body; an actual JSON null result remains distinguishable;
* `public_payload`: the complete expected semantic public result, computed by
  the existing `ApplicationOutput.Encode` projection and operation readback.

The separate native observation artifact contains these same three fields and
`exchange`: the complete original request and actual returned exchange,
including every RPC content block and transport error. A CLI run retains its
arguments, complete stdout/stderr and exit status instead. The pure evaluator
receives only the input above; it cannot read the native final world, response
or exchange while computing an expected observation.

A registered completed payload includes `operation_token`, `status`, the
original request metadata (`operation`, arguments, settings and `bound_at`),
and `result`. Correction, recovery, pending, cancellation and reserved outcomes
retain all their fields and diagnostic paths. Comparing only `result`, only a
count, or only a success indication does not satisfy this contract. A cached
completion preserves the present world and returns the saved original result;
it does not restore a historical snapshot over later work.

For MCP, the transport adapter validates the protocol version and request ID,
the response/error form, and exactly one expected JSON text content block before
unwrapping `public_payload`. Extra, mixed, missing or unexpected content blocks
fail the test; they are never silently discarded. The complete outer exchange
remains in the test artifact. Existing native wire checks own this transport
validation; no separate formal JSON-RPC model is required here.

### The complete finite world

World field names below are the existing Agda record field names. Row values
reuse their existing public/source/history representations, including the
actual native enum spellings. The adapter must retain every field of those
values, rather than introduce a smaller test-specific belief or experience.

| World path | Required content |
| --- | --- |
| `learning.publication.ledger.cells` | Every stored incident's project, current/source revision, review revision, acknowledged revision and original contribution key. |
| `learning.publication.ledger.histories` | Every version's source/review revisions, requested canonical review, applied canonical review and optional original unallocated review. Histories retain their newest-first order. |
| `learning.publication.registry` | Experience ID, complete original candidate declaration, node ID and retired flag. |
| `learning.publication.owners` | Every learning-item ID's experience, source reference and actor. |
| `learning.publication.nodes` | Complete beliefs and patterns. Beliefs include identity, content, project, memory type, creation, activation and decay-accounted timestamps, probability, confidence, alpha, beta, alpha0 and beta0. Patterns include identity, situation, approach, project, creation, activation count and success rate. |
| `learning.publication.assessments` | Experience/review/belief IDs, complete assessment payload and all calculated values. |
| `learning.publication.edges` | Owner, endpoints, relation and exact weight. |
| `learning.current` | Complete current experience snapshot, all three revision counters, candidate IDs and source update timestamp. |
| `learning.sources` | Every source version's complete payload, revision and creation timestamp. |
| `learning.reviewTimes` | Experience, review revision and original creation timestamp. |
| `learning.grounding` | Every belief's complete stored grounding value. |
| `learning.independentOrigins` | Every belief's stored independent provenance basis and reference, including absent or malformed legacy values. |
| `learning.itemKeys` | Every experience/local-key to PostgreSQL item-ID mapping. |
| `chunks` | ID, document, complete section path/content, parent and project. |
| `beliefVectors`, `chunkVectors` | Every owner ID and every component of its full stored vector. |
| `grounds` | Every chunk/belief pair and exact weight. |
| `beliefSources` | Every belief's complete ordered citations: chunk, document, quotation and explanation. |
| `history.heads` | Physical experience ID/project and all revision columns, independently of JSON payload decoding. |
| `history.sourceRows`, `history.reviewRows` | Experience, revision, source revision, creation timestamp and complete original JSONB payload, including old shapes and omitted fields. |
| `operations.reservations` | Token and original PostgreSQL reservation timestamp. |
| `operations.requestKeys` | Exact request key and token. |
| `operations.bindings` | Token, operation, original arguments, original semantic settings and binding timestamp. |
| `operations.plans` | Token and complete original raw plan, including captured selection when present. |
| `operations.savedReplies` | Token, exact step ID and complete raw saved answer, including the final operation result. |
| `operations.cancellations` | Token and first cancellation timestamp. |
| `operations.executions` | Every execution, including executions whose stop is acknowledged: PostgreSQL execution ID, owning operation token, registration and optional stop timestamps, program, PID, optional host label and its source, and actual PostgreSQL client address. |
| `embeddingOwners` | Owner token, project, original reservation timestamp and optional owning operation token. |
| `retirementClocks` | Every belief's first-defeat timestamp or explicit legacy-expired state. This is independent of source/activation time. |

Function-valued model maps use complete finite keyed rows with a fixed absent
default: no owner/key mapping, no history, and the empty zero-counter/no-
contribution cell for an absent incident. The adapter must enumerate every
stored key, including dangling rows. This represents finite database snapshots;
it does not claim to serialize arbitrary infinite Agda functions. Proof fields
are checked or reconstructed by the existing model adapter, not supplied as
caller assertions.

Acknowledged execution rows remain in the snapshot. A missing stop timestamp
means that physical stop is unconfirmed; neither a host label, a PID, a client
address nor elapsed time can substitute for that acknowledgement. Cancellation
tests compare those stored facts as well as the unchanged business result.
Execution identity/token values use the same canonical UUID strings as other
identities, and registration/stop times use the existing UTC timestamp codec.
The snapshot retains the model's field names without inventing another ID or
time representation.

Private row fields use their existing model record names, and nested public
records use their existing public encoding. A keyed row is `{"key":...,"value":...}`;
compound keys retain their tuple order. Vector rows are `{"id":...,"vector":[...]}`.
Finite-map envelopes contain `"default":"absent"` and all `rows`; "absent"
means the fixed type-specific default stated above. Standard tagged constructor
data is used only for existing private sum types, such as a retirement clock
or contribution key. It introduces no new business interpretation. Assessment
write expressions use `AssessmentEvaluation.evaluate` to obtain their actual
numeric contribution values; the adapter must also compare every stored numeric
column, rather than reconstructing it from the payload and concealing a bad
stored value.

Physical SQL tables are unordered. The fixed adapter orders their complete rows
deterministically while preserving multiplicity and every value. It preserves
ordered histories, public arrays, vector components, section paths, captured
selections and raw JSON arrays in their original order. It does not sort those
arrays, deduplicate rows, trim text, reconstruct missing history, normalize
probabilities or truncate vectors. The same adapter serializes the pure expected
world and the observed native world.

Ordinary public payloads retain their public numeric representation. Existing
standard typed f64/f32 conversion must round-trip every represented floating
value and vector component, without an epsilon, truncation or silent loss of a
required signed zero. This introduces no companion bit format or custom float
serializer. JSONB arguments and raw history retain the existing
PostgreSQL JSONB comparison boundary: object-member order and numeric spelling
are not independent stored values, while omission, null and array order are.
An unrepresentable snapshot is an explicit adapter failure with the original
raw snapshot retained. It cannot be repaired, sampled or accepted by dropping
the fields that failed to decode.

### Execution-bound external observations

Every observation names the actual operation token, registered boundary,
attempt, and selected item/candidate key when relevant. Its provenance points
to the retained native observation. The runner supplies only observations that
the actual attempt received or whose commit outcome was read back. An
unacknowledged commit is not automatically classified as rollback.

| Observation | Required facts |
| --- | --- |
| PostgreSQL allocation | Actual returned token/owner/node/item/chunk IDs and creation timestamps, tied to the allocating boundary and selected declaration. |
| PostgreSQL writer clock | The actual clock sampled under the relevant writer lock; keep it separate from reservation and identity-creation timestamps. |
| Database snapshot | The complete actual read-only snapshot and its scope, including concurrent changes seen by that read. A caller's desired snapshot is not a receipt. |
| File read | Requested/canonical path, project, complete source text or precise filesystem failure, tied to the fixed file-read protocol. |
| Provider | Bound backend/model/vector identity, original input and scope/owner, complete returned vectors or exact unavailability/failure. No expected vector or deterministic-provider assumption is permitted. |
| Owned worker stop | Actual operating-system wait receipt or its precise failure, tied by the harness to the execution ID, token, attempt and worker. An application cleanup label, a missing process found later, elapsed time or a final database acknowledgement is not a replacement for that receipt. |
| Indexed support | The actual supplied citation and explanation plus the indexed passage observed at commit; use existing scope/quotation checks, without a similarity acceptance cutoff. |
| Numeric calculation | The actual report data required by the existing numerical semantic boundary. Existing checked numerical functions validate it; the observed new posteriors are not accepted as an expected answer. |
| Database vector/text services | The actual configured pgvector and Unicode operations required by retrieval, preserving their existing precision and tie-breaking boundaries. |
| Configuration/event | Actual semantic settings, cancellation, owner revocation or source-change observation at its named boundary. These do not grant permission to change configuration or cancel automatically. |

Expected bindings, plans, owner rows, per-step answers, final saved answers and
public envelopes are computed from the original invocation and the reviewed
pure metadata intentions. They are not copied from newly observed database
rows. Existing rows in `initial_world` are inputs for replay, not fresh expected
outputs. Missing or surplus observations, wrong keys/models/scopes, or an
unconsumed receipt fail adapter validation with the exact boundary identified.
An observed final database state is never reclassified as an external snapshot
receipt to obtain the expected output without computing the intent.

The existing `ExecutionOwnership.WorkerExited.exited` requires the actual
`EmbeddingLifecycle.WorkerStop.stop` trace ending in a successful wait. Its raw
events do not contain the token, attempt or worker identity; the harness must
retain and check that association separately. The native worker currently
discards a successful exit status after waiting. Capturing the exact receipt
for this adapter is still required harness work, rather than an existing
application response field. Expected execution registration and stop rows
must be computed from those facts and PostgreSQL observations, not copied
from the final execution table.

### Required pure adapters

The table names actual existing pure functions, not new expectation algorithms.
Each adapter must compose the applicable business function with the reviewed
creating/owner/journal metadata intentions and the existing public projection.
The operation's executable script and `Run.evaluate` are excluded as oracles.
Requests rejected by existing structural decoding or fresh admission use those
actual pure validators and the existing diagnostic projection. Their body is
`not_entered`; they cannot acquire a fabricated successful operation or binding.
Malformed outer protocol messages remain covered at the separate retained
transport boundary, without inventing an operation constructor for them.

`IntendedGraphWrites.Evaluate.With.evaluate` currently composes pattern creation
and deletion and direct support, cause and contradiction writes with that
metadata boundary. A fresh pattern needs its actual PostgreSQL identity and
creation-time receipt; a completed replay needs no new allocation. Missing
required test observations return `ObservationError`, not a product correction
or an invented identity.
It computes the complete expected world at that database boundary, the typed
body result and semantic public outcome. Host execution registration and stop
acknowledgements must still be composed around it. The remaining family
adapters and public serialization are separate unfinished work; this is not a
complete evaluator for all public tools.

`IntendedPreparation.Evaluate.OperationReadback.evaluate` also computes the
expected `operation_outcome` read directly from the complete saved state. It
validates the submitted request, keeps its typed status and all world fields,
and needs no fresh clock, identity or other observation. An invalid request
keeps the body absent. The later public projection must use this control
request and the returned world for its full pending-execution diagnostics;
ordinary write-result formatting cannot substitute for that response.

`IntendedPreparation.Evaluate.ReservationIntent.evaluate` computes
`reserve_operation` from the admitted request key and saved reservation state.
A new key requires its actual PostgreSQL identity/time receipt; reusing a key
returns its original row and time without new observations. A captured fresh
identity that already exists is invalid test input. Missing facts remain
`ObservationError`, while malformed public requests keep the body absent.
The internal `reservationReadback` outcome retains both the key and typed
reservation result for later public projection; it introduces no new public
response format. A broken existing key stays a recovery result without making
up a replacement reservation. Whole-host and wire integration remain unfinished.

`IntendedPreparation.Evaluate.AssessmentIntent.evaluate` admits the three
assessment reads (`get_lesson_assessment`, `lesson_assessment_history` and
`explain_belief`) with their existing public field readers, then computes
`LearningQueryBinding.AssessmentReads.answer` from the complete original world.
The internal `assessmentReadback` retains the complete typed result, including
missing targets, invalid stored history or provenance, and invalid scores.
Those outcomes cannot become successful JSON null or an incomplete page.
Every read preserves the full world, and malformed admission leaves the body
absent. The later public projection must handle the retained outcome; this
adapter does not add or change a public wire format.

`IntendedPreparation.Evaluate.BasicIntent.evaluate` admits `get_belief`,
`list_beliefs`, `list_patterns`, `get_contradictions`, `get_evidence` and
`learning_capabilities`, then computes the existing `BasicReads.answer` and
its shared public encoder. It preserves complete records, source passages,
ordered pages and capability fields. Omitted belief selection returns all
matches; explicit pages keep the existing positive-count and offset rules.
The complete world is unchanged, including on malformed requests, whose
business body stays absent. No extra observations or expected values are input.

`IntendedPreparation.Evaluate.ExperienceIntent.evaluate` covers `get_experience`,
`get_learning_review`, `experience_history` and `pending_experiences` through
their existing public field readers and `ExperienceReads.answer`. Historical
source/review payloads remain the complete stored raw JSON, and pending reads
retain original ordering, exclusions and optional positive selection without
an invented default count. Every result preserves the complete starting world;
malformed requests leave the business body absent. These adapters introduce
neither external observations nor caller-supplied expected history.

| Public operation family | Existing pure business source | Required external observations |
| --- | --- | --- |
| `delete_project` | `ProjectDeletion.Registered.intended`, `expectedReply` | Existing original binding/plan/result; no invented fresh count. |
| `insert_pattern` | `PatternPublicationRecovery.createdPattern`, `GraphWrites.insertPattern` | PostgreSQL identity and creation time. |
| `delete_pattern` | `GraphDeletion.PatternRecovery.desired`, `answer` | Existing original request and saved result. |
| `record_support`, `record_cause`, `record_contradiction` | `DirectGraphRecovery.Business.checked` | Original endpoint/weight arguments. |
| `delete_belief` | `BeliefDeletionRecovery.Business.checked` | Actual locked publication time and checked numerical report. |
| `add_evidence` and library `delete_evidence` | `GroundingRecovery.Business.checked` | Actual locked publication time, stored chunk and numerical report. |
| `propagate_from` | `PropagationRecovery.Business.checked` | Actual locked publication time and numerical report; preserve its full changed-belief list reply. |
| `decay_all` | `DecayRecovery.Business.intended`, `checked` | Actual locked clock, original factor/project and stored accounted-time baseline. |
| `record_defeat` | `DefeatRecovery.Business.edge`, `FinalBusiness.checked` | First edge-commit clock and final locked posterior-publication clock, independently observed. |
| `sweep_expired_defeated` | `SweepRecovery.Business.checked` | Original user retention policy, actual saved selection and locked publication clock. |
| `clear_document` | `DocumentRemovalRecovery.Business.checked` | Original document/settings snapshot and final locked clock. |
| `load_document` | `DocumentLoadingRecovery.capture`, `Registered.prepare`, `DocumentReplacementRecovery.Business.checked` | Fixed file observations, PostgreSQL owner/chunk allocations, original previous-chunk snapshot, complete owned vectors and final locked clock. |
| `insert_belief` | `IndependentBeliefRecovery.Owner.intended`, `Business.checked` | PostgreSQL owner/creation receipt, original provenance, valid owned vector, indexed citation/passage and actual publication clock. |
| `record_experience` | `ExperienceSourceRecovery.Business.checked` | Actual item allocations, source-creation time and independent locked posterior-publication time. |
| `review_experience` | `ReviewPublicationRecovery.Business.checked`, `ReviewPublicationIntent.Fresh.intended` | Original raw and canonical declarations, saved owners, item/pattern allocations, prepared indexed support/vectors, review-creation time and independent publication clock. |
| CLI `reembed` | `BackfillRecovery.capture`, `itemIntent`, `finalItemIntent` | Original saved source selection/settings, each actual owned packet and concurrent-source/vector observation; count acknowledged writes and preserved concurrent vectors truthfully. |
| `stats`, `get_pattern`, `get_belief`, `list_beliefs`, `list_patterns`, `get_contradictions`, `get_evidence` | `StorageReadBinding.BasicReads.answer` | Actual consistent read view; preserve the whole world unchanged. Statistics and pattern lookup also cover their CLI/core entries without advertising new MCP tools. |
| `get_experience`, `get_learning_review`, `experience_history`, `pending_experiences` | `LearningQueryBinding.ExperienceReads.answer` | Actual consistent read view. |
| `get_lesson_assessment`, `lesson_assessment_history`, `explain_belief` | `LearningQueryBinding.AssessmentReads.answer` | Actual consistent read view and existing result projection. |
| `query_intervention` | `InferenceStorageBinding.InterventionRecovery.answer` | Actual consistent graph view and numerical report. |
| `query_relevant` | `PublicRetrievalRecovery.Run.answer` | Actual preparation and configured vector/Unicode dependency values. |
| `query_learning_context` | `PublicLearningContextRecovery.Run.answer` | Actual preparation and configured vector/Unicode dependency values. |
| `query_document` | `PublicDocumentQueryRecovery.Run.answer` | Actual configured query-vector result and database vector operations. |
| `learning_capabilities` | `LearningCapabilities.current` and the existing `ApplicationOutput.Encode` projection | No database mutation or invented capability value. |
| `reserve_operation` | `OperationControls.Reservation.execute` | Actual PostgreSQL reservation row; stable original request key. |
| `operation_outcome` | `OperationControls.Readback.answer` | Actual full binding/plan/prefix/result/cancellation state. |
| `cancel_operation` | `Recovery.Cancellation.intended`, `expectedReply` | Actual PostgreSQL cancellation clock; preserve committed changes, answers and completed results. |

Existing #152 must supply executable adapters for this complete list, including
the whole-operation metadata composition for prepared beliefs, documents,
reviews and repeated backfill. Their business functions and proof relations
already exist; that does not mean their complete test adapters already exist.
An unsupported family must be reported as unsupported and fail coverage. It
must never fall back to an identity expected world, an observed-world goal
validator, or a duplicate native implementation.

`IntendedPreparation.Evaluate.With.evaluate` computes the surrounding write
metadata from the actual decoded request and the retained settings, PostgreSQL
binding time and standard plan-encoding observations. It uses the existing
pure binding, plan and readback functions. It preserves original settings for
an already bound action and reads its saved outcome before checking a current
sweep policy. Invalid input returns a correction with the original world.
It does not run an effect script or perform business writes. The complete
adapter must still compose this result with the selected operation's
independent business intent and its public response encoding; the metadata
adapter alone does not satisfy any of the remaining whole-operation entries.

Its receipt fields are optional because an existing binding and plan need no
fresh timestamp or plan encoding. The evaluator uses the stored values on
those paths. If a genuinely new binding or plan lacks its required capture,
the evaluator returns a separate `ObservationError`. This is a test-input
failure: the runner must identify and capture the missing fact. It is never
encoded as Mimir asking the user to correct a valid product request, and no
zero timestamp, guessed ID or invented plan fills the gap.

The project-deletion composition is
`IntendedPreparation.Evaluate.ProjectDeletion.evaluate`. It takes the original
submitted value, decodes its token and project, prepares its metadata and then
computes `ProjectDeletion.Registered.intended` and `expectedReply`. It retains
the complete expected world, whether the body was entered, and the semantic
correction or operation readback. This uses neither a desired-world input nor
an effect-script evaluator. Public wire projection, executable transport
and the enclosing execution-registration/physical-stop composition remain
required before this entry can be marked complete.

`IntendedPreparation.Evaluate.ReadOnly.basic` and `experience` use the existing
read functions on the selected complete world. They preserve that world and
retain both the returned body value and the public value, including an actual
returned null. These typed read adapters cover statistics, pattern/belief
lookup and lists, contradictions, evidence, capabilities and experience reads;
the executable entrypoint decoder still has to select them from the original
request.

`scripts/formal/compare-outcomes.py --expected PATH --observed PATH` compares
the retained complete output of that adapter with a native observation. It
requires the world, body result and public reply on both sides; the native
file also retains its outer exchange separately. It reports every differing
path and returns a failing status for a mismatch or an incomplete envelope.
It checks the required snapshot tables and record shapes from the contract,
including every execution receipt field. It does not sort arrays, truncate
diagnostics, apply a numeric tolerance or
discard execution receipts. Physical table ordering and PostgreSQL JSONB
normalization belong to the shared typed snapshot adapter described above.
This comparator does not validate domain records or supply the missing #152
adapters. Its focused tests are comparison tests, not evidence that a native
operation has already been compared with an evaluated Agda outcome.

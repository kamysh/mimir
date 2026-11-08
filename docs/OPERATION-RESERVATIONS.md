# PostgreSQL-issued operation tokens

The storage API can reserve an operation token before business publication.
`reserve_operation(request_key)` returns `operation_token` and `reserved_at` directly from
PostgreSQL. The insert supplies neither value; the database uses its UUID and
timestamp defaults. UUID allocation is an external database guarantee.

The caller retains the returned token. `read_operation_reservation` looks up
that exact token and returns the stored reservation or absence. It does not
create a replacement token, infer an identity, retry automatically or filter
by age. Reserving another token does not expire an earlier one.

Keep one exact request key for one action and reuse it if the reservation reply
is lost. Repeating that key returns its original token and time. The key and
reservation publish together; concurrent losing allocations roll back.
Missing or blank keys are refused with repair instructions. The association
never expires or changes. See [request keys](OPERATION-REQUEST-KEYS.md).

Reservation changes only `mimir_operation_reservations` and its request-key
metadata. It creates no belief,
experience, vector or other business record. The additive migration creates
that metadata table; it does not change historical migrations. The existing
transaction and migration receipt rules still govern publication.

This storage foundation adds no MCP tool or CLI command. Whole-operation readback,
registered step order and client integration remain #122–#123 and
#85–#86. A reservation alone does not yet guard a business handler or establish
that all operations recover correctly. Public reservation-control recovery is
also an obligation of #163.

The Agda reservation model proves readback by the original key, unchanged state
and the original answer after a repeated reservation, and preservation
of the complete business state for every transaction receipt, including both
possible states after a lost acknowledgement. It contains no identity
generator or UUID uniqueness proof.

Isolated PostgreSQL verification checks persistence across a new service
connection, continued readback of old reservations, absence after rollback and
unchanged contents of every business table, including graph and vector data.

## Keeping the original request

After the calling interface validates a request, `bind_operation_request`
stores its operation name, arguments and relevant settings under the reserved
token. PostgreSQL supplies the binding timestamp. A binding is metadata, not a
receipt that a belief, document or other business record was published.

For example, a token first bound to deleting project A cannot later be used to
delete project B. A changed operation, argument or captured setting returns
`ChangedRequest` with the complete original binding. The caller must read that
binding and retain its original request, or explicitly resolve the old operation
before starting distinct work. The method never overwrites the earlier request
or allocates another token to hide it. `read_operation_binding` supplies the
same readback after reconnecting or losing a reply.

Request comparison uses PostgreSQL JSONB equality. Object-key order and
equivalent numbers do not change the request; array order does. No application
hash, truncation, expiry, retry delay or size limit is involved. The database
also rejects updates and deletes of an existing binding. Competing clients
cannot bind different requests successfully under one token.

The caller supplies only the settings that govern the admitted operation;
interface-specific capture belongs to #85–#86. Credentials are not operation
policy. This storage-shape constructor does not replace tool-schema validation,
and no public MCP/CLI handler is enabled by this change.

The binding model states that an existing request remains unchanged after any
transaction receipt, including a lost acknowledgement, and that binding changes
no business data. These are storage guarantees; completed business work still
requires its own atomic step and saved result.

## Publishing one step and its answer together

`commit_operation_step` checks the token's original request under a database row
lock before invoking any business change, even when that step already has a
saved answer. Unknown bindings and changed requests never invoke the callback.
The callback receives the stored request, including its original settings.

The helper owns one transaction containing the business change and the saved
answer. It returns the stored answer on both the first call and a retry. If
saving the answer fails, the business change rolls back. Competing callers
under the same token wait for the first transaction and read its answer instead
of applying the change again. No timeout or attempt limit is involved.

If a connection disappears around commit, keep the same token and step name.
Use `read_operation_step` or retry that same admitted step. An absent answer is
not permission to substitute a different request or silently reserve a token.

The formal constructor proves replay stability over the complete business
state and selected saved answer, and uses the existing recovery constructor to
cover interruption before or after publication. Its caller must still prove
that the business change matches an independently stated intended outcome.
This is one step's guarantee. Public registration/order integration remains #123,
the theorem for a complete sequence remains #84, and public admission/dispatch
remain #85–#86. No public write route is enabled by these storage helpers.

Tests delete actual private-fixture experience rows, reject saving an answer,
interrupt the test's own PostgreSQL connection, reconnect and retry, and race
two callers. They check both business data and the original saved answer.

## Keeping the same work and enforcing its order

`prepare_operation` captures selected item keys through a read-only database
transaction. It then saves the registered step order and those keys under the
original token. Reconnecting or retrying returns that saved plan without
selecting different work. An explicitly empty selection means that no items
matched; an omitted selection is an error. No selection count is imposed.

The core step writer accepts only a handle issued by this saved plan.
Passing a later step returns the next required step before running any change.
Repeating a completed step returns its original answer. A caller cannot obtain
a completion result until every planned step has a saved answer. The final
step uses `commit_final_operation_step`: its business change, step answer and
whole-operation answer share one transaction. The ordinary step writer refuses
the final step before running its change. The database rejects changes to or
deletion of a saved plan.

For example, if the first step completed and its reply was lost, the retry reads
that answer and proceeds to the second step. It cannot skip directly to the
last step or silently select a different set of rows.

These core checks do not yet connect the existing public handlers to saved
plans. That remains #123 and #85–#86. A completed plan alone is not proof that
its business changes meet the user's intended outcome; #84 and the concrete
operation proofs supply that separate obligation.

## Reading the original outcome

`read_operation_outcome` reads the original binding, saved steps and final
answer in one consistent database snapshot. It distinguishes an unknown token,
an unbound reservation, a request awaiting selection, unfinished work with the
exact next step and saved answers, an empty selection awaiting completion, and
a completed operation with its original answer. Supplying a changed request
returns the original binding even if the operation already completed.

Readback never writes data, recalculates a selection, substitutes another token,
or infers success from the presence or absence of business rows. A failed
database read returns an error requiring readback under the same token; it does
not return a guessed operation status. Inconsistent older saved steps require
explicit recovery with the saved answers, rather than repeating their changes.

For a nonempty plan, saving the final answer separately from the last business
change is refused. If saving either answer fails, the transaction rolls back
the final change and both answers. After a lost response, a new connection can
read the original result or retry the same final step without repeating its
business change. An explicitly empty plan has no business change and can save
its answer through `complete_operation`.

The formal atomic-publication law covers committed, aborted and both possible
lost-acknowledgement states. PostgreSQL tests reject only the final answer after
the step answer was inserted, then verify rollback of all three changes and a
successful retry. These remain core storage APIs; public readback is connected
by the later MCP and CLI integration issues.

## Atomic project deletion

The store and service project-deletion methods now use one transaction for
beliefs, patterns, their graph edges, belief vectors, document chunks, chunk
vectors and project learning records with their dependent history. IDs are
collected before their discovery roots are removed. Patterns remain excluded
from the returned count, which counts beliefs and document chunks.

The registered deletion has one commit boundary. `delete_project_operation`
accepts its checked step handle and saves the deletion count together with the
whole closure deletion and final operation answer. Retrying that token returns
the original count even though the rows have already gone. A failure while
saving the result rolls the entire deletion back.

The existing public interfaces still need their token binding from #85–#86.
Their current calls use the same atomic closure, but do not yet acquire a
saved operation result automatically. The independent ownership intent and
concrete recovery proof are described below. Mandatory dispatcher assembly is
still #74/#76; this change does not claim that every public request is protected.

The deletion intent now defines the resulting world directly: retain records
outside the selected project's ownership, remove edges attached to its roots,
and remove vectors using the IDs from the original world. It does not describe
an order of SQL statements. The shared recovery goal compares the whole result
and original deletion count with this intent.

General laws establish removal of the original belief and chunk vectors, graph
nodes, chunks, dependent edges, grounding links and current experiences. They
also establish preservation of each unowned node, chunk, edge and vector row.
Checking ownership against the original world matters: deleting the roots and
then observing no IDs cannot make leftover vectors satisfy these laws.

`ProjectDeletion.Registered.recoverable` now supplies the required recovery
value over the complete shared application world. For a new accepted deletion,
the intended result is the independently defined ownership removal with both
original answers saved. After any interruption covered by the shared execution
model, a completed retry reaches that same world and returns the original
deletion count. Separate general laws state that no original belief vector
remains and that saving the answers changes no part of the deletion's business
result. These are laws for every request and starting world, not chosen examples.

The registered deletion's only business argument is `project`; it has no tuning
policy to capture. Its model checks that the token's original binding has that
argument, no captured policy fields, and the registered single deletion step.
Missing or changed metadata opens request correction. A completed deletion
returns its saved answer without deleting again. A legacy record with only one
of the two final answers asks for outcome inspection and a user decision,
without inventing an answer or repeating the deletion. All correction paths
retain the complete original world.

The generic single-statement constructor requires the deletion's complete
state-and-reply idempotence proof. Its existing database contract covers
rollback and both possible publications after a lost acknowledgement. The
public MCP/CLI adapters and their tests remain #85–#86; dispatcher enforcement
remains #74/#76. The formal value alone does not install those adapters.

## Recovery of a saved sequence

The shared application world now includes the existing reservation, request-key,
binding, plan and saved-answer tables. It retains every business component in the
same world. Operation identities and times remain PostgreSQL observations.

The shared save-or-read rule preserves the first answer for a token and step.
Its general laws cover retries with a different proposed answer, preservation of
other steps, every business component, and the reservation/binding/plan inputs.
This is the common-state prerequisite from #228. The concrete deletion proof
now uses it; #74/#76's mandatory dispatcher remains separate.

The shared sequence constructor reads a checked saved prefix and executes only
the remaining work. Each step changes business data and saves its answer in one
publication; the last step also saves completion. An empty plan publishes its
result without changing business data. Re-reading completed work performs no
business write.

The general proof covers a stop at any script prefix and a lost reply at any
active write. At every write boundary it covers a confirmed commit, rollback,
and both possible states after a lost acknowledgement. Retrying to completion
has the same final state and reply as completing the original saved plan. The
proof also establishes that a completed execution exists and that advancing
work preserves the complete plan.

The constructor does not invent the intended business outcome. Its caller must
provide a separate pure intent and prove that completing the plan produces
that entire state and reply. The shared recovery goal remains unchanged.
Concrete operation proofs and the mandatory dispatcher assembly still have to
use this constructor; merely defining it does not complete #74 or #76.

## Reads and their complete answers

`Recovery.ReadOnly.operation` takes the independently defined complete answer
for a read and supplies its recovery value over the whole shared application
world. An identity state update alone, or a boolean read-only label, is not an
argument to this constructor. The caller must supply the answer's actual
contract for every input and world.

General laws establish that every interrupted read preserves all stored state,
including the operation journal, and that a completed retry returns that same
state and the complete original answer. No readiness condition or narrower
state projection is introduced. Individual query definitions and the mandatory
dispatcher still need to use this constructor in their own issues.

Belief paging now keeps its total and selected rows inside one explicit
read-only, repeatable-read transaction. If another client deletes a belief
after the count query, that response still returns the rows from the count's
snapshot; a new request sees the committed deletion. The transaction closes
after the response is assembled, or rolls back on an unfinished read. It adds
no timeout or result ceiling. The separate read-committed policy for learning
writes remains unchanged.

The formal page protocol retains both database observations and requires the
second to match the first snapshot. Its general result law then states that
the page total and rows are projections of that same stored state. PostgreSQL's
[repeatable-read guarantee](https://www.postgresql.org/docs/current/transaction-iso.html#XACT-REPEATABLE-READ)
is an external dependency, rather than a database algorithm to re-prove.
Direct evidence responses now use the same read-only transaction policy for
grounding links and every selected passage. A document removed after link
selection remains visible to that response's snapshot; a later response sees
its removal. Strongest-first ordering and explicit positive passage selection
are preserved. The formal read binding requires each passage to come from the
original link snapshot, and transaction cleanup applies to unfinished reads.

Contradiction reads likewise keep the selected pairs and their endpoint beliefs
in one read-only repeatable-read transaction. Removing an endpoint through
another connection does not remove it halfway through that response; the next
request observes the deletion. The Agda relation requires the endpoint read to
use the pair selection's snapshot, and its general law preserves the resulting
active contradictions. Completed and interrupted reads release their transaction.

Concrete recovery values now cover belief lookup, complete belief lists,
explicit positive pages, pattern lists, active contradictions, direct evidence
and learning capabilities. Their inputs contain only the request's identities
and filters. Their result definitions retain every public field, including
page totals and offsets and the supporting passages' complete contents. They
reuse the same public encoders as ordinary output.

For any represented initial state and interrupted read, a completed retry
preserves the entire application state and returns that request's complete
defined answer. The capability answer uses contract version 3, matching the
current MCP handler. These values are prerequisites for mandatory dispatcher
assembly in #74/#76; those issues are still unfinished. Evidence-enriched
retrieval has its separate operation proof in #132.

Ordinary CLI output prints selected belief and pattern text and supporting
document passages in full, including their original whitespace. Record
selection, ordering and numeric display do not impose a text-width ceiling.
Existing hook retrieval also passes the complete nonblank query and returns
all matching beliefs without fixed result counts. Injected knowledge and
working-belief messages retain complete selected content. No hook is installed
or enabled by this source change; the separate legacy Stop policy remains.

Experience lookup, current review, source/review history and pending selection
also have concrete read recovery values. Their full answers retain revisions,
payload fields, timestamps and explicit positive selection. Reading these
values leaves all business data and operation records unchanged.

Stored history JSON is included in the same shared application world. Current
review and historical rows preserve older payload shapes instead of decoding
them through the current schema. Project ownership comes from the physical
experience header, so project deletion also removes those raw history rows.

The two experience-history queries use one read-only repeatable-read
transaction. A revision and review committed by another client between those
queries become visible together on the next request. The formal binding pins
the review query to the source query's snapshot. Completion or interruption
releases the transaction. Mandatory dispatcher assembly remains #74/#76.

Assessment lookup likewise validates its target and reads its contributions
in one read-only stable transaction. A project deletion committed between
those queries cannot replace the original scores with neutral defaults in
the same response. The next request sees the missing target. Its Agda binding
requires the score query to use the target-validation snapshot. Concrete
assessment/explanation recovery remains #131.

Belief explanations also read the belief, incoming parents, review history and
both kinds of provenance in one read-only stable transaction. A concurrent
project deletion cannot mix the original belief with missing parents or
history. The next request observes the deletion. The formal binding requires
every component to use the initial belief snapshot, and the shared-view law
identifies the complete response with the explanation of that one world.
Completion and interruption release the transaction. Mandatory dispatcher
assembly remains #74/#76.

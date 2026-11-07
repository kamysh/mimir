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

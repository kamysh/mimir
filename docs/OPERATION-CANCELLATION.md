# Recording explicit operation cancellation

Cancellation belongs to the user. The judge must not cancel work automatically
to get past a problem, invent a replacement token, or silently abandon an
operation whose outcome is uncertain.

The storage method `record_operation_cancellation` records that explicit
decision. PostgreSQL supplies the timestamp, and repeating the call returns
the same record. The cancellation has no expiry. An unknown token changes
nothing and requires the original reservation to be recovered.

If an operation already has a saved result, cancellation changes nothing and
returns that original result row. This reports a stored fact; callers still
use `read_operation_outcome` to validate and describe completion. It does not
declare a damaged older journal complete merely because one answer exists.

For unfinished work, cancellation preserves every committed business change
and saved step answer. For example, if a defeat edge was committed before
propagation began, cancelling preserves that edge and its receipt. Further
steps under that token are stopped before their callbacks run. Outcome
readback returns the cancellation, original binding and complete saved answers
from one database view.

The cancellation transaction revokes embedding owners linked to that token.
Other operation owners and independent owners remain valid. Existing database
notifications wake preparation monitors after owner deletion. A prepared
result cannot publish after its owner was revoked.

## Ordering cancellation and publication

Registered writers first lock their reservation, then their binding and any
learning or owner rows. Cancellation locks that same reservation before
recording the decision and deleting owners. A write therefore either commits
before cancellation or finds the cancellation before changing business data.

Prepared belief and review publication read their linked operation tokens
before taking learning or owner locks. They lock distinct reservations in
UUID order, check cancellation, and then hold the preparation owner through
publication. An owner's operation association cannot change after allocation.
Cancellation does not acquire the learning advisory lock while deleting owners.

Database insertion checks also reject late bindings, plans, step replies and
embedding owners for cancelled tokens. They use the same reservation lock;
checking a flag without holding that lock would leave a publication race.
Cancellation records, original bindings, plans and answers remain immutable.

## Confirming every copy stopped

`CancellationDecision::Recorded` means publication was revoked. It does not
mean every worker stopped. The MCP and CLI cancellation handlers separately
wait for every registered execution's actual stop acknowledgement.

Each enclosing public request registers one PostgreSQL-issued execution ID
before starting. Its provider jobs borrow a private capability belonging to
that exact request and service. They remain owned children: the request cannot
acknowledge stopping until every child future is destroyed and its physical
cleanup is confirmed. Finding another active call with the same token grants
no capability. A standalone token-associated provider call registers its own
execution; it cannot borrow another service's request. Starting a child still
checks the durable completion/cancellation fence without adding metadata rows
inside the business operation.

Registration and cancellation lock the same
reservation row, so registration either becomes part of the wait or is refused
before work starts. The ID is read from INSERT RETURNING before COMMIT. If the
commit reply or the request itself is lost, the original owner retains that
ID; it reads back the same record rather than starting invisible replacement
work.

The owner destroys its body, confirms cleanup of its owned workers, and only
then records `stopped_at`. An interrupted registration that never started a
body can also be acknowledged after its transaction is settled. A stop write
may follow cancellation, and repeating it returns its original timestamp.
Execution records cannot be deleted or expired. Revoking preparation owners
does not remove these records.

Both the worker and canceller subscribe before checking their state. A worker
stops on its action's cancellation event or when its monitor reports a disconnect. The
canceller waits on actual acknowledgement events and rereads all outstanding
records. It does not poll or choose a wait limit. A disconnected or crashed
copy without a stop receipt keeps global confirmation pending. The original
owner can retry its acknowledgement after reconnecting; this protocol provides
no forced-clear command or inference from a process ID.

If the business result already completed, explicit cancellation still wakes
and waits for duplicate executions under that token. The original completed
answer is returned exactly; no cancellation row or business mutation is added.
New provider registration is already fenced by the saved final answer.

See [the public protocol](OPERATION-PROTOCOL.md) for pending readback, physical
cleanup errors and the required all-copies 2.3.0 upgrade boundary. No live
migration or rollout follows merely from these source changes.

The safe Agda model uses `ApplicationStore.World`, including the actual
cancellation rows and embedding owners. It proves preservation of business
records, original inputs and saved answers, stable cancellation time on retry,
and removal of token-owned preparation. Registered pattern and project
deletion admission refuses cancelled tokens. Mandatory application-wide
dispatcher enforcement remains #74/#76. Its execution-ownership extension
separately describes registered copies, actual body/worker exit observations,
and acknowledgements. A full stop confirmation requires every matching
execution row to be acknowledged; a pending row rules that confirmation out.
The host may wait indefinitely, so the model does not invent a termination
promise for an unreachable copy.

`ApplicationHost` places registration before the actual application run and
the request's physical stop acknowledgement after its reached world. Its
in-flight receipt also covers partial application runs: disconnect cleanup
derives its owned execution rows from their actual registration receipts,
including handlers that have not produced a tool reply. Local shutdown stops
those requests; it does not revoke their tokens or confirm other hosts.

The public handler requires this host receipt rather than accepting a bare
application trace. An unconfirmed cleanup is an error with the retained cause
and observed world. For explicit cancellation, a durable completion or
cancellation fence requires the separate all-copy stop trace before the host
can claim confirmation. Ordinary writes keep their exact original completed
payload; explicit outcome readback additionally shows pending copy identities.

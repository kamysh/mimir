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

## Remaining public integration

This is a storage foundation. It adds no MCP tool or CLI cancel command.
Public operation admission and associating all owned work with tokens remain
#85–#86. The public cancellation flow in #124 must stop and join every owned
worker before reporting cleanup complete. `CancellationDecision::Recorded`
means the durable decision and revocation committed; it does not claim that
every worker has already joined.

The safe Agda model uses `ApplicationStore.World`, including the actual
cancellation rows and embedding owners. It proves preservation of business
records, original inputs and saved answers, stable cancellation time on retry,
and removal of token-owned preparation. Registered pattern and project
deletion admission refuses cancelled tokens. Mandatory application-wide
dispatcher enforcement remains #74/#76.

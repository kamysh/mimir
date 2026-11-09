# A request for input stays pending

A write can discover a reason to ask the user before it finishes. For example,
deleting a belief can require recalculating other beliefs, and the calculation
can repeat without reaching its required result. The deletion must then roll
back together with every dependent change. Neither a step answer nor a final
operation answer may claim that deletion completed.

`RecoverableStoreStep` supplies the shared proof for this distinction. Its
decision is either a diagnostic or the complete proposed state and answer.
The diagnostic branch preserves the entire application state. The successful
branch publishes the data and both original answers together. Retrying a
saved operation returns its original answer instead of changing data again.
Cancelled work is refused, and an incomplete older pair of answers requires
readback rather than invented completion.

The calling operation must provide its own independently defined goal and
prove that its result satisfies it. The shared constructor cannot replace
that goal. The returned `RecoverableFor` value requires both convergence and
progress. Its execution evidence includes the actual complete application
stored state, the database's commit or rollback receipt, and the returned semantic
answer. Interruptions include a commit whose acknowledgement was lost.

This constructor receives the original admitted request. It does not replace
MCP/CLI decoding or the checked native step handle. Mandatory dispatcher and
public token integration remain #74/#76 and #85–#86. Concrete belief-deletion
and decay are completed separately under #138 and #141.

## Belief deletion keeps its original result

The registered belief-deletion writer now uses the stored original belief ID.
Deletion, candidate retirement, vector removal, recalculation of affected
beliefs and both saved answers commit together. A completed retry returns the
original `deleted` value. In particular, an original `false` must not delete a
belief created later with the same ID.

`BeliefDeletionRecovery` defines success from the complete initial stored state.
The selected belief and its references disappear, every affected posterior
satisfies its required equation, and all other stored components survive.
The calculator supplies raw results; the existing checker validates them.
A repeated incomplete calculation produces a request for a user decision,
with the complete original state preserved and no completion answer saved.

`RegisteredStoreAdmission` reads the reservation, original binding and saved
single-step plan before replaying any answer. The original arguments must
contain exactly a valid UUID `id`, with no per-request settings. A mismatch
explains what to correct and preserves stored state. The shared admission
wrapper preserves the complete-world recovery requirement; it does not use a
smaller view of the database as its goal.

The native entrypoint still receives the existing checked registered-step
handle. Public token handling and mandatory MCP/CLI dispatcher wiring remain
their existing follow-up issues; this storage writer does not replace them.

## Confirm rollback before returning a no-change diagnostic

The native shared writer now awaits rollback when its business callback
returns an error. An acknowledged rollback preserves the original error type
so the caller can open the corresponding user dialog. No completion answer
is saved.

If rollback cannot be confirmed, the response retains the original cause,
rollback cause and operation token, and tells the caller to read the saved
steps and operation outcome. It deliberately does not retain a diagnostic
type that the caller could mistake for an acknowledged no-change result.
There is no automatic cancellation, replacement token, retry timer or timeout.

Isolated database checks change a real record before requesting rollback,
verify that the record and pending status survive, and verify cleanup before
return. A second check terminates only its own disposable database connection
and verifies the readback response when rollback acknowledgement is lost.

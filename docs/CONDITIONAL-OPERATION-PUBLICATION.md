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
and decay goals remain #138 and #141.

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

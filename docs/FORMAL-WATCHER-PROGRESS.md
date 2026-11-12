# Operation rollback and fresh restart

A failed operation must roll back its partial business changes and release its
owned resources. A retry starts the original request from the beginning. The
application must not save a half-finished execution for later continuation.

Numerical calculation is an external operation. The specification does not
implement its solver, iteration count, stopping threshold or convergence proof.
It requires an unsuccessful calculation to leave business changes unpublished;
successful calculation results remain private until the operation commits.

This is a general requirement. For example, `record_defeat` prepares the link
and recalculation inside one transaction. It publishes both together. If either
part fails, neither is published. Retrying creates no duplicate from the failed
attempt because that attempt left no durable changes.

`Recovery.Recoverable` requires `rollbackInterrupted` and `rollbackFailed`, as
well as the successful-outcome theorem. `restartsFresh` follows from those
rollback proofs. Transaction cleanup receipts confirm that the owned handle has
been released; a cleanup diagnostic does not permit an unfinished cleanup.

Experience and review preparation accepts a transaction-scope proof alongside
the proposed steps. A rejected preparation can finish only in the closed scope;
a preparation ready to publish still owns its transaction. Preparing and
committing are separate typed boundaries. Preparation cannot commit, and a
commit either publishes the complete proposal or leaves the store unchanged.

Invalid requests receive a clear explanation and correction path. An operation
that needs a user decision must clean up before returning that request. A
recoverable review error ends its attempt safely without permanently stopping
the watcher. Stopping an attempt must also stop its active embedding work.
The owned-child stop effect returns only after that work has stopped. There is
no alternative cleanup-error return that allows the operation to finish while
the child continues running.

Belief and document preparation also uses a recovery controller. These steps
cannot publish business changes. Publication is constructed through the
separate transaction controller after preparation completes. Clearing indexed
data retains the existing fallback to the supplied path when the source file
can no longer be resolved; deleting the source file does not prevent clearing
its indexed data.

The review specification does not define statistics. Its incident-confirmation rule
requires evidence from the selected reviews' database readback rather than
deriving confirmation from report counts. Incident persistence is an external
operation; the specification defines the decision, not the storage implementation.

Every executing application state requires a recovery controller. Correction
states return without effects, and the request-ID wrapper only forwards the
underlying controller. Implementation and application-level verification follow
after the specification is finalized. Focused local compilation does not claim
that the implementation or deployment satisfies these contracts.

Final specification verification completed on 2026-11-12. The aggregate
`spec/Mimir.agda` checked successfully in the persistent interactive Agda
process, with no errors, warnings, visible goals or hidden goals. A subsequent
`Cmd_metas` inspection confirmed no remaining goals. The full stage output is
retained locally at `/tmp/mimir-final-agda-20261112-YbwcL1O9.log`.
Compiler fixes narrowed module aliases to the exports actually used and replaced
a natural-number comparison of history identities with UUID equality.
`git diff --check` also passed. These are specification checks; application
builds, installation and runtime verification were outside this stage.

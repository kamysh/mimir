# Operation rollback and fresh restart

A failed operation must roll back its partial business changes and release its
owned resources. A retry starts the original request from the beginning. The
application must not save a half-finished execution for later continuation.

The transaction analogy applies to every operation, including preparation
outside PostgreSQL: acquire resources, prepare privately, publish the complete
result once, and release resources. On failure, discard the private work and
finish cleanup before reporting a correction or asking for a user decision.
Restart means running the original request again, never loading a saved
execution position. State-machine states describe an active attempt; they do
not require database records for unfinished work.

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

Earlier baseline verification completed on 2026-11-12. The aggregate
`spec/Mimir.agda` checked successfully in the persistent interactive Agda
process, with no errors, warnings, visible goals or hidden goals. A subsequent
`Cmd_metas` inspection confirmed no remaining goals. The full stage output is
retained locally at `/tmp/mimir-final-agda-20261112-YbwcL1O9.log`.
Compiler fixes narrowed module aliases to the exports actually used and replaced
a natural-number comparison of history identities with UUID equality.
`git diff --check` also passed. These are specification checks; application
builds, installation and runtime verification were outside this stage.

The subsequent recovery completion connects every executing phase to the
mandatory `operation` registry. It adds private preparation and atomic
publication for review-created beliefs and re-embedding, requires active work
to stop before deletion, and carries informative semantic-search availability
through MCP, CLI and optional hook consumers. Notification cleanup runs
independently of reviews. Configuration creation and replacement have atomic
publication contracts. Log failures no longer prevent reviews; log rotation,
diagnostic read ceilings and the inter-batch delay are removed from the
application contracts.

For these changes, focused interactive checks of `CLIServiceBinding`,
`JudgeHostProtocol` and `McpRuntimeComposition`, including their changed
dependencies, completed with no errors, warnings or unresolved goals. Final
`Cmd_metas` inspection also reported no goals for each entry module. The shared
interactive transcript is retained locally at
`/tmp/mimir-local-recovery-development-20261111.log`.

The final structural coverage check passed for all 34 MCP operations, 30 CLI
commands, seven lifecycle groups, and the closed recovery registry. Its output
is retained at `/tmp/mimir-finish-spec-final-coverage-20261112.log`. This is a
structural audit, not a Rust refinement proof. The earlier aggregate receipt
has not been relabeled as verification of these later edits.

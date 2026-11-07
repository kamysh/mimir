# When the running watcher must make progress

The watcher has two different obligations: continue attempting work, and
confirm work that can be completed. A retry proves only the first.

## Continued attempts

One round includes the actual batch program and the daily notification check.
A successful, non-idle, non-degraded batch continues directly to the next queue
check, without constructing a timer or waiting for a timer acknowledgement.
An empty queue waits for a database work event, then scans again. It cannot
construct a timer. Incomplete-work paths still use the configured wait; their
replacements and removal of failure backoff are tracked in #67. No retained
wait is approved by this description.

The `Round` record and `roundTrace` proof in
[JudgeDigestComposition](../spec/Mimir/JudgeDigestComposition.agda) connect these
conditions to the actual repeated watcher program.
`successfulRoundNeedsNoTimer` constructs the continuation of every successful
non-idle batch without a timer premise, for any configured interval, failure
history, or digest reply. The timer acknowledgement on the remaining waiting
paths is an external scheduling condition, not a proof about the operating
system. `JudgeHost.idleBatchWaitsForWork` covers every idle batch and digest
reply. Its continuation requires an actual listener event; cancellation exits
the wait. A disconnected listener returns to the subscription phase, which
requires a fresh configuration receipt, acknowledgement and queue scan before
waiting again. A failed reconnection reports the missing prerequisite and
restart instruction. OS file events wake configuration reload at batch
boundaries, including an idle wait. Invalid replacements pause for a correction
event without overwriting the file or publishing the invalid settings.
`invalidConfigurationCannotStartBatch` excludes batch execution from that wait.
Each round uses the same admitted settings for review and the daily summary.

## Completing stable work after recovery

The completion guarantee requires a finite, ordered queue of eligible source
revisions and all of the following conditions:

- The project, configuration and source revisions stay unchanged. No new work
  is inserted into this queue during the guarantee.
- Each continued attempt selects a nonempty first group from the remaining
  queue, using the configured batch size and the actual pending-work call.
- Each selected revision receives a valid completed review. Final database
  reads confirm its identity and unchanged source revision, acknowledge that
  source revision, and show a newer review revision.
- Batch work and the daily notification check return. Any remaining waiting
  path receives its required external event. Productive batches have no timer
  prerequisite. The watcher is not stopped.

Under these conditions, every original revision is confirmed within at most as
many attempts as there were revisions in the original queue. For example,
seven stable revisions take at most seven such attempts; larger batches can
finish them sooner. This is a bound on attempts, not a wall-clock deadline.

`RecoveredRound` requires the selection and confirmation reads to occur inside
the actual host batch. `allRecoveredHistoriesFinish` proves the bound for every
history meeting these conditions, rather than exhibiting one successful path.
The continuation condition says arbitrarily many recovered rounds receive time
to finish. It does not assume that the whole queue eventually completes.
`everyStableRevisionEventuallyConfirmed` applies the bound to that continuing
operation and produces an actual watcher execution and database confirmation
evidence for every original revision.

Recovery means more than a database accepting connections or a model returning
HTTP success. A model that keeps returning invalid reviews, unavailable final
reads, repeated lock conflicts, changing source revisions, or an indefinitely
blocked notification operation does not meet these conditions. Temporary
failures can precede the recovered execution; its bound starts after recovery.

## Deferrals remain pending

A deliberately deferred revision that remains unchanged and unreviewed stays
excluded on the next selection. Merely waiting longer does not release it.
Correcting the source or reviewing it elsewhere releases that exclusion when
the next reconciliation observes the change. A deferred item need not be
included in the recovered queue while other eligible work progresses.

[JudgeSelection](../spec/Mimir/JudgeSelection.agda) proves both retention and
release for the actual reconciliation operation.
[ReviewObservation](../spec/Mimir/ReviewObservation.agda) proves that an
unchanged deferred, unreviewed revision cannot also have a confirmed review.
The specification therefore does not promise that a revision deliberately
deferred on every attempt will eventually be processed.

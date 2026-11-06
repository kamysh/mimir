# Stopping the judge and cleaning up its work

The signal controller previously asked an unspecified `dropWork` operation to
finish. Nothing required that acknowledgement to include the cleanup described
for the model process, MCP client or files. It also retained the work value
supplied before execution, which could omit a child acquired later.

[JudgeSignal](../spec/Mimir/JudgeSignal.agda) now receives the current work when
the signal wins the race. [JudgeSignalBinding](../spec/Mimir/JudgeSignalBinding.agda)
requires cleanup of that work before returning the existing stopped exit code.
The initial and current work must belong to the same owned future. Listener
installation still precedes polling the work, and listener failure starts no
work. The entry point requires an initial state with no acquired child or lock.

[JudgeCommandExecution](../spec/Mimir/JudgeCommandExecution.agda) connects this
controller to the parsed `judge run` and `judge watch` commands. A normal exit
requires the existing host or watcher execution. A stopped exit requires the
concrete cleanup receipts. Explicit native path bytes are preserved; textual
paths use the supplied UTF-8 operation.

## What the current work contains

[JudgeOwnedWork](../spec/Mimir/JudgeOwnedWork.agda) retains the point reached in
the component protocols, the MCP client and every owned file lock. Acquisitions
and partial progress come from those protocols' actual receipts and prefixes.
The lock list cannot repeat a live handle. Model and tool work require their
client and lock; saving requires a lock for the saved file's directory. Waiting
between batches requires an empty resource inventory.

The full inventory matters during finalization. A notification can hold its own
lock while the batch still owns the judge lock and MCP client. Cleanup closes
the client and releases every listed lock; it does not assume that only one
lock exists.

| Point at which work stops | Required cleanup |
| --- | --- |
| Startup before spawning a child | Drop the awaited library work and release any acquired locks. |
| MCP startup after spawning, before client construction | Derive child ownership from the startup prefix and invoke its direct-child guard. Once construction completed, use the normal client cleanup. |
| Harness model work | Wait for an already-started filesystem call to settle, drop pending I/O, use spawn/wait records to identify the unreaped child, invoke its process cleanup, and remove only a run directory whose creation was acknowledged. |
| API model work | Drop the outstanding request or its owned response body, retaining the adapter state already reached. |
| Tool request | Drop the owned MCP client, using its current child identity, and release the locks. The request may already have reached the service. |
| Saving a report or other private state | Wait for the filesystem call already running; never start the next normal write. Include its result when available, then close known descriptors. Remove the temporary file only when ownership is confirmed and the result is available. Release the client and all locks still owned. |
| Daily notification/read work | Drop awaited library I/O and release the client and locks still owned. Delivery may already have occurred. |
| Waiting between batches | No child or file-lock cleanup remains. Dropping the timer future is a supplied runtime operation. |

Harness and API cancellation also feed the existing
[backend composition](../spec/Mimir/JudgeBackendComposition.agda), preserving
the state already reached rather than resetting the adapter. MCP cleanup keeps
partial startup separate from a fully constructed client. Its ownership is
derived from [startup events](../spec/Mimir/JudgeMcpLifecycle.agda).

## Interrupted results stay unconfirmed

Cleanup preserves the previously observed report value. This does not say the
file on disk stayed unchanged: an interrupted rename may already have published
it. Cleanup does not write a successful review or invent a rollback. The stopped result retains the kind
of unconfirmed work: a model response, a particular tool request, a file target
or a notification. An interrupted save requires readback; cleanup does not delete
a possibly published target. A join with an unavailable result still means the
call finished, but does not authorize temporary-file removal. Temporary-file removal
requires the actual successful exclusive-create receipt.

`stopRequiresCleanup` proves this requirement for the complete command signal
path. The component receipts require their actual cleanup programs;
`cleanupPreservesReport`, `cleanupRetainsUncertainty`, `locksCleanupExact` and
`waitingNeedsNoResourceActions` state the corresponding general laws.

The native binding must supply genuine I/O observations and the actual current
work of the selected future. Standard future/file/socket destruction, signal
delivery, settlement of an existing filesystem call, and kernel behavior remain external guarantees. A checkpoint between calls means no background call is still running; an active call must instead carry its job identity. Joining that identity never reissues the call. Returned file handles whose result cannot be delivered remain the responsibility of the external task's guards. Invoking process
cleanup does not prove that every descendant terminated. These laws specify
valid application behavior; they do not prove native implementation
correspondence or promise that an external cleanup call always returns.

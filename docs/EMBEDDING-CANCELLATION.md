# Embedding cancellation ownership

Every configured embedding call from `MimirService` enters through
`OwnedEmbeddingBackend`. Each call receives its own owner and cancellation
source. Dropping the returned job requests cancellation, including when the job
was never polled. A stop handle can also cancel that particular call explicitly.
Stopping one call does not stop another call on the same backend.

Cancellation and completion use one ordered state transition. If cancellation
wins before a result is accepted, the caller receives a cancellation error, not
vectors. Once work has finished, another cancellation cannot revoke its result.
`Finished` describes work ending; the caller must still inspect its `Result`
for a provider error. Cancellation has no timeout, lifetime quota or retry count.

The existing `EmbeddingLifecycle.Ownership` model proves that stop and completion
release ownership, completion cannot undo an earlier stop, and another job's
ownership remains unchanged. Controlled native tests exercise cancellation before
starting, dropping an active job, independent simultaneous calls, cancellation
against a ready result, and ownership release after a provider error.

The local backend checks cancellation around cooperative work boundaries. An
already-running initialization or inference call still needs the owned-process
work in #70 to stop immediately. Operation revocation and publication fencing
remain separate work in #78–#79. This handle does not claim that those later
guarantees are already implemented.

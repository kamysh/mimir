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

Local model download, loading and inference run in an owned worker process.
Dropping an active request kills and waits for its worker, including during a
blocking native inference call. It does not wait for the next model batch.
The worker also watches its input pipe: a lost parent closes that pipe and ends
the worker without waiting for model progress. Successful workers are retained
for reuse; concurrent requests lease separate workers. There is no worker-count
limit, idle expiry, inference deadline or retry quota.

The private versioned protocol sends complete text lists and complete vectors.
The existing tokenizer, model, batching and mean-pooling arithmetic are reused.
Errors identify a private directory containing the worker's complete stderr;
there is no diagnostic truncation. Cancellation removes only that worker's
temporary downloads, preserving complete model files and other workers' files.

Both Mimir executables enter the private worker before loading configuration or
connecting to PostgreSQL. Rust SDK applications using local embeddings must
either call `embed::worker_entrypoint()` at their own synchronous entry point,
or explicitly select a compatible Mimir executable with
`embed::make_backend_with_worker` (or `MimirService::connect_with_worker`).
No installed executable is chosen implicitly.

The lifecycle model permits stopping at any loading or inference stage without
a model reply, and requires waiting for process exit after sending the kill.
Native tests cover blocked work, process reaping, isolation between workers,
complete result transport, reuse, and complete diagnostics.

Operation revocation and publication fencing remain separate work in #78–#79.
An owned embedding process alone does not supply those later guarantees.

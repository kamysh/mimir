# Notification persistence conformance

Contract-derived change, before implementation: `NotificationStorage.File.write`
delegates all three named files to `JudgeWrite.With.replace`, after its 1 MiB
admission check. `creationFailure` permits no removal after failed exclusive
creation. `cleanupRequiresCreation` grants cleanup only after creation;
`writeTemporary`, `syncTemporary` and `replaceName` close the owned file before
best-effort removal on failure. `afterRename` never removes a temporary path.
`committedRequiresReceipts` requires successful write, file sync, rename and
directory sync in order. `AtomicFile.directoryFailureIsUncertain` distinguishes
publication from durability acknowledgement.

Derivation: preserve serialization, size checking, UUID generation, names and
permissions. Extract a private byte-replacement helper. Exclusive creation
occurs before the cleanup-bearing block; that block contains only write, sync
and rename. On its failure, close then remove, returning the original error.
After rename, directory errors propagate without removal or rollback. Rust
scope drops the directory handle before the file handle, as in JudgeWrite.
No public interface, storage format or dependency change is needed.

Verification will exercise collisions, symlinks, failed rename, directory-open
failure after publication, successful private replacement, admission errors,
and reopening all three named files in the presence of an orphan temporary
file. Existing notification behavior fixtures will be selected where they
use disposable state and simulated delivery. Agda sources remain unchanged.

## Completed verification

All six new persistence tests passed, followed by all 21 notification tests,
including outbox retries, restart/recovery, digest cursors, OAuth cache and
rotation, and local SMTP/TLS fixtures. No external mailbox or provider was used.
Logs: `/tmp/mimir-notification-persistence-UI5JpgRA.log` and
`/tmp/mimir-alignment-notifications-5NUTGGB2.log`, both exit 0.

Creation collision/symlink, rename failure, directory-open failure after
publication, private-file replacement, serialization/size refusal, and named
file recovery were exercised. File-write/fsync and directory-fsync failures
were not induced; their branches were reviewed against the general checked
JudgeWrite contracts. This is implementation review plus executable evidence,
not a machine-checked Rust refinement theorem.

Only `crates/notifications/src/state.rs` and its new
`state_persistence_tests.rs` changed in this subsystem. Formats, filenames,
permissions, bounds, configuration and version 2.1.0 remain unchanged.
The overall receipt is [RUST-CONFORMANCE-VERIFICATION.json](RUST-CONFORMANCE-VERIFICATION.json).

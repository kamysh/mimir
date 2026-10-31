# Judge persistence and cleanup conformance

Approved scope: judge trace/report publication, temporary-file ownership,
failure cleanup and recovery, using disposable-file verification. Existing
formats, versions, installation, migrations, live models, production data and
system configuration are excluded.

## Contract mapping before implementation

The governing Agda sources are unchanged from the successful aggregate receipt
in `FORMAL-BEHAVIOR-VERIFICATION.json`.

| Obligation | Formal authority | Rust derivation |
| --- | --- | --- |
| Encoding and size admission precede entropy/filesystem effects | `JudgeNamedWrite.writeEncoded`, `writeBytes`; `encodingFailureNoEffects`, `oversizedNoEffects` | Preserve serialization and size checks before UUID generation and the replacement helper. |
| Failed exclusive creation authorizes no cleanup | `JudgeWrite.creationFailure`, `cleanupRequiresCreation` | Open the temporary file before entering the cleanup-bearing part of replacement. Return creation errors directly. |
| Write, file-sync or rename failure closes the created file, attempts removal of its temporary pathname, and preserves the original error | `JudgeWrite.writeTemporary`, `syncTemporary`, `replaceName`, `cleanup` | Keep these three operations in one fallible block; on failure drop the owned file before best-effort removal. |
| Successful rename ends temporary-name ownership; later directory-open/sync errors must not remove that pathname | `JudgeWrite.afterRename`, `afterDirectoryOpen`, `finishDirectory` | Execute directory open/fsync after the cleanup-bearing block. Return its error without pathname cleanup or rollback. |
| Success requires write, file fsync, rename and directory fsync acknowledgements in order | `JudgeWrite.committedRequiresReceipts`, `JudgeNamedWrite.successRequiresReceipts` | Preserve this operation order, O_EXCL/create_new, mode 0600, O_NOFOLLOW and O_CLOEXEC. |
| Recovery reads the named committed file and does not interpret orphan temporary files as reports | `JudgePersistenceComposition.Storage.Reading`; `JudgeStateOperations` | Preserve named-file decoding and bounds. Verify reopen with an unfinished temporary file. |
| Starting a new trace marks prior running traces interrupted; incident evidence survives unrelated successful work | `JudgeTraceStart`, `JudgeIncident`, `JudgeStateOperations.Began/IncidentExecution` | Existing paths already implement these decisions. Preserve them and exercise restart and existing incident/retention tests. |

## Implementation shape and correctness argument

Extract only the existing byte-replacement sequence into a private helper whose
arguments are the three paths and serialized bytes already present in the
formal protocol. No injectable production filesystem, retry system or new
persistence format is required.

Exclusive open is the only entry to the branch that may remove a temporary
file. The cleanup branch is reachable only when write, file sync or rename
returns an error, and it explicitly drops the file before attempting removal.
Once rename succeeds, control leaves that branch permanently. Directory errors
propagate without cleanup; successful return follows directory sync. This is
the same case split as the checked general creation/cleanup/commit laws.

Reports may have been replaced when directory synchronization fails. Returning
an error does not assert rollback. The existing public Result API and recovery
behavior remain unchanged.

This source-to-contract argument precedes Rust changes. The filesystem error
branches are already represented and proved in Agda. Disposable-file tests
supplement the argument; no new postulate or weakened specification is needed.

## Verification scope

Exercise exclusive-create collisions and symlinks, rename failure, directory
open failure after rename, successful private replacement, serialization/size
admission without filesystem mutation, and restart with interrupted traces and
orphan temporary files. Run the existing state/incident/retention tests and
runner fixtures. Retain all logs and check the scoped source diff/hashes.

## Completed result

The private `replace_state_file` helper now follows the ownership case split
above. Trace retention, incident selection, report formats and recovery
decisions remain unchanged. Six new disposable-filesystem tests supplement
the existing state and runner tests. The existing lock test now also uses a
unique temporary directory instead of deleting a predictable pre-existing path.

All selected checks passed on their first execution:

- 10 state tests, including the six new persistence tests:
  `/tmp/mimir-persistence-state-ncO0c3Fx.log`.
- Four runner fixtures, excluding `isolated_mcp_review_cycle` because it can
  access a configured database: `/tmp/mimir-persistence-runner-PWyL3cM5.log`.
- Rustfmt check: `/tmp/mimir-persistence-format-check-yt7JYHjg.log`.
- Scoped whitespace check: `/tmp/mimir-persistence-diff-check-993j0v_c.log`.
- Stage-input hash and scope audit:
  `/tmp/mimir-persistence-final-audit-20261031.log`.
- Source diff against this stage's input:
  `/tmp/mimir-persistence-source-diff-15oei53r.log`.

The audit confirms that `state.rs` is the only changed existing source input,
`state_persistence_tests.rs` is the only new crate file, and all 638 checked
Agda source hashes remain unchanged. Cargo manifests, lockfile, migrations,
previous startup work and crate versions (2.1.0) are unchanged.

File-write and file-sync failures were not induced by the executable tests;
their shared cleanup branch was reviewed against the general checked contract.
Directory-open failure was exercised after publication; directory-sync failure
was not induced. This is a source-to-contract review with focused tests, not a
machine-checked Rust refinement proof or an installed-binary verification.
No installation, live model call, production-data write or configuration change
was performed.

# Operational log writes and batch startup

A successful log write must save the requested entry, after applying the
configured entry limit and rotation rule. Returning a different set of small
files is not a successful write. A failed write must describe the contents
that could remain after the operations already attempted.

[OperationalLogSteps](../spec/Mimir/OperationalLogSteps.agda) defines the exact
numbered-file changes. When the current file has room, the clipped entry is
appended and archives are unchanged. Otherwise, the oldest slot is removed,
older slots are moved in descending order, and the new entry becomes the
current file. `rotationExact` proves the resulting archive order;
`planExact` connects those operations to the existing append rule.

For example, with a current file and two archives, rotation removes archive 2,
moves archive 1 to archive 2, and moves the current file to archive 1. The new
entry is then written into the current slot. The slot view records contents;
an absent file and an empty file both have no retained contents. Slots are
fixed numbered names in the configured directory.

[OperationalLogProtocol](../spec/Mimir/OperationalLogProtocol.agda) requires
completed lock, read, file-operation, append and descriptor-cleanup
observations. Every read and mutation uses the acquired handle. An independent
access policy proves that all complete attempts keep those operations inside
that handle's owned region, including failure paths. The native adapter must
relate these observations to the actual directory and file calls. No native
adapter instance or kernel implementation proof is supplied here.

Success retains the actual read made under the lock, all required successful
file changes, the exact clipped entry and descriptor cleanup. If a rotation
operation fails, the files are precisely a reachable prefix of the planned
changes. An interrupted operation may have taken effect; that alternative is
retained. If appending fails, the current file contains its prior contents
followed by a prefix of the clipped entry. That prefix can be empty or complete.
Neither failure permits unrelated replacement contents or continued rotation.
Failure before reading the files reports that their contents were not observed.

The existing per-file and total storage bounds hold for every retained state
in this bounded slot view. These are preservation laws from admitted bounded
slots; they do not assert that arbitrary existing files already satisfy a new
configuration's smaller limits. They also do not establish crash durability.

## Starting a judge batch

[OperationalLifecycle](../spec/Mimir/OperationalLifecycle.agda) now requires a
checked log attempt for the configured directory, file limit and retained-file
count. A success has the exact append result. A failed attempt cannot authorize
reviewing.

The [actual judge host protocol](../spec/Mimir/JudgeHostProtocol.agda) consumes
that checked attempt after loading configuration and before resolving the batch
state path, taking its judge lock or executing the backend. Logging failure
ends that attempt with the existing unavailable exit category. The general
`logFailureEvents` proof shows that only its optional one-shot error output can
follow; no state, database, model or tool work can follow within that batch
attempt. Watch mode uses this path for every batch. Configuration checking and
the separate daily-notification cycle retain their existing rules.

This change specifies application behavior and its external receipt boundary.
It does not change installed binaries, services, system settings or production
data, and it makes no claim that the native implementation has been verified.

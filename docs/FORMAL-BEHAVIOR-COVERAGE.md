# Mimir formal specification coverage

The specification describes application outcomes and recovery obligations. It
does not prescribe statistics, wire formatting, database query text, or other
implementation details.

[Recovery](../spec/Mimir/Recovery.agda) defines the shared recovery contract.
[ProjectDeletion](../spec/Mimir/ProjectDeletion.agda) gives a project-deletion
instance, and the MCP path uses that instance. The transaction contract assumes
that a committed transaction succeeds and its client receives the result.

Executing application states require recovery controllers. Preparation uses
read-only controllers; publication uses transaction controllers. Correction
states return without effects, and request-ID wrappers forward the underlying
controller. See the [recovery summary](FORMAL-WATCHER-PROGRESS.md).

The aggregate `spec/Mimir.agda` checked successfully on 2026-11-12 with no
errors, warnings or unresolved goals. Rust alignment and application-level
verification have not started; this check does not verify the installed binary.

# Mimir formal specification coverage

The specification describes application outcomes and recovery obligations. It
does not prescribe statistics, wire formatting, database query text, or other
implementation details.

[Recovery](../spec/Mimir/Recovery.agda) defines the shared recovery contract.
[ProjectDeletion](../spec/Mimir/ProjectDeletion.agda) gives a project-deletion
instance, and the MCP path uses that instance. The transaction contract assumes
that a committed transaction succeeds and its client receives the result.

Executing application states require recovery controllers. The exhaustive
`operation` registry supplies the proof for each preparation or publication
phase; `State.running` accepts only that registry entry's run state. Public
requests normalize into these phases. Correction states return without effects,
and request-ID wrappers forward the underlying controller. The coverage script
checks the request and registry cases alongside the advertised tools and CLI
commands. Agda checks the proof terms.

Preparation remains private; publication is all-or-nothing. Failure must restore
the original business state and release owned resources before a correction or
user decision is returned. Restart runs the original request again. There are
no stored execution checkpoints. See the [recovery summary](FORMAL-WATCHER-PROGRESS.md).

The earlier aggregate `spec/Mimir.agda` check on 2026-11-12 is a baseline receipt.
The subsequent recovery changes use focused interactive checks of affected
entry modules, reusing compiled dependencies. Their checks and the structural
coverage result are recorded in the recovery summary. These specification
checks do not verify the installed binary.

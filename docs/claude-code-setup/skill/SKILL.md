---
name: mimir
description: Use Mimir's persistent belief graph when prior decisions, lessons, errors or competing approaches could affect the work, or when a durable finding would save future investigation.
---

# Mimir

Mimir preserves reasoning across sessions: decisions, rejected approaches,
constraints and lessons learned from failures. A focused query can reveal why
an apparently reasonable solution was rejected, or how a previous session
resolved the same error. At startup, resume or after compaction, use it to fill
relevant gaps before reconstructing that reasoning from scratch.

## Retrieve what can change the decision

Use `query_relevant` with a focused `context` question and the project name when
known. Useful questions concern an unfamiliar subsystem, a surprising failure,
or a choice between approaches. Scope each query directly with `project`;
no session marker or `mimir hook set-project` command is needed for MCP queries.
An unscoped query can mix projects, so inspect applicability carefully.

The result is a set of beliefs, not a synthesized answer. Compare beliefs with
each other and current source or observations. Probability and confidence help
assess evidence; a high score does not make a stale belief authoritative.
Explain a material belief's effect on the approach in ordinary language.
Refine a poor query or use another source when retrieval does not help.
For causal impact questions, consider `query_intervention`.

## Preserve findings that will save future work

Record a concise, project-scoped belief when a durable, non-obvious finding
would change how a future session works. Include the lesson, its rationale and
limits. Good candidates include a verified constraint, a failed approach and
why it failed, or a correction likely to matter again. Avoid secrets, task logs,
duplicated instructions and obvious facts readily available in source.

Choose `memory_type` explicitly in `insert_belief`: `fact` for declarative
knowledge, `experiential` for a corrected approach or lesson. Calibrate
`probability` and `confidence` to the evidence. Use `insert_pattern` for a reusable
situation/approach pair when that representation fits.

`working` beliefs are temporary and excluded from cross-session retrieval. They
are not the default writing strategy in this guidance. If a task needs one,
track its ID and deliberately promote or discard it when resolved. The standard
installation has no Stop gate or automatic judge to do this for the agent.

When evidence confirms or supersedes a stored claim, use support/defeat links
where the relationship is justified. A belief that is irrelevant to this task
has not thereby been disproved. Conflicting results need investigation before
choosing which claim to update. Consult the available tool schemas for argument
names; do not invent links to satisfy a writeback ritual.

## Relationship to Muninn and reminders

If Muninn is installed, use it to find relevant implementations and repository
notes; use Mimir to recover reasoning that can change the approach. Read Muninn's
skill for checkout selection and note scoping.

The startup reminder explains this purpose. It does not run retrieval or enforce
calls, ratings, per-turn writes or a fixed exploration threshold. Use the tools
because the information can improve the work, and judge what they return.

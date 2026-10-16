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
When choosing an approach, use `query_learning_context` to retrieve relevant
beliefs and procedures with observed outcome counts. For causal impact questions,
inspect `explain_belief` and consider `query_intervention`: its projections are
conditional on the stored graph, not proof of causation.

## Explain retrieval to the user

After a retrieval, tell the user how useful the result was for the current task:
give a 0–5 score, one short reason, and what you will do with the information.
Use 0 when nothing usable was found and 5 when it directly resolves the question.
This is your assessment of task usefulness, not the belief's probability or
confidence. When several retrievals answer one question, a single assessment
of the combined findings is enough. Explain in plain language; do not repeat
raw JSON unless the user asks for it. For example: "Mimir usefulness: 4/5 —
this recalls an earlier decision; I'll check it against the current code."

## Choose the write that matches the evidence

For an incident that may change a later approach, use `record_experience` with
the situation, action, observed outcome and concrete evidence. The judge can
then form or revise a hypothesis through an atomic, experience-owned candidate
and review. Do not also use `insert_belief` or `insert_pattern` to state a
conclusion drawn from that same incident: the new node's standalone prior and
the queued review would count one report twice. Capture non-obvious results,
not every command or a raw transcript. Retrieval alone is not successful use.

Use `insert_belief` directly for an independently established durable constraint
or explicit decision that is not a conclusion inferred from a queued incident.
The MCP tool requires `provenance: {"basis":"user_instruction"|"document",
"reference":"..."}`. Give a specific user instruction or document location;
do not label an agent inference or incident report as an independent source.
`explain_belief` exposes this provenance. Older untagged MCP insertion calls
are rejected; capture their incident as an experience instead.
User requirements are authoritative constraints for the task, not statistical
hypotheses for the judge to approve or disprove. If both kinds of information
arrive together, keep the requirement direct and the observed incident in its
experience; state their different provenance. Do not turn a user report into
`tool_result` merely because it passed through an MCP tool.

Use a stable incident UUID and `expected_revision: 0` on first submission. Keep
the returned identity/revision with the task's receipt and carry that same UUID
into any later correction. Retrieve the existing experience, update the same ID
with its current revision, and describe what changed. If the earlier ID is lost,
look for the existing incident before creating another; different UUIDs for one
real-world event cannot be deduplicated automatically.
Retries must not create new independent observations. Include relevant belief
IDs and a pattern ID when an approach actually used them. State provenance honestly:
`tool_result` for observed tool receipts, `user_feedback` for the user's report,
`agent_report` for your own assessment. Use `unknown` when success is unverified.
When a user describes tests they ran, the source is still `user_feedback`.
Choose `tool_result` only when you actually observed the relevant tool output;
writing the user's report through an MCP tool does not turn it into tool evidence.
Never store credentials or sensitive raw logs.

After a retrieved lesson influences a later action, record that later action and
its *observed* outcome as a new experience with its own incident UUID, the used
`belief_ids`, and the used `pattern_id` when applicable. Record `unknown` if
the result was not verified. Correct this later experience under the same UUID
if the outcome changes. The act of retrieval or choosing an action is not a
success observation and must not increment pattern success counts.

The judge owns the causal assessment of queued observations. Do not add direct
support/defeat edges for that same evidence. If a standalone belief was already
inserted from this incident, disclose its ID as possible overlap to the judge;
the server cannot remove its independent prior merely from similar wording.
Do not present the belief and the experience as two independent confirmations.
If the installed server lacks learning tools, say that experience capture is
unavailable; ordinary belief retrieval/writeback remains usable. Do not claim the
learning loop ran merely because a belief was inserted. Use persistent writes
only within the user's authorized scope.

## Preserve findings that will save future work

Record a concise, project-scoped belief directly only when it is independent
of a queued experience and would change future work. Include the lesson, its
rationale and limits. Good candidates include an explicit durable decision or
an independently verified constraint. Capture failed approaches, successes and
corrections as experiences so their interpretation can be revised. Avoid secrets,
task logs, duplicated instructions and obvious facts readily available in source.

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
calls, hook-generated ratings, per-turn writes or a fixed exploration threshold. Use the tools
because the information can improve the work, and judge what they return.

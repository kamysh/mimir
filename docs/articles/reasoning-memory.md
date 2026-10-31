# Mimir reasoning memory with evidence and corrections

A useful memory for a coding agent includes the reason behind a decision. If a
project rejected an implementation because it violated an interface constraint,
the next session needs that constraint and its source. The memory also needs a
way to change when the interface changes or the original diagnosis proves wrong.

[Mimir](https://github.com/kamysh/mimir) is a persistent belief graph exposed
through MCP. It preserves decisions, rejected approaches, patterns and evidence
in PostgreSQL and Apache AGE. Agents can retrieve that reasoning across sessions
and check it against current source.

## Retrieving a decision in context

Suppose a service previously rejected a cache because it returned data from the
wrong tenant. A later task proposes adding caching to the same path. A relevant
memory would connect the earlier implementation, the failure and the condition
that made it unsafe.

An agent can ask `query_learning_context` for project-scoped reasoning:

```json
{
  "project": "example-service",
  "context": "Previous cache approaches for tenant settings and the constraints that rejected them",
  "limit": 5
}
```

The response contains relevant beliefs and matching procedures with recorded
outcomes. The agent still needs to read and reconcile them. Retrieval does not
establish that the earlier condition remains true or that the proposed change
will fail.

## Separating observations from conclusions

An observed failure and an explanation of that failure are different records.
The observation might be that a test returned another tenant's setting. The
explanation might be that a cache key omitted tenant identity. A later review
can discover that the test fixture was wrong, which changes what the observation
supports.

Mimir's experience ledger records a situation, action, outcome and evidence
references under a stable incident UUID. The record also identifies whether its
source is tool output, user feedback or an agent report. Evidence references are
provided by the caller; the database does not independently verify their
contents.

An agent or the optional judge reviews that incident. A new inferred belief or
procedure can be declared inside the review, giving it an identity owned by that
incident. Recording the same explanation first as an independent belief and
then reviewing the incident as additional evidence would count one report twice.
The documented workflow keeps those paths separate.

Direct belief insertion remains available for an independently established
source. Its MCP interface requires provenance identifying a user instruction or
document. That makes the distinction inspectable instead of depending on the
reader guessing how a belief entered the graph.

## Correcting an incident

If the cache failure was misdiagnosed, the caller corrects the same incident UUID
using its current revision. Mimir preserves the previous versions, invalidates
the prior review's active contribution, and makes the changed observation
available for another review.

Reviews also have revision checks. A stale review cannot silently overwrite a
newer one. Applying the same accepted request again does not add its evidence
again. This protection depends on preserving the incident identity: submitting
the same real-world event under unrelated UUIDs is not semantic deduplication.

Corrections retract review-owned contributions. They do not erase independently
inserted knowledge merely because its wording resembles the corrected report.
The history remains available through `experience_history`; `explain_belief`
connects a belief to provenance and active reviews.

The
[ledger implementation](https://github.com/kamysh/mimir/blob/d5cf1704f90f82db867ba7837e8a0a90a6a72bbc/crates/core/src/store/learning.rs)
contains the transaction and revision checks behind these operations.

## Representing relationships

Beliefs can support, defeat or contradict one another. Causal hypotheses use a
separate relationship. A failed observation can therefore change the reasoning
connected to it, rather than remaining an isolated paragraph that every future
session must interpret from scratch.

Mimir also offers intervention queries over stored causal hypotheses. Those
queries calculate consequences under the recorded graph; they do not establish
that a causal explanation is true. Likewise, an agent's reported success alone
does not demonstrate a successful intervention.

## Using the memory during work

Mimir is available to clients including Codex and Claude Code. The client
launches the MCP server, which connects to the configured database. A separate
optional judge can review queued experiences when explicitly launched. Ordinary
installation does not start that judge or schedule maintenance.

The agent integration includes guidance on when past reasoning can inform a
decision. Having a connected memory tool does not guarantee that the model will
consult it or follow the retrieved lesson. The workflow asks the agent to check
relevance and source evidence before acting.

The graph can run locally. Optional hosted embeddings and a configured cloud
judge send their selected inputs to the configured provider. Details and setup
are in the [repository](https://github.com/kamysh/mimir) and
[runner guide](https://github.com/kamysh/mimir/blob/main/runtime/README.md).

Mimir is written in Rust and licensed under Apache 2.0. Its companion
[Muninn](https://github.com/kamysh/muninn) retrieves code and repository knowledge;
[Kryzhen](https://github.com/kamysh/kryzhen) supplies PostgreSQL migrations.

This article was drafted by an AI assistant from the project's source code and
documentation. The tenant-cache example is illustrative.

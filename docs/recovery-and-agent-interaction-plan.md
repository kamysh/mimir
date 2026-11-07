# Recovery enforcement, agent interaction, and removal of arbitrary restrictions

Status: implementation in progress. The contracts below are required targets,
not a claim that the complete plan is implemented.

Prepared on 2026-11-06 against the local `origin/main` reference,
`a402f463441c677db82863fe4805e30fbfbe7c55`. Start implementation from a fresh
worktree based on `origin/main`, without reusing the discarded implementation.

This plan has three required outcomes:

- Ready work proceeds without arbitrary waits, caps, or timeouts.
- Incorrect MCP requests receive an explanation and a correction path, while
  the application continues running.
- Every dispatched operation carries a concrete recovery proof, with Rust
  behavior checked against its intended result.

The implementation work is split into [108 issues, each scoped to no more
than one hour including focused verification](recovery-and-agent-interaction-issues.md).
The index links every issue and its prerequisites. Before the first PR, bump
the version to **2.3.0**; do not create a tag yet.

The [operation catalogue](OPERATION-CATALOGUE.md) records each public operation,
its intended result, permitted writes, retry requirements, and existing source
and model locations.

## 1. Establish the baseline and the acceptance conditions

Use a fresh, dedicated worktree from `origin/main`. Preserve the existing
checkout and unrelated work.

Create two working inventories:

| Inventory | Required information |
| --- | --- |
| Operations | Public name, inputs, required prerequisites, intended result, affected data, transaction boundaries, retry behavior, proof, Rust handler, verification |
| Restrictions | Exact location, affected behavior, default/value, removal method, and any exception proposed for user approval |

The operation inventory covers MCP tools, corresponding CLI commands, and
background paths that perform the same work. The restriction inventory covers
the whole application: core, embeddings, database access, MCP, CLI, judge,
notifications, configuration, scripts, tests, and formal models.

Search matches are candidates for inspection, not proof that every occurrence
is a cap. For example, allocating a vector with capacity is different from
truncating its contents.

Completion is defined by observable behavior and enforced connections.
Creating modules or increasing proof counts does not count as completion.

## 2. Address the reported five-minute wait first

The baseline contains:

- A watcher interval default of 300 seconds.
- A sleep between watcher iterations.
- An escalation to at least 3,600 seconds after repeated failures.

Trace the reported nightly failure through that path and identify what should
have made the next operation ready. Preserve the distinction between the
user-reported cause and what local reproduction establishes.

Replace the delay according to actual readiness:

- After completing work, immediately check for further eligible work.
- When idle, wait for a work-availability event rather than a polling timer.
- Subscribe before checking the queue, so work arriving between checking and
  waiting cannot be missed.
- After reconnecting, check the durable queue again.
- Configuration changes must wake work waiting for corrected configuration.
- Explicit stop or cancellation must remain effective while waiting.

For PostgreSQL-backed work, the proposed mechanism is `LISTEN/NOTIFY` plus a
durable queue check. Notifications wake the watcher; the database determines
what work exists. Configuration changes use file events.

Removing the timer must not produce a busy loop that repeatedly submits
unchanged, unusable work. Missing information or a required decision produces
an actionable waiting state, with an explicit way to resume.

Verification must demonstrate that newly ready work proceeds without the
five-minute delay, including work arriving while the watcher enters its idle
state. These tests use controlled events, rather than waiting five minutes.

## 3. Make correction an ordinary part of MCP interaction

Place a shared validation and correction boundary before business execution.

It must handle:

- Missing mandatory fields.
- Unknown or misspelled fields.
- Wrong types, malformed identifiers, and invalid values.
- Conflicting arguments.
- Missing, stale, or wrongly scoped references.
- Calls made before their prerequisites exist.
- Repeated requests and requests whose previous outcome is uncertain.

Incorrect requests must not terminate the server, end an unrelated review,
silently substitute defaults, or report successful execution.

The response must tell the agent:

| Information | Example |
| --- | --- |
| What happened | "This request needs correction; no business changes were made." |
| Where | `arguments.probabilty` |
| What is wrong | "Unknown field." |
| Expected input | "The field is named `probability`." |
| How to continue | "Correct the field name and submit the request again." |

For a missing value, explain what information is needed. Do not invent it. For
a stale revision, explain which read retrieves the current revision and how
to resubmit safely.

Interaction means a concrete loop: **agent submits → Mimir explains the
problem → agent corrects → Mimir validates again → normal execution**.
Ordinary correction replies do not require an LLM inside Mimir.

Malformed JSON or an invalid JSON-RPC envelope still requires a
protocol-compliant diagnostic. The server continues accepting subsequent
requests whenever the connection remains usable.

The calling agent must be told to ask the user when correction requires a
business decision. Mimir must not silently make that decision. This includes
the previously established requirement that missing embedding or grounding
cannot become permission to publish an ungrounded belief.

Verification will submit incorrect requests over the real MCP connection,
inspect the response, submit corrected requests on that connection, and check
the resulting data.

## 4. Remove arbitrary restrictions throughout the application

Remove restrictions by default. Moving a hardcoded restriction into
configuration does not satisfy this requirement.

The inventory includes:

- Execution and network deadlines.
- Polling delays and failure backoff.
- Retry, attempt, model-call, and iteration quotas.
- Result ceilings and default result truncation.
- Input, evidence, message, and collection truncation.
- Embedding truncation and artificial batch ceilings.
- Diagnostic and history truncation.
- Notification deadlines and retry limits.
- Restrictions inherited from application-supplied dependency settings.
- Equivalent restrictions encoded in Agda or test fixtures.

Already observed examples include the ten-result belief-page ceiling, the
embedding download timeout, propagation's iteration cutoff, and diagnostic
truncation.

Each removal must preserve truthful behavior. In particular, propagation
cannot exhaust an iteration counter and return unfinished values as a
completed result. Its stopping condition must follow the operation's
numerical meaning. If that meaning is insufficient to establish completion,
expose the design question rather than inventing another number.

Proposed request semantics are explicit:

- Omitting a result limit requests all matching results.
- A supplied limit must be a positive integer and represents the caller's
  requested selection.
- `limit=0` produces a correction response.
- The server imposes no additional maximum or hidden default selection cap.

Domain validity checks remain meaningful: for example, a probability must be
a valid probability. They must not conceal restrictions on work or accepted
content.

**Any restriction proposed for retention requires a separate explanation and
explicit user approval.** That explanation must contain its location, exact
behavior, concrete scenario, evidence supporting it, alternatives, and
consequences of removal. Existing settings, dependency defaults, and provider
constraints are not automatically approved exceptions.

External constraints must be reported honestly. They must not cause silent
truncation or justify an invented application limit.

## 5. Define the minimal shared recovery contract

Introduce one shared `Recoverable` interface and integrate it into existing
operation modules.

Its required obligations are:

- A pure `intended` function describing the user-visible result.
- Statement semantics tied to actual before-and-after worlds.
- A generic definition of interruption covering every execution boundary.
- Convergence after interruption and completed retry.
- A progress obligation for valid, admitted requests under their declared
  prerequisites.

The goal is defined centrally from observable state and `intended`. It is not
a freely supplied predicate.

The observable state must include the relevant business data and operation
outcome. It cannot be replaced with `⊤`, an empty projection, or a view that
hides affected records. Operations must also preserve unrelated data.

Single-statement operations require idempotence. A single insert does not
qualify merely because PostgreSQL executes it atomically. Where existing
identities or revision checks do not make retries safe, identify the required
logical-operation identity and receipt mechanism before implementing it.

PostgreSQL's UUID generation and database atomicity remain external contracts.
This task will not reprove those facilities or standard formatting, parsing,
hashing, or floating-point representation.

Malformed input connects to the same contract: correction preserves business
state, and a corrected request must pass through ordinary admission.

## 6. Make the concrete dispatcher enforce the contract

Replace the raw-script entry constructors with the required form:

```agda
operation : (r : Public.Request) → Recoverable World (Input r)

data State : Set where
  running : ∀ r → RunState (operation r) → State
```

Every case of `operation` must select an actual, concrete proved operation.

There will be no caller-supplied certificate catalogue, unchecked fallback,
or alternative dispatcher accepting raw scripts. Missing cases and missing
proofs must fail type-checking.

Project deletion is the first complete proof example because its intended
result is clear: remove the project's ownership closure, including dependent
vectors, while preserving unrelated data. Its implementation and proof must
agree on transaction boundaries and retry results.

Then cover the remaining operations using their actual semantics. Read-only
operations also need correct-result and no-mutation behavior; declaring their
intended world unchanged is insufficient to establish that their replies are
correct.

An unfinished operation table remains explicitly unfinished. It cannot be
presented as application-wide enforcement.

## 7. Mirror the enforced operation table in Rust

Route dispatch through typed registered `Operation` values. Each registration
identifies its validated input, handler, statement boundaries, and verification
case.

MCP and corresponding CLI paths must reach these registered operations. A
parallel string-based dispatch or direct store path must not bypass the
contract.

Connect the existing coverage checker to an explicit mapping:

**advertised tool → decoded request → concrete Agda operation → Rust
registration → boundary tests**

Derive the operation set instead of fixing its size at 34.

Compare named boundaries and their correspondence, rather than relying only
on equal counts. Include conditional and repeated work so helper statements
cannot escape verification.

## 8. Check implementation behavior against intended

Use disposable databases and the registered operation table to drive the
required differential tests.

For each operation:

- Establish the same starting world for the specification and Rust.
- Execute normally and compare the observable result with `intended`.
- Interrupt at its registered transaction boundaries.
- Retry according to the operation contract.
- Compare the final data and reply with the specified result.
- Check that unrelated data remains intact.

Expose the specification through an Agda-owned executable test interface.
Generated compiler output remains build output; the harness does not depend
on inspecting generated Haskell internals.

Use existing standard parsing and serialization at that boundary. Do not
build another low-level formalization exercise.

Also test that the enforcement detects deliberate omissions: removing a
proof, bypassing registration, omitting a boundary, or substituting an
incorrect intended result must make the relevant check fail.

## 9. Verify and prepare delivery

During development, run checks appropriate to the changed behavior. After
integration, run the aggregate Agda check, mechanical coverage checks, Rust
checks, and required integration tests once against the completed snapshot.
Repeat them only when changes or failures justify it.

The final report must identify:

- Which workflows were exercised successfully.
- Whether malformed calls were corrected over actual MCP connections.
- Whether every dispatched operation has a concrete proof.
- Whether boundary tests agree with the specification.
- Every remaining restriction and its explicit approval.
- Any unresolved or unverified behavior.

A successful build or version string is not evidence that the watcher
completed a review.

Before the first PR in this series, bump the application version to **2.3.0**
and update corresponding current-version references consistently. Do not
create a tag yet. Preserve historical release references.

Installation and release form a separate approved stage: static build,
local installation, configuration compatibility,
and observation of the actual affected workflow. System configuration, live
migrations, pushes, tags, and publication require their applicable explicit
permissions.

## Implementation order and current authorization

The first implementation stage is the five-minute watcher delay and its
directly connected behavior, accompanied by the application-wide restriction
inventory. The subsequent stages complete corrective MCP interaction,
restriction removal, and concrete recovery enforcement.

This document is the planning deliverable. Saving it does not authorize
implementation, installation, deployment, or publication. No exception to
restriction removal is approved by this plan.

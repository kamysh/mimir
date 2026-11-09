# Recording and correcting one incident

The registered `record_experience` storage entry saves the source change and its
original answer in one transaction. The incident UUID remains the one supplied
by the caller. PostgreSQL assigns new learning-item UUIDs on the same locked
connection; retrying an existing local item key retains its original UUID,
source reference and author.

For example, one operation records incident A at revision 1. A second operation
corrects A to revision 2. Retrying the first operation returns its saved revision
1 answer, while the current source stays at revision 2. Retrying the second
returns its original revision 2 answer. Neither retry adds a source version or
another incident.

A genuine correction appends a source version and preserves earlier source and
review payloads. It removes the old review's active contributions and owned
relationships, then recalculates affected beliefs in that incident's project.
Other projects and unrelated records remain unchanged. Source-history times
come from the publishing PostgreSQL transaction; posterior calculation uses the
original operation's reserved time, preserving the existing clock policy.

An identical source may also be submitted under a different token. Its original
source answer is saved for that token without publishing another revision.
Tentative item allocations made while checking it are rolled back before the
answer is saved, matching the direct storage entry's replay behavior.

Malformed source fields return correction guidance. A stale revision directs the
caller to the current experience and history. A request already bound to a token
cannot be rewritten: read its original binding and outcome, then ask the user
whether to cancel unfinished work and reserve the corrected request. A refused
request saves no source change or completed answer. If saving the final answer
fails, the source version and item ownership roll back together.

`ExperienceSourceIntent` defines the complete source, immutable history, item map,
affected posterior state and answer from the submitted incident and starting
store. `ExperienceSourceRecovery.Registered.operation` connects that meaning to
the original reservation, binding and saved plan. Its input is only the token.
PostgreSQL times and per-key allocation replies are observations in the actual
execution relation, rather than extra caller fields or an expected answer.
Incomplete allocation observations cannot represent a completed fresh attempt.
The progress proof follows the finite allocation program using an external
PostgreSQL capability; it does not assume a desired result or prove PostgreSQL's
UUID generator. The recovery proof covers interruption before publication and
after a commit whose reply was lost, including replies that differ on retry.

The full instance is available for the mandatory public dispatcher in #74/#76.
Those integration issues still need to route execution through it; public token
interfaces remain #85–#86. This change adds no tool, policy, quota or timeout.

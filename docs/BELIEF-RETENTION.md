# User-owned belief retention

Sweeping requires the user's `[retirement].grace_hours` configuration. Mimir
chooses no period when it is missing, and MCP requests or CLI flags cannot
override it. Ask the user for the value; do not choose one from an example or
invent a default.

```toml
[retirement]
# Set grace_hours only after the user chooses the period, measured in hours.
```

An absent, empty or invalid policy pauses sweeping before candidate reads or
deletion. MCP and CLI return `needs_input`, identify the configuration field
and ask for a user decision or repair. Other core tools remain usable.
An explicitly supplied invalid policy is also reported by `mimir config check`;
an omitted policy is allowed when sweeping is not needed.

The period must be a finite nonnegative number that the clock's duration type
can represent. No additional maximum is chosen by Mimir. Conversion uses the
clock's precision rather than rounding to whole minutes or saturating an
integer. Zero means immediate eligibility only when explicitly configured by
the user; an agent cannot select it in a sweep request.

Remove the old `grace_hours` MCP argument and `--grace-hours` CLI flag. The tool
description and command help name the required configuration. A wrong request
gets a correction; it does not silently fall back to 24 hours or another period.

A service uses the configuration captured at startup. After the user repairs
the policy, reload or restart the MCP connection to use it. This source change
does not edit the live configuration or restart a client.

The registered sweep saves its original project, probability threshold and
configured policy before doing business work. An unfinished operation pauses
if that policy has changed or is unset. The agent must open a user dialog to
restore the original policy or explicitly cancel unfinished work before
starting a separate operation. It cannot rewrite the saved request, choose a
new period or cancel automatically.

Selection, deletion of the entire selected set and its vectors, survivor
recomputation, and the original selected IDs and count publish in one
transaction. Before that transaction commits, no selection is durable. After
it commits, retry reads its original answer even if configuration has changed
or a newly eligible belief now exists. It does not run another sweep under
the same token. PostgreSQL supplies the actual selection and publication
times while the transaction holds Mimir's writer lock.

Completed results from the old per-belief plan remain readable. An unfinished
old plan pauses for a user decision; it is never silently converted into the
new plan. The currently advertised MCP and CLI sweep also use the atomic
transaction. Public operation-token routing remains the separate #85–#86
interface work; the registered core path does not claim that wiring is done.

The shared admission check is required before MCP or CLI execution. Its
configuration correction has no application events. A completed operation
witness includes successful admission for new work. An already completed
operation replays its original result before checking current policy.
The connection contract ties the effective policy to the parsed configuration.

Nine focused native tests cover missing and malformed policy, explicit zero,
subminute precision, project scope, retained data, the retired override and a
continued real MCP session. They use only the owned disposable fixture.

`SweepRecovery` states the whole-store outcome and proves retry convergence
for the registered publication, including both possible states after a lost
database acknowledgement. The goal requires every selected target and vector
to be removed, all affected survivor equations to hold, unrelated data to be
preserved, and both original answers to be saved. Configuration and clock
observations belong to actual effect replies, so a refused uncommitted attempt
can later use repaired configuration while a committed answer remains fixed.
Exact old-result readback reuses the operation-control read-only certificate.

Four focused database cases check atomic multi-target deletion and replay,
policy changes and restoration, old completed versus unfinished plans, and an
actual repeated-count refusal that rolls the entire deletion back. Two actual
MCP exchanges check multi-target legacy expiry and correction for missing
retirement metadata. These checks add no timeout, artificial failure hook or
selection limit.

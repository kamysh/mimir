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
does not edit the live configuration or restart a client. Saving the original
policy with retryable selections and pausing a changed policy remain #142.

The shared admission check is required before MCP or CLI execution. Its
configuration correction has no application events. A completed operation
witness includes successful admission, so an unset policy cannot satisfy it.
The connection contract ties the effective policy to the parsed configuration.

Nine focused native tests cover missing and malformed policy, explicit zero,
subminute precision, project scope, retained data, the retired override and a
continued real MCP session. They use only the owned disposable fixture.

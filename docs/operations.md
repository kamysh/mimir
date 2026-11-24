# Operating and troubleshooting Mimir

After **every binary update**, run `mimir config check`. The source installer
does this automatically for an existing configuration. Every new CLI/MCP
connection and every judge batch also checks compatibility before contacting
the database or model. Replacing an executable does not replace a running
process: restart the existing judge and reconnect MCP clients after upgrading.
Do not start a second watcher alongside the first.

Configuration format `1` requires these settings, independent of the package
version. `mimir init` writes them automatically using the local state directory.

```toml
config_version = 1

[logging]
directory = "/absolute/path/to/mimir/logs"
```

For an existing configuration:

```sh
mimir config upgrade --log-directory "$HOME/.local/state/mimir/logs"
mimir config check
```

Both commands accept `--config PATH`; otherwise they use `MIMIR_CONFIG`, then
`$XDG_CONFIG_HOME/mimir/config.toml`, then `$HOME/.config/mimir/config.toml`.
Upgrade preserves credentials, unrelated settings and comments, uses a private
atomic replacement, and creates no backup. It rejects malformed configurations
and unsupported format versions without overwriting them. Do not manually
lower a newer format version to make an older binary accept it.

`config check` validates optional judge settings when present, without database
or model calls. Graph-only installations do not need `[judge]` or `[llm]`.
Missing or invalid required settings produce a field-specific error. A logging
directory must be writable when starting application work; the offline check
does not create directories. No database schema change is needed for these
operational settings.

## When a review fails

Run this on the computer named in the email:

```sh
mimir judge diagnose
```

It explains the cause, affected experience IDs, confirmed/pending counts,
configuration compatibility, log location, and the recorded watcher version
and current waiting state. It remains usable when configuration validation fails.
A snapshot is historical evidence, not proof that a process is currently alive.
With a custom configuration or state directory, pass `--config PATH` and/or
`--state-dir PATH` to select the same installation as the watcher.

The daily email shows the backlog, the watcher’s next action and a repair
command for each review that needs a decision. If the judge exits unexpectedly,
Mimir checks whether PostgreSQL already saved the review. If the revision is
still pending, the watcher gives other ready reviews their turn and starts
a fresh attempt from the stored source. New arrivals go behind that turn.

When a review needs an operator decision, Mimir queues an alert as soon as the
problem is detected. Its email has the experience UUID, source revision,
explanation, and a repair command. Daily statistics use their configured time.
The watcher owns alert delivery, so a stalled SMTP connection does not delay
other reviews.

```sh
mimir judge repair --experience EXPERIENCE_UUID --revision SOURCE_REVISION
```

The command opens the rejected review, explains the affected assessment,
and lets you remove it or choose an existing belief by its text. Review the
proposed edit and type `yes` to submit it. If removal leaves any extracted
statement unassessed, Mimir shows the affected sources before saving.
Add `--retry` to request a new judge attempt or `--review PATH` when a complete
corrected `review_experience` JSON object is already available. Use the UUID and source revision
from the alert and include the same configuration and state options when the
alert supplies them. Inspect the current source if the command reports a newer
revision. A successful repair reports `confirmed` after PostgreSQL readback.

If a fresh judge exits again without a recovery signal, the repair command
explains which backend stopped. Choose **edit settings** to select a working
backend, or restore the configured account and choose **verify**. The command
checks the source and runs the review. If the tool could not read the result,
repair verifies access before allowing another submission. Closing the dialog
leaves that revision pending. Other reviews can continue.

If PostgreSQL refuses the connection at startup or a work subscription drops,
the watcher retries every five seconds until it reconnects. For example, if
Mimir starts before PostgreSQL after a reboot, the delay avoids a tight loop
and lets work resume automatically. The watcher also detects a disconnect
while it is waiting for repair after a blocked batch. After subscribing,
it immediately checks for work queued during the outage. This timer runs
only while disconnected.
Mimir records one diagnostic per outage, even when many retries fail.

For failures that require a repair, correct the reported problem and edit the
configuration or send `kill -HUP WATCHER_PID` to start a fresh attempt. When
the model provider declares a usage limit with a usable reset time, the
watcher schedules one retry at that time. The report records the provider's
message as `provider_usage_limit`. An HTTP provider can also supply a
`Retry-After` header. Without a recovery signal, a repeated failure opens
the review-specific repair described above.
Configuration changes are observed through file events.

Common cases:

| Cause | Action |
| --- | --- |
| Missing/incompatible configuration | Run `mimir config check`; upgrade missing operational settings as above. |
| PostgreSQL unavailable | The running watcher retries automatically. Check database availability if the condition persists. |
| Source quotation rejected | The judge receives the field path and expected correction. If it repeats the same defect, open the repair command in the alert to supply the corrected review. |
| Historical deadline/request-budget failure | This can appear in retained reports from an older binary. The current judge imposes neither limit. Run `mimir config upgrade`, check configuration, restart the existing application, and inspect a fresh attempt. |
| Tool/database error | Run `mimir judge diagnose` for the cause and next action. Mimir reads the review back to determine what committed. |

Use these commands for the latest outcome and its recovery instructions.

```sh
mimir judge diagnose
mimir judge status
```

`status` retains its JSON interface for automation. Failure reports include
the reason and any relevant argument location. Emails contain a plain-English
summary and a concrete next action. Report persistent failures at
<https://github.com/kamysh/mimir/issues>, including the summary, version, time
and diagnostic ID. Never include credentials.

## Complete logs and diagnostics

CLI judge events and MCP tracing append complete entries to
`logging.directory/mimir.log` under a process-independent file lock. Mimir
does not truncate entries, rotate files or delete history automatically.
An unavailable log is reported without stopping review work.

The judge logs batch outcomes and actionable failures. It keeps transcripts
only for unresolved review attempts and saves them in PostgreSQL. Use the
command in the repair alert or run `mimir judge diagnostics --list` to find
the transcript. The transcript may contain private source text, so review it
before sharing. Successful attempts discard their transcripts. When PostgreSQL
cannot accept a transcript, the watcher reports it as pending and retains it
in memory until it can retry. Pending transcripts are lost if that process exits.

Status, last-failure and runtime reports replace their previous snapshots.
Diagnostics describe the failure in plain language. Add `--json` to retrieve
the raw transcript or a machine-readable list. Historical trace IDs from
the old local file still work.

Mimir does not change a supervisor's own journal or files to which a shell
redirects stdout/stderr. Any external retention policy remains an operator
decision. Configuration errors that prevent opening the log are also printed
to stderr for one-shot commands and recorded in judge state when available.

## Confirm recovery

Check the actual running process after restarting the existing watcher. Then
verify a new report has `confirmed > 0` and the previously affected experience
has a saved review for its current revision. A successful build, configuration
check, installed version string or attempted retry alone does not establish
that the judge works. Ordinary Mimir graph operations remain independent of
the optional judge and of any external agent harness.

### Review limit migration

The judge no longer imposes deadlines, request or retry quotas, transport-size
caps, or learning-content/count caps. `mimir config check` rejects retired
`[llm]` keys: `timeout_seconds`, `max_calls`, `max_output_tokens`, and
`max_budget_usd`. Run `mimir config upgrade` to remove them while preserving
other settings, then check again and restart the existing application. No
system service changes are required. Stop/cancel remains available through
normal process control and releases owned child processes.

Batch state can contain every selected and deferred revision. Provider and
platform limits remain external constraints;
see the runtime guide for Anthropic’s required native capacity lookup.

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
max_file_bytes = 1048576
retained_files = 4
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
and retry schedule. It remains usable when configuration validation fails.
A snapshot is historical evidence, not proof that a process is currently alive.
With a custom configuration or state directory, pass `--config PATH` and/or
`--state-dir PATH` to select the same installation as the watcher.

The daily email includes a cause, batch impact, next action and this diagnostic
command. A backlog is work still awaiting review; a scheduled retry does not
mean the failure has been repaired. After a successful non-idle batch, the
watcher immediately checks for the next eligible work. An empty queue waits for
a PostgreSQL work event and then scans the durable queue again. There is no idle
polling interval. After losing its listener, the watcher reconnects and scans
saved pending work, including changes whose notifications were missed. After
incomplete work or an unresolved prerequisite, it waits for a configuration
correction or explicit SIGHUP retry and prints `kill -HUP PID` for its current
process. Correct the cause before retrying. New work notifications cannot retry
an unchanged missing prerequisite. There is no failure-count threshold or
scheduled backoff. It announces failure/recovery transitions once per episode.

While running, the watcher observes configuration file changes through OS
events, including edits and atomic replacements. It applies a valid replacement
at the next batch boundary, subscribes using the new settings, then scans before
waiting. An invalid file produces a diagnostic and waits for a correction; the
file and last admitted settings are left intact. Save the corrected file to
resume, or press Ctrl-C to stop. No polling timer is used for configuration
changes.

Daily reports require the user's `judge.daily_report_time` configuration, with
an explicit `hour` and `minute` and no default. The watcher has a separate
calendar wake-up for that chosen local time, including when review work is idle
or awaiting correction. That wake-up queues mail and does not retry reviews.
Skipped local times use the first valid time afterward; repeated times produce
one admission at the first occurrence. A stalled delivery cannot cause repeated
admission of that day's report. Calendar and delivery tasks are cancelled and
joined when the watcher stops.

In watch mode, alert and daily-summary delivery run in one owned background
task. A stalled SMTP or authentication exchange does not hold the judge's state
lock or block another review. The report's `notification: "queued"` records
queue admission, not confirmed email delivery. Delivery problems are logged by
the worker. Stopping the watcher cancels and awaits the worker: existing notifier
outbox entries remain on disk, while jobs not yet submitted are cancelled.
Completed review reports remain stored. Standalone `judge run` delivery is still
synchronous; its remaining deadline is tracked in #110.

Common cases:

| Cause | Action |
| --- | --- |
| Missing/incompatible configuration | Run `mimir config check`; upgrade missing operational settings as above. |
| Source quotation rejected | The proposed quotation differs from the stored source, including literal JSON escapes. The judge receives the exact field path and correction explanation. Keep exact-quotation validation enabled. Persistent failure belongs in a bug report. |
| Historical deadline/request-budget failure | This can appear in retained reports from an older binary. The current judge imposes neither limit. Run `mimir config upgrade`, check configuration, restart the existing application, and inspect a fresh attempt. |
| Tool/database error | Inspect the private diagnostic trace. Mimir reads the review back to determine what actually committed; an opaque tool error is not proof that nothing changed. |

The diagnostic command prints an exact command for the relevant private trace:

```sh
mimir judge diagnostics --id ATTEMPT_UUID
mimir judge status
```

`status` retains its JSON interface for automation. `diagnostics` contains private
model/tool data; a citation failure also retains its rejected item and cited
source in the status report. Review and redact those files before sharing.
The plain-English diagnostic summary and emails exclude raw source excerpts,
model replies and arbitrary failure details. Report persistent failures at
<https://github.com/kamysh/mimir/issues>, including the summary, version, time
and diagnostic ID. Never include credentials.

## Log bounds and locations

CLI judge events and MCP tracing share `logging.directory/mimir.log`, with
fixed numbered rotation files. Writers use one process-independent file lock.
`retained_files` includes the current file: defaults retain at most **4 MiB**
across four files. Values are limited to 1–16 files and 4 KiB–16 MiB per file.
Oversized events are bounded; repeated errors cannot create new filenames or
increase this budget. Reducing limits prunes/truncates owned log files on the
next successful write. Unrelated files are never removed.

Private judge diagnostics remain in the existing state directory, selected by
`--state-dir` or the XDG state default. This preserves locks and restart history.
The trace store is separately limited to **3 MiB**, eight attempts and 48 events
per attempt; individual traces are capped at 256 KiB. Status, last-failure and
runtime snapshots replace bounded files rather than append indefinitely.
These are diagnostic retention files, not backups.

Application rotation does not control a supervisor's own journal or files to
which a shell redirects stdout/stderr. Use the supervisor's bounded journal or
an explicitly configured rotation policy; avoid indefinite append-only shell
redirection. Configuration errors that prevent opening the log are also printed
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

Diagnostic logs, excerpts and trace history retain their storage bounds. These
bounds do not truncate model input or stop a review. New trace fields
`model_requests` and `tool_attempts` count work performed; for legacy traces they
are absent. Batch state can contain every selected/deferred revision without a
fixed file-size ceiling. Provider/platform limits remain external constraints;
see the runtime guide for Anthropic’s required native capacity lookup.

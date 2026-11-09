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

## Closing an MCP session

The server watches client input while a request is running. Closing the
connection cancels the unfinished request and discards queued requests. An
owned local embedding worker is terminated and reaped before the server returns;
requests that remain connected still run in arrival order.

Disconnect does not undo changes already committed to the database. Read back
the affected work before retrying a write whose response was lost.

`mimir reembed` also watches its current belief while embedding. Deleting that
belief or its project stops the unfinished embedding call and reaps its local
worker. The command identifies the missing belief and asks for a user decision
before resuming; it does not recreate the belief. Other beliefs' workers keep
running, and the final vector write still checks its target in the same
transaction as the write.

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
saved pending work, including changes whose notifications were missed. The current
incomplete-work paths still use the configured interval and failure backoff;
their removal is tracked separately in #67. It announces
failure/recovery transitions instead of repeating the same error on every
polling cycle.

While running, the watcher observes configuration file changes through OS
events, including edits and atomic replacements. It applies a valid replacement
at the next batch boundary, subscribes using the new settings, then scans before
waiting. An invalid file produces a diagnostic and waits for a correction; the
file and last admitted settings are left intact. Save the corrected file to
resume, or press Ctrl-C to stop. No polling timer is used for configuration
changes.

In watch mode, alert and daily-summary delivery run in one owned background
task. A stalled SMTP or authentication exchange does not hold the judge's state
lock or block another review. The report's `notification: "queued"` records
queue admission, not confirmed email delivery. Delivery problems are logged by
the worker. Stopping the watcher cancels and awaits the worker: existing notifier
outbox entries remain on disk, while jobs not yet submitted are cancelled.
Completed review reports remain stored. Standalone `judge run` delivery is still
synchronous; its remaining delivery ownership work is tracked in #180.

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

## Log locations and preservation

CLI judge events and MCP tracing append complete entries to
`logging.directory/mimir.log` under one process-independent file lock. Mimir
applies no file-size limit, rotation or automatic deletion. Existing numbered
archives and unrelated files are left untouched. The current log grows as new
entries arrive.

`logging.max_file_bytes` and `logging.retained_files` are retired. Configuration
checking reports them and points to `mimir config upgrade`, which removes those
settings while preserving the directory, unrelated settings and comments. Run
the upgrade explicitly for the intended configuration, then check it again.

Private judge diagnostics remain in the existing state directory, selected by
`--state-dir` or the XDG state default. This preserves locks and restart history.
Traces retain all attempts, events and selected IDs. Status, last-failure and
runtime snapshots replace their previous files; private diagnostic records have
no application byte ceiling. New source diagnostics keep the complete rendered
input. Historical partial records retain their original omissions. These files
are diagnostics, not backups.

Mimir does not manage a supervisor's journal or shell redirections. Any external
retention policy is a separate user choice. Configuration errors that prevent opening the log are also printed
to stderr for one-shot commands and recorded in judge state when available.

## Confirm recovery

Check the actual running process after restarting the existing watcher. Then
verify a new report has `confirmed > 0` and the previously affected experience
has a saved review for its current revision. A successful build, configuration
check, installed version string or attempted retry alone does not establish
that the judge works. Ordinary Mimir graph operations remain independent of
the optional judge and of any external agent harness.

### Review limit migration

`mimir config check` names retired settings and points to `mimir config upgrade`.
Checking and upgrading use the same list:

| Section | Retired fields |
| --- | --- |
| `logging` | `max_file_bytes`, `retained_files` |
| `judge` | `batch_size` |
| `llm` | `timeout_seconds`, `max_calls`, `max_output_tokens`, `max_budget_usd` |
| `email` | `timeout_seconds`, `retry_seconds`, `max_attempts` |

Run `mimir config upgrade` against the chosen configuration, then check again.
The upgrade removes only those fields from their named sections and preserves
other settings and comments, including credentials, model choice and nested
email authentication. It chooses no replacement limit, changes no service,
creates no backup and makes no database or model request. Repeating it leaves
the upgraded file unchanged. Restart the existing application when applying
an upgrade to an installation. Stop/cancel remains available through normal
process control and releases owned child processes.

Diagnostic logs, excerpts and trace history retain complete content. Private
file and ownership checks remain in force. New trace fields
`model_requests` and `tool_attempts` count work performed; for legacy traces they
are absent. Batch state can contain every selected/deferred revision without a
fixed file-size ceiling. Provider/platform limits remain external constraints;
see the runtime guide for Anthropic’s required native capacity lookup.

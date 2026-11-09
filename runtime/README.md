# Mimir learning runtime

The experiential judge is part of the Rust `mimir` CLI. Configure it with
`[judge]` and `[llm]` in `~/.config/mimir/config.toml` (or pass `--config PATH`).
Keep that file and its directory private if it contains credentials. See
`config.example.toml` for the supported settings.

## Updates and failures

Run `mimir config check` after each binary update. Existing configurations need
`config_version = 1` and `[logging].directory`; use
`mimir config upgrade --log-directory "$HOME/.local/state/mimir/logs"` to add
these while preserving other settings. Restart the existing watcher after
updating its binary. An old running process continues to use its old code.

When an email reports a failure, run `mimir judge diagnose` on that computer.
See [operations and troubleshooting](../docs/operations.md) for exact recovery
steps, append-only operational logs and private diagnostic handling.

## Configure a scheduled judge

The supported job runs `mimir judge run` from the installed CLI. The model
subprocess is managed by that runtime; do not make a separate Claude prompt,
MCP allowlist or direct belief-insertion script part of this job.
Configuring skills and startup reminders does not configure the judge.

For an agreed Claude Code setup, merge these sections into the existing private
Mimir config. Preserve its database, embedding, notification and other settings.
Choose a model actually available to the authenticated Claude account:

```toml
[judge]
mcp_command = "/ABSOLUTE/HOME/.local/bin/mimir-mcp"
mcp_args = []

[llm]
backend = "claude-code"
model = "YOUR_MODEL"
```

For an agreed Codex setup, keep `[judge]` above and use this `[llm]` section
instead. Use the model and effort selected for the authenticated Codex account;
do not substitute models merely because another one is newer:

```toml
[llm]
backend = "codex"
model = "YOUR_CODEX_MODEL"
reasoning_effort = "medium" # use the selected effort, or omit for the CLI default
```

Check Codex authentication with `codex login status`; use `codex login` when
needed. The job's `PATH` must resolve the intended `codex` executable. A
successful harmless `codex exec` request verifies model access without creating
an experience or review. OpenAI/Codex authentication does not authenticate GitHub
or Claude Code.

Set the config directory to `0700` and the config file to `0600`.
Check the selected client's authentication and network access before scheduling.
For Claude Code, `claude auth status` reports account status; `claude auth login`
renews an expired login. A successful `mimir stats` or MCP registration does not
verify the model account. Never copy credentials into the plist or disable TLS
verification to get a test to pass.

If Claude reports `UNABLE_TO_GET_ISSUER_CERT_LOCALLY`, configure its trusted CA
bundle with `NODE_EXTRA_CA_CERTS` in the job environment. Use a verified existing
bundle appropriate to this machine (for example `/etc/ssl/cert.pem` when that
bundle contains the required trust roots). Test a harmless Claude request with
that same environment, model and authentication before claiming model access.
See [Claude network configuration](https://code.claude.com/docs/en/network-config).
Do not silently substitute a different backend or model on an access failure.

### macOS launchd

Inspect any existing job with this label before replacing it. When replacement
is authorized, unload its registration and remove the superseded job definition
and task-specific launcher/prompt; do not leave two scheduled writers active.
Preserve unrelated jobs, application data and credentials. Create
`~/Library/LaunchAgents/org.mimir.judge.plist` using literal absolute paths:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0"><dict>
  <key>Label</key><string>org.mimir.judge</string>
  <key>ProgramArguments</key><array>
    <string>/ABSOLUTE/HOME/.local/bin/mimir</string>
    <string>judge</string><string>run</string>
    <string>--config</string><string>/ABSOLUTE/HOME/.config/mimir/config.toml</string>
  </array>
  <key>WorkingDirectory</key><string>/ABSOLUTE/HOME</string>
  <key>EnvironmentVariables</key><dict>
    <key>HOME</key><string>/ABSOLUTE/HOME</string>
    <key>PATH</key><string>/ABSOLUTE/HOME/.local/bin:/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin</string>
  </dict>
  <key>StartCalendarInterval</key><dict>
    <key>Weekday</key><integer>0</integer>
    <key>Hour</key><integer>5</integer>
    <key>Minute</key><integer>0</integer>
  </dict>
  <key>RunAtLoad</key><false/>
  <key>StandardOutPath</key><string>/ABSOLUTE/HOME/.local/state/mimir/judge.log</string>
  <key>StandardErrorPath</key><string>/ABSOLUTE/HOME/.local/state/mimir/judge.log</string>
</dict></plist>
```

Adjust the schedule to the agreed time (this example is Sunday 05:00).
Include the actual directory from `command -v claude` or `command -v codex`,
as appropriate, in `PATH`; Nix/Home Manager
commonly uses `/etc/profiles/per-user/YOUR_USER/bin`. Add `NODE_EXTRA_CA_CERTS`
only when the verified network setup requires it. launchd does not inherit shell
exports. No credential value belongs in the plist.

Create the private state directory, validate and load the job:

```sh
mkdir -p "$HOME/.local/state/mimir" "$HOME/Library/LaunchAgents"
chmod 700 "$HOME/.local/state/mimir" "$HOME/.config/mimir"
chmod 600 "$HOME/.config/mimir/config.toml" "$HOME/Library/LaunchAgents/org.mimir.judge.plist"
plutil -lint "$HOME/Library/LaunchAgents/org.mimir.judge.plist"
mimir judge check-config --config "$HOME/.config/mimir/config.toml"
launchctl bootstrap "gui/$(id -u)" "$HOME/Library/LaunchAgents/org.mimir.judge.plist"
launchctl print "gui/$(id -u)/org.mimir.judge"
```

For a previously loaded job, `launchctl bootout "gui/$(id -u)/org.mimir.judge"`
must precede bootstrap. A calendar job normally has no PID between runs.

### Verify the actual scheduled job

A registered job or valid config is not a completed model review. When a live
review run covering all currently eligible work is authorized, start the actual
service and inspect its report:

```sh
launchctl kickstart "gui/$(id -u)/org.mimir.judge"
launchctl print "gui/$(id -u)/org.mimir.judge"
tail -n 30 "$HOME/.local/state/mimir/judge.log"
mimir judge status
```

Check the final exit status and the report. An empty pending queue should finish
without a model call: it verifies scheduling, config, MCP and database access,
but does not verify provider authentication or model/review behavior. For a
nonempty batch, verify committed database review receipts. Do not manufacture
an experience merely to make an installation test write to memory. Use
`mimir judge diagnostics` for a failed batch, and report authentication, network,
model and review failures separately. Keep the installation incomplete
when a required account or permission step remains unresolved.

## Runtime behavior

When enabling email, obtain the desired local delivery time from the user and set
`judge.daily_report_time = { hour = H, minute = M }` in the configuration. Hours
run from 0 through 23 and minutes from 0 through 59. Both fields are required;
there is no default and no request-level override. A missing or invalid time
produces a configuration diagnostic with the correction to make.

An owned calendar task admits the report at that time even when reviews are idle
or paused for correction. It does not start a review batch. A skipped clock time
uses the first valid time afterward; a repeated time uses its first occurrence,
once. Missed days are included by the existing reporting cursor. Queue admission
is remembered while delivery is pending, so status updates cannot repeatedly
enqueue the same day's report. Disabling email through an admitted configuration
stops future calendar admissions. Restart cancels and joins the calendar owner.

Watch mode owns a background task for alert and daily-summary delivery. A stalled
SMTP or authentication exchange does not block another review. `notification:
"queued"` means accepted for an attempt, not delivered. Shutdown cancels and
awaits that task; queued jobs not yet submitted are cancelled, and saved notifier
outbox entries remain. Standalone `judge run` delivery remains synchronous.

`mimir judge check-config` validates settings locally. `mimir judge run` reviews
one selected batch through `mimir-mcp`; `mimir judge watch` immediately checks
for further eligible work after each successful non-idle batch. An empty queue
waits for PostgreSQL work events and scans again when one arrives; it has no idle
polling interval. After a listener disconnects, it subscribes again and scans
saved work before waiting, so missed notifications do not lose pending reviews.
If restoring the connection fails, it waits for a configuration correction or
an explicit SIGHUP retry. OS file events detect configuration edits and replacements without
polling. Valid changes are subscribed before the next queue scan. Invalid
settings pause for a correction event, leave the file intact, and do not replace
the admitted settings. After incomplete work or an unresolved prerequisite, the
watcher explains the problem and prints `kill -HUP PID` with its current process
ID. Correct the cause before requesting that retry. New work notifications do
not retry an unchanged missing prerequisite. The retry revalidates configuration
and acknowledges its database subscription before scanning pending work.
There is no failure-count threshold or retry timer. The former
`--interval-seconds` and `--max-consecutive-failures` arguments are removed.
An empty queue
makes no model call. `mimir judge status` reads the last local report and gives
the ID of a retained failure trace. `mimir judge diagnostics` reads the first
failure trace of the current incident; `--list` shows retained attempt IDs and
`--id UUID` selects a specific attempt. The private trace records ordered model
requests, tool requests and outcomes, cumulative model-request and tool-attempt counts, and the final
failure reason. It retains every attempt, selected ID and event with complete
details. Later successful runs do not erase an earlier
failure trace. The database review receipt is authoritative; a local status
snapshot or model claim does not establish completion. The runner restricts
tool calls to the selected experience and project.
After a committed review, it checks the pinned database revision and finishes
that item without requiring a separate model "done" turn. A failed or interrupted run leaves the revision pending for the next run and reports a
`block_reason` without exposing provider or experience text.

The `claude-code`, `codex`, and `command` LLM backends are implemented. Claude
Code and Codex use explicit CLI flags for structured output and isolation, and
reject installed versions whose help lacks required flags. Each model turn is
one subprocess owned by the judge. Mimir imposes no review deadline, model/tool
request quota, correction-retry ceiling, or subprocess input/output size ceiling.
Ctrl-C or SIGTERM stops active `run` and `watch` work, including model/tool waits; it cleans up
its owned model and MCP children. Provider-native limits still apply.
Select the model with `[llm].model`; for Codex, optional
`[llm].reasoning_effort` passes an explicit effort to each invocation. Omitting
it leaves Codex's normal default in effect. Model-specific effort support is
checked by Codex at runtime.

Codex runs with `--json` and reads its structured answer from
`--output-last-message`; Claude Code uses `--output-format json` and reads the
structured reply from that wrapper. Codex's human-readable mode echoes the prompt
to stderr, so it is unsuitable for the judge's potentially large history payloads.
Subprocess stdin, stdout and structured answer files are read completely. Stderr
is continuously drained and retained completely for diagnostics. MCP frames and notification sequences
have no Mimir-imposed byte/count ceiling. Model call arrays are executed in order,
with one result per call. Successful process output alone never acknowledges a
review; the database-receipt rule remains in force.

After updating, run `mimir config check`. Retired `[llm]` settings
`timeout_seconds`, `max_calls`, `max_output_tokens`, and `max_budget_usd` are
rejected with migration instructions. `mimir config upgrade` removes those four
settings along with retired judge, email and logging limits listed in
[operations](../docs/operations.md#review-limit-migration), preserves other
settings and comments, and creates no backup.
Run `mimir config check` again, then restart your existing application process.
No service definitions need changing. The judge selects all currently eligible
work in its project scope. `judge.batch_size` is retired: run
`mimir config upgrade`, then `mimir config check`, for a configuration that still
contains it. A separately configured embedding batch setting is preserved.
An explicit pending-query result count must be positive; omission returns all
matches. See [judge selection](../docs/JUDGE-SELECTION.md).

Review and experience content, source records, extracted items, predictions,
assessment references, candidate declarations and text fields have no application
size/count ceilings. Required fields, exact quotations, numeric domains,
provenance, unique identities, transactions and revision checks remain enforced.
Native integer/storage limits can still produce explicit errors. Complete batch
state and private diagnostic history are retained. Operational logs append complete
entries without application rotation or automatic deletion.
Legacy diagnostic files load, but their remaining-budget values are not presented
as cumulative work counts: new count fields are absent for old records.

The `api` backend requires an explicit model, provider, and API key. OpenAI
Responses calls use stateless `store: false`
requests and replay response output, including encrypted reasoning items, with
function results. Anthropic calls replay signed thinking/content blocks unchanged
and pair each `tool_result` with its `tool_use` ID. Multiple calls in one provider
response are executed one at a time through the same scoped host gate. Provider
redirects, incomplete responses and provider errors block the run. Malformed tool
arguments return correction feedback. Transport bodies are read completely. `watch` runs locally and waits for database work events when idle; no service or timer is installed
by the source change. The Step 11 Codex comparison exercised live judge calls,
but the new watch mode and API-provider accounts have not been exercised live.

The other API providers use non-streaming Chat Completions and function tools.
The host replays complete assistant messages before all tool results, retaining
DeepSeek `reasoning_content` and Gemini tool-call thought signatures. A provider
or model that rejects those requests fails the review; Mimir does not substitute
another model. OpenAI Responses and Chat Completions omit optional output-token
limits. Anthropic Messages requires `max_tokens`: Mimir obtains the configured
model’s actual capacity from `GET /v1/models/{model_id}` and caches it for that
adapter. Missing or invalid capacity metadata is an explicit provider error.
Choose a model that supports function tools.

| `llm.provider` | Default API base | Protocol and local verification | Live account |
| --- | --- | --- | --- |
| `openai` | `https://api.openai.com/v1` | Responses fixture | Not checked |
| `anthropic` | `https://api.anthropic.com/v1` | Messages fixture | Not checked |
| `openrouter` | `https://openrouter.ai/api/v1` | Chat fixture; explicit model, `allow_fallbacks=false`, `require_parameters=true` | Not checked |
| `deepseek` | `https://api.deepseek.com` | Chat fixture; replay `reasoning_content` | Not checked |
| `zai` | `https://api.z.ai/api/paas/v4` | Chat fixture; accepts documented object-form function arguments | Not checked |
| `gemini` | `https://generativelanguage.googleapis.com/v1beta/openai` | Chat fixture; replay thought signatures | Not checked |
| `openai-compatible` | Required `llm.base_url` | Generic Chat fixture; actual endpoint/model support varies | Not checked |

OpenRouter disables fallback after choosing an upstream provider, but without
an upstream pin it may choose a different compatible provider on another turn.
Mimir sends no `models` fallback list or retry to a different model. A
provider's own internal retries are outside Mimir's control. The transport
assumes standard Chat Completions function tools and fails closed on missing,
malformed, or partial tool responses. API bases may be overridden with
`llm.base_url`; only the explicit compatible endpoint requires it.

Protocol references: [OpenRouter routing](https://openrouter.ai/docs/guides/routing/provider-selection),
[DeepSeek chat and thinking](https://api-docs.deepseek.com/guides/thinking_mode/),
[Z.ai chat](https://docs.z.ai/api-reference/llm/chat-completion), and
[Gemini OpenAI compatibility](https://ai.google.dev/gemini-api/docs/openai).

Notifications live in the reusable Rust `mimir-notifications` crate. A component
submits a source, incident key, and failure code with a short safe summary, or
a recovery event. It may also provide bounded, validated email details that
are stored with the pending alert for retries. The judge supplies the project,
failure reason, selected experience IDs, result counts, and diagnostic ID. On
recovery it reports the earlier failure and distinguishes affected reviews
confirmed by a later completed batch from reviews whose completion is
unverified. An idle queue closes the alert episode but does not prove that a
specific review completed. Email excludes belief contents, model output, tool
arguments and responses, and credentials. Each incident has independent
failure suppression, recovery, and pending-delivery state. The crate owns
`notification.lock` and a private atomic `notification-outbox.json` in the Mimir
state directory; other components can use the same crate and directory without
depending on the judge. `Notifier::retry_due()` retries all saved alerts independently of a new review,
without a result quota, delay, or attempt ceiling. It does not schedule itself.
The watcher owns delivery. Standalone review commands save pending events and
print the exact `mimir judge watch` command; they never wait for mail. The
private incoming-event queue is separate from the sender lock, so stalled SMTP
or OAuth cannot stop a review from saving its result and notification.

With `[email].enabled=true`, password, OAuth2, or unauthenticated SMTP uses the
configured relay with required STARTTLS or implicit TLS and certificate
verification. OAuth2 refresh uses Google's or Microsoft's fixed HTTPS token
endpoint and `lettre`'s XOAUTH2-only SMTP authentication. The private
`notification-oauth.json` file caches access and rotated refresh tokens under
the same notification lock. A changed account, client, tenant, scope, client
secret, SMTP host, or bootstrap refresh token is refused rather than silently
reusing the previous cache. Notification status is separate from the judge's
database-confirmed learning status: `disabled`, `not_needed`, `sent`,
`retry_pending`, `auth_required`, or `unavailable` for a local
state failure. A failed email cannot undo a committed review.

OAuth setup is a separate account action: register a client, grant the SMTP
scope with offline access, and put the resulting refresh token in the private
config file. Mimir does not open a browser or obtain initial consent. The
examples below replace the password settings in `config.example.toml`; use
one provider at a time and select the SMTP host for your account.

Google Gmail example:

```toml
[email]
enabled = true
host = "smtp.gmail.com"
port = 587
tls = "starttls"
from = "you@gmail.com"
to = ["you@gmail.com"]
username = "you@gmail.com"
auth = "oauth2"

[email.oauth]
provider = "google"
client_id = "YOUR_CLIENT_ID"
client_secret = "YOUR_CLIENT_SECRET" # omit only if your client has none
refresh_token = "YOUR_INITIAL_REFRESH_TOKEN"
scope = "https://mail.google.com/"
```

Microsoft 365 example:

```toml
[email]
enabled = true
host = "smtp.office365.com"
port = 587
tls = "starttls"
from = "you@example.com"
to = ["you@example.com"]
username = "you@example.com"
auth = "oauth2"

[email.oauth]
provider = "microsoft"
client_id = "YOUR_CLIENT_ID"
client_secret = "YOUR_CLIENT_SECRET" # omit only if your client has none
refresh_token = "YOUR_INITIAL_REFRESH_TOKEN"
tenant = "common" # or the registered tenant ID
scope = "https://outlook.office.com/SMTP.Send offline_access"
```

Keep `~/.config/mimir` at mode 0700 and `config.toml` at mode 0600. The state
directory and its token file must also remain private. The judge uses
`--state-dir`, then `$XDG_STATE_HOME/mimir`, then `~/.local/state/mimir`.
After a refresh-token
rotation, the state file contains the current token while the config still
contains the initial token; do not delete that state file expecting the initial
token to remain valid. If account settings or consent change, obtain a new
refresh token through the provider's authorization flow and deliberately reset
the old OAuth cache after preserving any token you may still need. Token
refresh is not an atomic transaction with the provider: if the provider rotates
its token and the local state write fails, Mimir blocks SMTP, but recovery may
require a new authorization if the provider invalidated the previous token.
Token revocation, expired consent, malformed responses, and changed account
identity surface as `auth_required`. Network/server failures remain retryable. A rejected
cached access token is cleared without losing the refresh token, then refreshed
and tried once more. No live Google or Microsoft account has been verified.

Provider references: [Google SMTP XOAUTH2](https://developers.google.com/workspace/gmail/imap/xoauth2-protocol),
[Google offline refresh](https://developers.google.com/identity/protocols/oauth2/web-server),
[Microsoft SMTP OAuth](https://learn.microsoft.com/en-us/exchange/client-developer/legacy-protocols/how-to-authenticate-an-imap-pop-smtp-application-by-using-oauth/),
and [Microsoft refresh-token rotation](https://learn.microsoft.com/en-us/entra/identity-platform/v2-oauth2-auth-code-flow).

Pending delivery is persisted before SMTP, reusing the same Message-ID across
retries. There is no SMTP/OAuth deadline, retry delay, attempt ceiling, or
notification batch quota. Remove obsolete `email.timeout_seconds`,
`email.retry_seconds` and `email.max_attempts` from configuration and run
`mimir judge check-config`; they are refused rather than ignored. Historical
saved deadlines and exhaustion flags do not block a retry. OAuth tokens remain
usable until the provider's reported expiry, without an invented early cutoff.

The watcher retries saved work on startup, incoming events and SIGHUP. After
correcting an unresolved prerequisite, send `kill -HUP <watcher-pid>` or restart
`mimir judge watch` with the same configuration and state directory. Delivery
errors leave mail pending and print recovery instructions. A sender's own queue
acknowledgements do not cause a retry loop. Stopping the watcher cancels and
joins delivery; no detached sender remains. Configuration, accounts and services
are never changed by this retry mechanism.

SMTP acceptance means the relay accepted the message, not that it reached an
inbox. A crash after relay acceptance and before the final outbox write may
cause a duplicate. This uncertainty is not treated as confirmed delivery.
The Tokio SMTP transport reports success after the server accepts DATA; a subsequent QUIT
failure does not turn that accepted message into a failed send. All SMTP tests
use loopback fixtures and generated test certificates; no external mail was
sent.

The custom `command` backend runs the absolute executable from `llm.command`
with the literal `llm.args`. It receives one JSON object on stdin containing
`instructions`, the pinned `experience`, the allowed `tools` with their schemas,
prior `history`, `response_schema`, and `protocol`. It writes one JSON object to
stdout matching this response shape:

```json
{"calls":[{"name":"get_experience","arguments_json":"{\"id\":\"00000000-0000-0000-0000-000000000001\"}"}]}
```

`calls` contains at most one request. `arguments_json` must be a JSON object
encoded as a string. `{"calls":[]}` ends the turn. The host executes and checks
requested tools, then includes the result in the next invocation's `history`.
The executable must not call Mimir tools itself. The runner blocks malformed,
oversized, failed, or timed-out replies and kills the subprocess group.
Per-turn private temporary files are created under `/var/tmp/mimir` and removed
afterward.

`tests/judge-adapters.sh` verifies the three adapters with local fake executables
and an isolated database, including malformed output and descendant cleanup.
Rust API tests use local HTTP fixtures and an isolated application-role database
to check continuation and review receipts. Neither suite invokes live model
accounts. The experimental evaluator under
`tests/eval/` is a separate Rust/Bash tool, not the learning runtime.

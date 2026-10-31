# Mimir learning runtime

The experiential judge is part of the Rust `mimir` CLI. Configure it with
`[judge]` and `[llm]` in `~/.config/mimir/config.toml` (or pass `--config PATH`).
Keep that file and its directory private if it contains credentials. See
`config.example.toml` for the supported settings.

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
batch_size = 5
mcp_command = "/ABSOLUTE/HOME/.local/bin/mimir-mcp"
mcp_args = []

[llm]
backend = "claude-code"
model = "YOUR_MODEL"
timeout_seconds = 300
max_calls = 20
```

For an agreed Codex setup, keep `[judge]` above and use this `[llm]` section
instead. Use the model and effort selected for the authenticated Codex account;
do not substitute models merely because another one is newer:

```toml
[llm]
backend = "codex"
model = "YOUR_CODEX_MODEL"
reasoning_effort = "medium" # use the selected effort, or omit for the CLI default
timeout_seconds = 300
max_calls = 20
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
bounded batch is authorized, start the actual service and inspect its report:

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
model, timeout and review failures separately. Keep the installation incomplete
when a required account or permission step remains unresolved.

## Runtime behavior

`mimir judge check-config` validates settings locally. `mimir judge run` reviews
one bounded batch through `mimir-mcp`; `mimir judge watch` repeats bounded runs
every five minutes by default (`--interval-seconds`, minimum 60) until interrupted.
After three consecutive incomplete or unavailable runs by default
(`--max-consecutive-failures`), it backs off to hourly runs. An empty queue
makes no model call. `mimir judge status` reads the last local report and gives
the ID of a retained failure trace. `mimir judge diagnostics` reads the first
failure trace of the current incident; `--list` shows retained attempt IDs and
`--id UUID` selects a specific attempt. The private trace records ordered model
requests, tool requests and outcomes, remaining call budgets, and the final
failure reason. It retains at
most eight attempts, 48 events and 256 KiB per attempt, and truncates event
details to 3,072 characters. Later successful runs do not erase an earlier
failure trace. The database review receipt is authoritative; a local status
snapshot or model claim does not establish completion. The runner restricts
tool calls to the selected experience and project.
After a committed review, it checks the pinned database revision and finishes
that item without requiring a separate model "done" turn. A failed or
budget-limited run leaves the revision pending for the next run and reports a
bounded `block_reason` without exposing provider or experience text.

The `claude-code`, `codex`, and `command` LLM backends are implemented. Claude
Code and Codex use explicit CLI flags for structured output and isolation, and
reject installed versions whose help lacks required flags. Each model turn is
one bounded subprocess. The Claude Code `max_budget_usd` setting is per
invocation; `max_calls` and the runner deadline bound the whole review run.
Select the model with `[llm].model`; for Codex, optional
`[llm].reasoning_effort` passes an explicit effort to each invocation. Omitting
it leaves Codex's normal default in effect. Model-specific effort support is
checked by Codex at runtime.

Codex runs with `--json` and reads its structured answer from
`--output-last-message`; Claude Code uses `--output-format json` and reads the
structured reply from that wrapper. Codex's human-readable mode echoes the prompt
to stderr, so it is unsuitable for the judge's potentially large history payloads.
All subprocess adapters retain the same per-invocation limits: 2 MiB input,
8 MiB stdout and 64 KiB stderr. Crossing an output limit still fails the attempt
and terminates its process group. The error names stdout or stderr, its limit,
and the observed byte count (a lower bound because reading stops at overflow).
The local failure report retains at most 32 KiB of that stream's prefix as a
private `failure_source`; ordinary error text and email omit the excerpt.
This is an I/O contract enforced by runtime tests, outside the abstract Agda
diagnostic-retention proofs. Successful process output alone never acknowledges
a review; the existing database-receipt rule remains in force.

The `api` backend requires an explicit model, provider, and API key. OpenAI
Responses calls use stateless `store: false`
requests and replay response output, including encrypted reasoning items, with
function results. Anthropic calls replay signed thinking/content blocks unchanged
and pair each `tool_result` with its `tool_use` ID. Multiple calls in one provider
response are executed one at a time through the same scoped host gate. Provider
redirects, incomplete responses, malformed calls, and response limits block the
run. `watch` supplies recurring local polling; no service or timer is installed
by the source change. The Step 11 Codex comparison exercised live judge calls,
but the new watch mode and API-provider accounts have not been exercised live.

The other API providers use non-streaming Chat Completions and function tools.
The host replays complete assistant messages before all tool results, retaining
DeepSeek `reasoning_content` and Gemini tool-call thought signatures. A provider
or model that rejects those requests fails the review; Mimir does not substitute
another model. `max_output_tokens` maps to Chat Completions `max_tokens` and
reported completion usage is checked against it. Choose a model that supports
function tools and the configured output limit.

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
failure suppression, recovery, retry, and exhaustion state. The crate owns
`notification.lock` and a private atomic `notification-outbox.json` in the Mimir
state directory; other components can use the same crate and directory without
depending on the judge. `Notifier::retry_due` lets a future caller retry due
alerts independently of a new judge run. It does not schedule itself.

With `[email].enabled=true`, password, OAuth2, or unauthenticated SMTP uses the
configured relay with required STARTTLS or implicit TLS and certificate
verification. OAuth2 refresh uses Google's or Microsoft's fixed HTTPS token
endpoint and `lettre`'s XOAUTH2-only SMTP authentication. The private
`notification-oauth.json` file caches access and rotated refresh tokens under
the same notification lock. A changed account, client, tenant, scope, client
secret, SMTP host, or bootstrap refresh token is refused rather than silently
reusing the previous cache. Notification status is separate from the judge's
database-confirmed learning status: `disabled`, `not_needed`, `sent`,
`retry_pending`, `auth_required`, `exhausted`, or `unavailable` for a local
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
identity surface as `auth_required` while attempts remain; the final failed attempt is
reported as `exhausted`. Network/server failures remain retryable. A rejected
cached access token is cleared without losing the refresh token, then refreshed
and tried once more. No live Google or Microsoft account has been verified.

Provider references: [Google SMTP XOAUTH2](https://developers.google.com/workspace/gmail/imap/xoauth2-protocol),
[Google offline refresh](https://developers.google.com/identity/protocols/oauth2/web-server),
[Microsoft SMTP OAuth](https://learn.microsoft.com/en-us/exchange/client-developer/legacy-protocols/how-to-authenticate-an-imap-pop-smtp-application-by-using-oauth/),
and [Microsoft refresh-token rotation](https://learn.microsoft.com/en-us/entra/identity-platform/v2-oauth2-auth-code-flow).

Each attempt is persisted before SMTP; a later invocation retries when due,
up to `max_attempts`, reusing the same Message-ID. SMTP acceptance means the
relay accepted the message, not that it reached an inbox. A crash after relay
acceptance and before the final outbox write may cause a duplicate; a crash
before sending can consume an attempt and eventually exhaust the retry budget.
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

# AGENTS.md — install instructions for AI coding agents

This file is the installation procedure for AI coding agents configuring Mimir
for Codex or Claude Code. [README.md](README.md#installation) is the human guide;
[Agent setup](docs/claude-code-setup/INSTALL.md) is the shared client-integration
procedure. Both use purpose-focused guidance and advisory lifecycle reminders.

## Read this first

- All steps are idempotent. Safe to rerun. If interrupted, restart
  from **State detection** below, not from Step 1.
- After every step, run the verify command. Do not stack failures —
  fix the current step before moving on.
- Destructive operations (dropping a database, removing a container,
  overwriting a file you did not author) require user confirmation.
  Stop and ask, even when a step appears to call for it.
- Do **not** run bare `mimir init` — with no arguments it opens
  `$EDITOR` and will block your shell indefinitely. Use the
  non-interactive `mimir init KEY=VALUE ...` form instead (Step 4).

## Upgrading from 1.x to 2.0

MCP `insert_belief` now rejects calls without an independent
`provenance: {"basis":"user_instruction"|"document","reference":"..."}`.
Update the installed skill and custom callers as part of the upgrade.
Incident-derived conclusions must use `record_experience` and review-owned
candidates; do not count the same report through both paths. Direct CLI
insertion is unchanged.

Back up the database and affected configuration before starting the new
binaries: startup applies the additive learning-ledger and review-candidate
migrations. Coordinate both binaries and client guidance. Validate any configured
scheduled judge against the current
[runtime setup](runtime/README.md#configure-a-scheduled-judge), including its
model account, service environment and actual run report. Old database/embedding
settings
remain usable, and the Rust judge stays opt-in. A binary rollback does not
retract reviews that have already changed the graph.

## What a complete install consists of

The application needs PostgreSQL, the `mimir` / `mimir-mcp` binaries and an MCP
registration in the chosen client. The standard agent setup also installs the
shared skill, global guidance and one purpose-focused SessionStart reminder.
They explain how prior reasoning can prevent repeated investigation and mistakes.
They do not require automatic queries, fixed call/write quotas, hook-generated
ratings, a Stop critic or consolidation gates. Omitting a reminder does not
disable the tools; report the intentional omission instead of claiming its
delivery was verified.

The client launches the MCP server. Schema migrations run through normal Mimir
startup. Optional scheduled maintenance judges are separate from agent setup.

## Variables

Resolve these values from the existing installation and user agreement; ask only
for missing consequential choices. Also select `AGENT_CLIENT=codex` or
`AGENT_CLIENT=claude` (repeat the client steps if both are requested):

1. **Docker container name** — the local name for the postgres-ai container
   (e.g. `local-postgres-ai`). Check `docker ps -a` and suggest a name that
   doesn't collide. The Docker image is always `kamysh/postgres-ai`.
2. **Docker volume name** — the named volume for postgres data
   (e.g. `local-postgres-ai-data`). If sharing a container with muninn, confirm
   the existing volume name rather than inventing one.
3. **Port** — the host port to expose PostgreSQL on (default `5432`; check
   `lsof -nP -iTCP -sTCP:LISTEN` for conflicts).
4. **DB user** — the PostgreSQL role to create for mimir (default `mimir`).
5. **DB name** — the database to create (default `mimir`; usually matches the user).

If mimir is being installed alongside muninn (see "Companion tool" at the end),
also confirm whether they share one container or use separate ones.

Bind the answers as shell variables once, then re-use in every command below:

| Variable | Notes |
|---|---|
| `PORT` | Host port. Avoid 5000 (AirPlay on macOS), 6000 (X11), and anything in use. |
| `CONTAINER` | Existing postgres-ai container to reuse, or an unused name for a new container. Image: `kamysh/postgres-ai`. |
| `VOLUME` | Docker volume for the postgres data dir (e.g. `mimir_data`). If sharing a container with muninn, use the same volume. |
| `DB_USER` | PostgreSQL role for mimir. |
| `DB_NAME` | Database for mimir. |
| `EMBEDDING_BACKEND` | `local` (no API key, downloads ~120 MB) \| `voyage` \| `openai`. Required only for `load_document` / `query_document`; omit the `[embeddings]` section entirely if you only need the belief graph. |

## Preflight (must all pass)

```sh
docker info >/dev/null                                                 # daemon running
echo "$PATH" | tr ':' '\n' | grep -qx "$HOME/.local/bin"               # PATH includes target
command -v "$AGENT_CLIENT" >/dev/null                                  # chosen client installed
```

If any check fails, stop and report the specific failure to the user.
Do not try to recover automatically.

## State detection — skip steps already complete

Run these probes before doing any work. For each that returns 0, skip
the corresponding step. For a shared or existing installation, confirm the
container's image, published port and volume match the agreed values. An occupied
port is expected when reusing that running container.

```sh
# Step 1 — postgres container running
docker ps --filter "name=^${CONTAINER}$" --filter "status=running" \
  --format '{{.Names}}' | grep -qx "$CONTAINER"

# Step 2 — DB and role exist, and the agreed role can connect
docker exec "$CONTAINER" psql -U "$DB_USER" -d "$DB_NAME" -c 'SELECT 1' >/dev/null

# Step 3 — binaries installed
command -v mimir && command -v mimir-mcp >/dev/null

# Step 4 — config exists and CLI can talk to the DB (can apply pending migrations)
[ -f "${MIMIR_CONFIG:-$HOME/.config/mimir/config.toml}" ] && mimir stats

# Step 5 — selected client's MCP registration (inspect path/scope too)
"$AGENT_CLIENT" mcp get mimir

# Step 6 — static reminder probe only; full verification is below.
# Inspect the chosen client's skill/global guidance at the paths in Agent setup.
if [ "$AGENT_CLIENT" = codex ]; then
  MIMIR_CLIENT_SETTINGS="${CODEX_HOME:-$HOME/.codex}/hooks.json"
else
  MIMIR_CLIENT_SETTINGS="$HOME/.claude/settings.json"
fi
jq -e 'any(.hooks.SessionStart[]?.hooks[]?;
  .command | test("(mimir|muninn)-reminder[.]md"))' "$MIMIR_CLIENT_SETTINGS"
# A combined reminder may use Muninn's file path. Inspect its actual text.
# Inline/custom hooks need equivalent inspection; do not install a duplicate.
```

## Step 1 — Start postgres

Skip this step when reusing the verified running container. For a **new**
container, both checks below must pass before creation. If the selected name
belongs to a stopped container or the port belongs to another service, stop and
resolve that existing state with the user; do not create a replacement blindly.

```sh
! lsof -nP -iTCP:"$PORT" -sTCP:LISTEN | grep -q .
! docker ps -a --format '{{.Names}}' | grep -qx "$CONTAINER"
```

```sh
docker run -d \
  --name "$CONTAINER" \
  --restart always \
  -p "127.0.0.1:${PORT}:5432" \
  -v "${VOLUME}:/var/lib/postgresql/data" \
  kamysh/postgres-ai:latest
sleep 3
```

**Verify:**
```sh
docker exec "$CONTAINER" psql -U postgres -c 'SELECT 1' >/dev/null && echo OK
```

The `kamysh/postgres-ai` image includes pgvector, Apache AGE, uuid-ossp,
and pgcrypto. Mimir sets `search_path = public,ag_catalog` on its own
connections. The setup script enables the required extensions and grants
access in the selected database; extension availability alone does not create
them in every database.

## Step 2 — Create role and database

Add a password line to `~/.pgpass` first (generate a fresh random
password — do not hardcode):

```sh
PASSWORD=$(openssl rand -hex 32)
touch "$HOME/.pgpass"
chmod 600 "$HOME/.pgpass"
printf 'localhost:%s:%s:%s:%s\n' "$PORT" "$DB_NAME" "$DB_USER" "$PASSWORD" >> "$HOME/.pgpass"
```

Run the setup script (creates role, DB, extensions, grants — but
**not** the AGE graph, which mimir's migrations create on first run):

```sh
curl -fsSL https://raw.githubusercontent.com/kamysh/mimir/v2.0.3/mimir-setup/create-db-user.sh \
  | bash -s -- --container "$CONTAINER" --port "$PORT" \
                --user "$DB_USER" --db "$DB_NAME"
```

**Verify:**
```sh
psql -h localhost -p "$PORT" -U "$DB_USER" -d "$DB_NAME" -c '\conninfo' >/dev/null && echo OK
```

## Step 3 — Install binaries

```sh
mkdir -p "$HOME/.local/bin"
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)  TARBALL=mimir-darwin-arm64.tar.gz ;;
  Linux-x86_64)  TARBALL=mimir-linux-amd64.tar.gz ;;
  Linux-aarch64) TARBALL=mimir-linux-arm64.tar.gz ;;
  *) echo "Unsupported platform: $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac
curl -fsSL "https://github.com/kamysh/mimir/releases/download/v2.0.3/${TARBALL}" \
  | tar -xz -C "$HOME/.local/bin"
chmod +x "$HOME/.local/bin/mimir" "$HOME/.local/bin/mimir-mcp"
```

(The 2.0.3 release workflow builds Apple Silicon, Linux x86_64 and Linux ARM64.
Intel Macs require a source build.)

Do **not** run `xattr -d com.apple.quarantine` on these files. The
quarantine flag is only set on browser downloads — `curl` does not
set it, so the command will error with "Permission denied" even
though nothing is wrong. Skip the step entirely.

**Verify:**
```sh
mimir --help >/dev/null && echo OK
```

## Step 4 — Write config (use `mimir init KEY=VALUE ...`, not bare `mimir init`)

Database credentials and TLS options can be specified in `[database]`, including
optional `password` and `pgpassfile`. See [credentials and TLS](docs/database-connections.md)
for source precedence, password-file escaping, CA verification and client certificates.
Keep config files owner-only and avoid printing existing credentials during inspection.

Bare `mimir init` opens `$EDITOR` and blocks. `mimir init` with `KEY=VALUE`
arguments writes the config directly, no editor. Check for an existing config
first, at `${MIMIR_CONFIG:-$HOME/.config/mimir/config.toml}`. If one exists,
inspect the connection and backend settings without printing credentials;
skip creation when they match. Do **not** overwrite a config you did not author
without user confirmation.

If the config is absent, choose **one** creation command:

Belief graph only (omit the embedding arguments entirely):

```sh
mimir init host=localhost port="${PORT}" dbname="${DB_NAME}" user="${DB_USER}"
```

Belief graph and local document embeddings:

```sh
mimir init host=localhost port="${PORT}" dbname="${DB_NAME}" user="${DB_USER}" backend=local
```

For a hosted backend, include its backend, model and API key in that same
initial creation command, for example:

```sh
mimir init host=localhost port="${PORT}" dbname="${DB_NAME}" user="${DB_USER}" \
  backend=voyage model=voyage-3-lite api_key="YOUR_KEY_HERE"
```

For API keys, ask the user — do not invent or fish for keys from the
environment.

For OpenAI, select `backend=openai` and the agreed model. Do not pass `backend=`
with an empty value, or run another creation command against an existing config.

**Verify:** the first `mimir stats` triggers schema migrations,
including AGE graph creation. The first run takes a second longer.

```sh
mimir stats >/dev/null && echo OK
```

## Step 5 — Register the MCP server in the selected client

Inspect the existing registration before adding one. Use the client's matching
commands in [Agent setup](docs/claude-code-setup/INSTALL.md#register-the-mcp-server):

```sh
# Run only the chosen client's command, when registration is absent.
codex mcp add mimir -- "$HOME/.local/bin/mimir-mcp"
claude mcp add --transport stdio --scope user mimir -- "$HOME/.local/bin/mimir-mcp"
```

Verify the actual path and scope with `mcp get mimir`, then establish connectivity
in the selected client. An error may involve credentials, environment or process
startup; inspect the reported cause before changing registration or configuration.

## Step 6 — Install the skill, guidance and startup reminder

Follow [Agent setup](docs/claude-code-setup/INSTALL.md). Include this work in the
agreed installation stage, then complete it and verification without repeatedly
asking for approval of ordinary details. Use the shared skill and Mimir-only
reminder, or one combined Mimir/Muninn reminder when both tools are installed.
Update the existing combined entry rather than adding duplicate hooks.

For upgrades, remove the old Mimir/Muninn automation and enforcement within the
agreed scope, including sentinel/project gates, enforced ratings and Stop requirements.
Align the global instructions and installed skill as well. The guide describes
which settings to preserve, Codex hook trust review, and delivery checks for both
clients. A startup reminder explains why and when to retrieve; it does not query
on every prompt or file action.

## Step 7 — Incremental experiential judge (optional)

The Rust judge is part of the `mimir` binary installed in Step 3. Its settings
belong in the private `~/.config/mimir/config.toml`; use
[`runtime/config.example.toml`](runtime/config.example.toml) and
[`runtime/README.md`](runtime/README.md) to choose a model, backend, and optional
notification settings. Validate with `mimir judge check-config`, then run one
bounded batch with `mimir judge run`. The optional
[`run.sh`](docs/claude-code-setup/mimir-judge-experiential/run.sh) is only a Bash
launcher for that command; the adjacent prompt is reference text, not a file
loaded by the Rust runner. `mimir judge watch` can repeat batches while running,
but this installer does not enable a service or timer. When a scheduled judge
is requested, follow the complete
[schedule and verification procedure](runtime/README.md#configure-a-scheduled-judge).
Do not run the judge as
part of agent installation or use a live account to verify this guide.

## Step 8 — Orphaned Working-belief consolidation judge (optional)

This optional maintenance workflow handles intentionally temporary `working`
beliefs left unresolved by earlier sessions. The standard skill now selects
`fact` or `experiential` explicitly for durable knowledge, and installs no Stop
consolidation gate. Existing working beliefs are not modified by changing hooks.

The historical judge template assumes the earlier working-first/Stop-gate
workflow. Review that assumption, its age criteria and its mutations before
choosing to schedule it. It is separate from a per-turn Claude critic, and is not
required for ordinary retrieval or the new agent integration.

Source files: [`docs/claude-code-setup/mimir-judge-working/`](docs/claude-code-setup/mimir-judge-working/)
(`prompt.md`, `run.sh`, `mcp-config.json`). `mcp-config.json` is for this
separate Claude Code workflow; the Rust experiential judge invokes `mimir-mcp`
from its own TOML configuration.

```sh
cp docs/claude-code-setup/mimir-judge-working/prompt.md \
   "$HOME/.claude/mimir-judge-working-prompt.md"
cp docs/claude-code-setup/mimir-judge-working/mcp-config.json \
   "$HOME/.claude/mimir-judge-mcp.json"
cp docs/claude-code-setup/mimir-judge-working/run.sh \
   "$HOME/.claude/mimir-judge-working.sh"
chmod +x "$HOME/.claude/mimir-judge-working.sh"
```

Unlike Step 7's prompt, this one contains a `CURRENT_TIME_UTC` placeholder —
`run.sh` substitutes it with the real current time at invocation, since the
judge has no clock or shell access of its own and needs a fixed reference
point to compare each belief's `created_at` against. Do not strip this
substitution when adapting the script.

**Scheduling** — same options as Step 7, but hourly instead of weekly:

- **systemd (Linux)**: a `systemd --user` timer running
  `bash "$HOME/.claude/mimir-judge-working.sh"` hourly, output appended to a
  log file. (On NixOS, prefer a declarative `systemd.services`/
  `systemd.timers` module.)
- **launchd (macOS)**: an equivalent hourly `LaunchAgent`.
- **cron**: `0 * * * * $HOME/.claude/mimir-judge-working.sh >> $HOME/.claude/mimir-judge-working.log 2>&1`
  as a fallback.

**Verify:**
```sh
bash "$HOME/.claude/mimir-judge-working.sh"
```
Should complete without error. If it found and processed any orphans, a
summary `working` belief appears under project `mimir-meta`.

## Final verification

Verify application connectivity and the selected client's registration:

```sh
mimir stats >/dev/null
command -v mimir-mcp >/dev/null
"$AGENT_CLIENT" mcp get mimir
```

Then check the agent integration explicitly; a working database or MCP
registration does not prove the agent received useful guidance:

- Inspect the installed skill and global instructions at the actual client paths.
  They should match the purpose-focused workflow, without mandatory-call or
  working-first instructions left over from an earlier installation.
- Parse the client hook configuration. Locate one relevant `SessionStart`
  reminder, inspect the selected Mimir-only or combined text and verify its direct
  output. The static probe in **State detection** is only a locator check.
- For an upgraded setup, compare against the backup: obsolete retrieval,
  sentinel/project gates, enforced ratings and Stop enforcement should be removed as
  agreed; unrelated hooks and settings should be preserved.
- Complete Codex native hook review where applicable. Verify actual delivery at
  startup, resume and after compaction using the client's diagnostic evidence.
- Make a focused retrieval against known stored knowledge. Separately observe
  whether a fresh agent uses relevant memory for an approach question without an
  explicit instruction to call Mimir.

Use the [detailed verification procedure](docs/claude-code-setup/INSTALL.md#verify-configuration-delivery-and-usefulness-separately).
Report results and untested lifecycle/behavioral checks separately. Do not install
old blocking hooks to satisfy checks copied from a historical guide.

## Known errors → fixes

| Error | Cause | Fix |
|---|---|---|
| `Cannot connect to the Docker daemon` | Daemon not running. | Tell the user to start Docker Desktop. Do not try to start it yourself. |
| `docker: ... container name "/postgres-ai" is already in use` | Name collision with an unrelated container. | Pick a different `CONTAINER`. Do **not** delete the existing one without user confirmation — it may hold data. |
| `bind: address already in use` on port 5432 | Another postgres or app on that port. | Pick a different `PORT`. Update `~/.pgpass`, `config.toml`, the `docker run -p` flag, and the setup-script `--port` flag together. |
| `error returned from database: graph "mimir" does not exist` | Migrations have not run yet. Mimir creates the graph on its first invocation. | Run any read-only command first, e.g. `mimir stats`. The migration will create the graph. |
| `error returned from database: permission denied for table _ag_label_vertex` | The connected role lacks access to AGE's catalog table. | Verify the actual role and database, then check the AGE grants made by `mimir-setup/create-db-user.sh`. Changing `search_path` does not grant privileges. |
| `xattr: [Errno 13] Permission denied` on `~/.local/bin/mimir*` | No quarantine flag exists (curl-downloaded). | Skip the `xattr -d` step entirely. |
| `~/.pgpass` ignored | Wrong permissions. | `chmod 600 ~/.pgpass`. |
| MCP shows `Failed to connect` | `mimir-mcp` crashing on startup. | Run `mimir-mcp` directly in a shell; the panic/error message goes to stderr. Usually a DB connectivity or config issue. |
| `error: unable to load document — embeddings not configured` | `[embeddings]` block missing from `config.toml`. | Add an `[embeddings]` block (Step 4). |

## Anti-patterns — things NOT to do

- **Do not run bare `mimir init`.** With no arguments it opens `$EDITOR`
  and will block. Use `mimir init KEY=VALUE ...` (Step 4).
- **Do not overwrite `~/.claude/settings.json`** when installing the
  hooks. The user almost certainly has other settings (theme, model
  selection, other hooks). Read → parse → merge → write back.
- **Do not delete or rename existing Docker containers/volumes** to
  free a name. Confirm with the user first. Data loss is irreversible.
- **Do not pick port 6000 on macOS** — it is X11. Likewise 5000
  (AirPlay Receiver) and any port already shown by
  `lsof -nP -iTCP -sTCP:LISTEN`.
- **Do not register the MCP server at `--scope project`.** Mimir is
  installed once per user, not per repo.
- **Do not chase `xattr` permission errors** on curl-downloaded
  files. Skip the step.
- **Do not invent API keys** for `voyage`/`openai` embedding
  backends. Ask the user, or default `EMBEDDING_BACKEND=local`, or
  omit `[embeddings]` entirely if document search is not needed.
- **Do not overwrite existing config files** (`~/.config/mimir/config.toml`)
  without reading them first. An existing config may have valid settings — check
  before clobbering. See Step 4.
- **Do not assume the AGE graph exists immediately after Step 2.**
  The setup script creates the role, database, extensions, and
  grants — but the AGE graph itself is created by mimir's own
  migrations on first invocation in Step 4. A common mistake (which
  the README's older wording encouraged) is to expect the graph
  after the setup script runs.
- **Do not declare the agent integration verified** from command success alone.
  Complete **Final verification** and report its observed outcomes and limits.

## Companion tool

If you are also installing [muninn](https://github.com/kamysh/muninn)
(the indexed code-search MCP server), the two tools can share **one**
`postgres-ai` container — just create separate roles and databases.
The `kamysh/postgres-ai` image includes the extensions needed by both tools;
each setup script enables them and grants access in its own database.

To share: run only one `postgres-ai` container in Step 1. For mimir,
use the variables in this doc. For muninn, run its setup script
against the same container with a different `--user` / `--db`. See
muninn's [AGENTS.md](https://github.com/kamysh/muninn/blob/main/AGENTS.md)
for the parallel procedure.

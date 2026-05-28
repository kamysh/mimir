# AGENTS.md — install instructions for AI coding agents

This file is the authoritative install procedure for AI coding agents
(Claude Code, Cursor, Aider, etc.) installing mimir. The human-facing
[README.md](README.md#installation) covers the same ground but uses
hedges ("recommended", "optional") that an agent should not rely on.
Follow this file instead.

## Read this first

- All steps are idempotent. Safe to rerun. If interrupted, restart
  from **State detection** below, not from Step 1.
- After every step, run the verify command. Do not stack failures —
  fix the current step before moving on.
- Destructive operations (dropping a database, removing a container,
  overwriting a file you did not author) require user confirmation.
  Stop and ask, even when a step appears to call for it.
- Do **not** run `mimir init` interactively — it opens `$EDITOR` and
  will block your shell indefinitely. Write the config file directly
  using the template in Step 4.

## What a complete install consists of

Mimir has three required pieces. Skipping any one yields a state that
looks installed but fails:

1. A **PostgreSQL container** (or your own DB) holding the belief
   graph and document index.
2. **Two binaries** on `PATH` — `mimir` (CLI) and `mimir-mcp` (the
   MCP server).
3. The `mimir-mcp` server **registered with Claude Code**. Without
   it, Claude Code has no tools to call.

There is **no daemon** to start. The MCP server is spawned by Claude
Code on demand, and the database schema is created on first run via
embedded migrations.

## Variables

**Before doing anything else, ask the user for these values:**

1. **Docker container name** — the local name for the postgres-ai container
   (e.g. `local-postgres-ai`). Check `docker ps -a` and suggest a name that
   doesn't collide. The Docker image is always `kamysh/postgres-ai`.
2. **Port** — the host port to expose PostgreSQL on (default `5432`; check
   `lsof -nP -iTCP -sTCP:LISTEN` for conflicts).
3. **DB user** — the PostgreSQL role to create for mimir (default `mimir`).
4. **DB name** — the database to create (default `mimir`; usually matches the user).

If mimir is being installed alongside muninn (see "Companion tool" at the end),
also confirm whether they share one container or use separate ones.

Bind the answers as shell variables once, then re-use in every command below:

| Variable | Notes |
|---|---|
| `PORT` | Host port. Avoid 5000 (AirPlay on macOS), 6000 (X11), and anything in use. |
| `CONTAINER` | Local container name. Must not collide with an existing container. Image: `kamysh/postgres-ai`. |
| `VOLUME` | Docker volume for the postgres data dir (e.g. `mimir_data`). If sharing a container with muninn, use the same volume. |
| `DB_USER` | PostgreSQL role for mimir. |
| `DB_NAME` | Database for mimir. |
| `EMBEDDING_BACKEND` | `local` (no API key, downloads ~120 MB) \| `voyage` \| `openai`. Required only for `load_document` / `query_document`; omit the `[embeddings]` section entirely if you only need the belief graph. |

## Preflight (must all pass)

```sh
docker info >/dev/null                                                 # daemon running
! lsof -nP -iTCP:"$PORT" -sTCP:LISTEN | grep -q .                      # port free
! docker ps -a --format '{{.Names}}' | grep -qx "$CONTAINER"           # container name free
echo "$PATH" | tr ':' '\n' | grep -qx "$HOME/.local/bin"               # PATH includes target
command -v claude >/dev/null                                           # Claude Code CLI installed
```

If any check fails, stop and report the specific failure to the user.
Do not try to recover automatically.

## State detection — skip steps already complete

Run these probes before doing any work. For each that returns 0, skip
the corresponding step.

```sh
# Step 1 — postgres container running
docker ps --filter "name=^${CONTAINER}$" --filter "status=running" \
  --format '{{.Names}}' | grep -qx "$CONTAINER"

# Step 2 — DB and role exist
docker exec "$CONTAINER" psql -U postgres -lqt \
  | cut -d\| -f1 | grep -qw "$DB_NAME"

# Step 3 — binaries installed
command -v mimir && command -v mimir-mcp >/dev/null

# Step 4 — config exists and CLI can talk to the DB
[ -f "$HOME/.config/mimir/config.toml" ] && mimir stats >/dev/null 2>&1

# Step 5 — MCP registered with Claude Code
claude mcp list 2>&1 | grep -E '^mimir:.*Connected' >/dev/null
```

## Step 1 — Start postgres

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

The `kamysh/postgres-ai` image has pgvector, Apache AGE, uuid-ossp,
and pgcrypto pre-installed, and sets `search_path = ag_catalog,
"$user", public` cluster-wide. Mimir relies on that search_path — if
you use a different postgres image, set it manually with
`ALTER DATABASE "$DB_NAME" SET search_path = ag_catalog, "$user", public;`.

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
curl -fsSL https://raw.githubusercontent.com/kamysh/mimir/main/mimir-setup/create-db-user.sh \
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
  Darwin-x86_64) TARBALL=mimir-darwin-amd64.tar.gz ;;
  Linux-x86_64)  TARBALL=mimir-linux-amd64.tar.gz ;;
  Linux-aarch64) TARBALL=mimir-linux-arm64.tar.gz ;;
  *) echo "Unsupported platform: $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac
curl -fsSL "https://github.com/kamysh/mimir/releases/latest/download/${TARBALL}" \
  | tar -xz -C "$HOME/.local/bin"
chmod +x "$HOME/.local/bin/mimir" "$HOME/.local/bin/mimir-mcp"
```

(Releases ship `darwin-arm64` for Apple Silicon and `darwin-amd64` for Intel Macs.)

Do **not** run `xattr -d com.apple.quarantine` on these files. The
quarantine flag is only set on browser downloads — `curl` does not
set it, so the command will error with "Permission denied" even
though nothing is wrong. Skip the step entirely.

**Verify:**
```sh
mimir --help >/dev/null && echo OK
```

## Step 4 — Write config (do **not** run `mimir init`)

`mimir init` opens `$EDITOR` and blocks. Write the file directly:

```sh
mkdir -p "$HOME/.config/mimir"
cat > "$HOME/.config/mimir/config.toml" <<EOF
[database]
host   = "localhost"
port   = ${PORT}
dbname = "${DB_NAME}"
user   = "${DB_USER}"

[embeddings]
backend = "${EMBEDDING_BACKEND}"
EOF
```

If `EMBEDDING_BACKEND` is `voyage` or `openai`, append model + key
under the `[embeddings]` block:

```toml
model   = "voyage-3-lite"        # or "text-embedding-3-small" for openai
api_key = "YOUR_KEY_HERE"
```

For API keys, ask the user — do not invent or fish for keys from the
environment.

If you only need the belief graph (no document search), you can omit
the entire `[embeddings]` section.

**Verify:** the first `mimir stats` triggers schema migrations,
including AGE graph creation. The first run takes a second longer.

```sh
mimir stats >/dev/null && echo OK
```

## Step 5 — Register MCP server with Claude Code

```sh
claude mcp add --scope user mimir "$HOME/.local/bin/mimir-mcp"
```

Use `--scope user`, never `--scope project`. Mimir is a system-wide
tool, not project-local.

**Verify:**
```sh
claude mcp list 2>&1 | grep -E '^mimir:.*Connected' && echo OK
```

If status is anything other than `Connected`, the MCP server is
crashing on startup. Run `mimir-mcp` directly to see stderr.

## Step 6 — (Optional) Install the skill and hooks

Strongly recommended for actual use — without them, Claude Code has
mimir's tools available but no guidance on when to query them or
write back to them.

The skill file is in this repo at `skill/SKILL.md`. If you have a
local clone, copy from there; otherwise fetch from the raw URL:

```sh
mkdir -p "$HOME/.claude/skills/mimir"
curl -fsSL https://raw.githubusercontent.com/kamysh/mimir/main/skill/SKILL.md \
  -o "$HOME/.claude/skills/mimir/SKILL.md"
```

Merge the following into `~/.claude/settings.json` under the top-level
`"hooks"` key. **Do not blindly overwrite the file** — read the
existing contents first, parse as JSON, merge the `hooks` block,
write back. If existing hook arrays already exist for these events,
append to them.

```json
{
  "hooks": {
    "SessionStart": [
      {
        "hooks": [
          {
            "type": "command",
            "command": "echo 'mcp__mimir tools are available. Invoke the mimir skill now to load the belief graph loop protocol for this session.'"
          }
        ]
      }
    ],
    "UserPromptSubmit": [
      {
        "matcher": "",
        "hooks": [
          {
            "type": "command",
            "command": "echo 'Before acting: query mimir for relevant rules (mcp__mimir__query_relevant), query muninn for relevant code knowledge (mcp__muninn__search_hybrid). Do this BEFORE reading files or writing code.'"
          }
        ]
      }
    ]
  }
}
```

If [muninn](https://github.com/kamysh/muninn) is **not** installed,
drop the `mcp__muninn__search_hybrid` reference from the
`UserPromptSubmit` command:

```
"echo 'Before acting: query mimir for relevant rules (mcp__mimir__query_relevant). Do this BEFORE reading files or writing code.'"
```

Hooks take effect on the **next** Claude Code session, not the
current one.

## Final verification gate

All five lines must print `OK`. If any fails, fix that step before
declaring the install complete.

```sh
mimir stats >/dev/null                                                  && echo OK  # 1
docker ps --filter "name=^${CONTAINER}$" --format '{{.Names}}' \
  | grep -qx "$CONTAINER"                                               && echo OK  # 2
command -v mimir-mcp >/dev/null                                         && echo OK  # 3
psql -h localhost -p "$PORT" -U "$DB_USER" -d "$DB_NAME" \
  -c "SELECT 1 FROM ag_catalog.ag_graph WHERE name='${DB_NAME}'" \
  -tA 2>/dev/null | grep -q 1                                           && echo OK  # 4
claude mcp list 2>&1 | grep -qE '^mimir:.*Connected'                    && echo OK  # 5
```

## Known errors → fixes

| Error | Cause | Fix |
|---|---|---|
| `Cannot connect to the Docker daemon` | Daemon not running. | Tell the user to start Docker Desktop. Do not try to start it yourself. |
| `docker: ... container name "/postgres-ai" is already in use` | Name collision with an unrelated container. | Pick a different `CONTAINER`. Do **not** delete the existing one without user confirmation — it may hold data. |
| `bind: address already in use` on port 5432 | Another postgres or app on that port. | Pick a different `PORT`. Update `~/.pgpass`, `config.toml`, the `docker run -p` flag, and the setup-script `--port` flag together. |
| `error returned from database: graph "mimir" does not exist` | Migrations have not run yet. Mimir creates the graph on its first invocation. | Run any read-only command first, e.g. `mimir stats`. The migration will create the graph. |
| `error returned from database: permission denied for table _ag_label_vertex` | `search_path` is missing `ag_catalog`. The `kamysh/postgres-ai` image sets this cluster-wide; a custom postgres does not. | `ALTER DATABASE "$DB_NAME" SET search_path = ag_catalog, "$user", public;` as the postgres superuser. |
| `xattr: [Errno 13] Permission denied` on `~/.local/bin/mimir*` | No quarantine flag exists (curl-downloaded). | Skip the `xattr -d` step entirely. |
| `~/.pgpass` ignored | Wrong permissions. | `chmod 600 ~/.pgpass`. |
| MCP shows `Failed to connect` | `mimir-mcp` crashing on startup. | Run `mimir-mcp` directly in a shell; the panic/error message goes to stderr. Usually a DB connectivity or config issue. |
| `error: unable to load document — embeddings not configured` | `[embeddings]` block missing from `config.toml`. | Add an `[embeddings]` block (Step 4). |

## Anti-patterns — things NOT to do

- **Do not run `mimir init` interactively.** It opens `$EDITOR` and
  will block. Write the file directly (Step 4).
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
- **Do not assume the AGE graph exists immediately after Step 2.**
  The setup script creates the role, database, extensions, and
  grants — but the AGE graph itself is created by mimir's own
  migrations on first invocation in Step 4. A common mistake (which
  the README's older wording encouraged) is to expect the graph
  after the setup script runs.
- **Do not declare install complete** before running the **Final
  verification gate** above and seeing five `OK` lines.

## Companion tool

If you are also installing [muninn](https://github.com/kamysh/muninn)
(the indexed code-search MCP server), the two tools can share **one**
`postgres-ai` container — just create separate roles and databases.
The `kamysh/postgres-ai` image is designed for this: AGE, pgvector,
and the support extensions are cluster-wide, and the cluster-default
`search_path` works for both tools.

To share: run only one `postgres-ai` container in Step 1. For mimir,
use the variables in this doc. For muninn, run its setup script
against the same container with a different `--user` / `--db`. See
muninn's [AGENTS.md](https://github.com/kamysh/muninn/blob/main/AGENTS.md)
for the parallel procedure.

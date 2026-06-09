# mimir

> *Mimir* (Old Norse: "memory") — the wisest of all beings, keeper of the well of wisdom at the root of Yggdrasil.

Persistent belief graph for [Claude Code](https://claude.ai/code). Mimir stores beliefs, patterns, and the typed relationships between them across sessions, letting Claude reason about its own knowledge over time.

## What it does

Claude Code connects to Mimir via MCP and can:

- Record beliefs with probability and confidence scores
- Link beliefs via typed edges — SUPPORTS, DEFEATS, CAUSES, CONTRADICTS
- Run defeat propagation cascades through the graph
- Decay belief confidence over time
- Index markdown documents and run semantic search over them (RAG)

Everything runs locally. No data leaves your machine unless you choose a cloud embedding backend (Voyage AI or OpenAI) for document search — and even then only short text chunks are sent, never the full document.

## Installation

> **Installing mimir as an AI coding agent?** See [AGENTS.md](AGENTS.md) — it's the same procedure, but framed for automation: explicit variables, verify-after-each-step, state detection for idempotent reruns, and an anti-patterns list.

### What a complete install consists of

Mimir has three required pieces. Skipping any one leaves an install that looks finished but fails:

1. A **PostgreSQL container** (or your own DB) holding the belief graph and document index.
2. **Two binaries** on `PATH` — `mimir` (CLI) and `mimir-mcp` (the MCP server).
3. The `mimir-mcp` server **registered with Claude Code**. Without this, Claude Code has no tools to call.

There is no daemon to start. The MCP server is spawned by Claude Code on demand; the database schema (including the AGE graph) is created automatically by mimir's embedded migrations on first run.

Step 6 at the end of this guide is a one-block verification that all three pieces are in place. Run it before declaring the install complete.

### Conventions used in this guide

This guide uses the following defaults. If you change any of them, change them everywhere they appear:

| Setting | Default | Used in |
|---|---|---|
| PostgreSQL port | `5432` | `docker run`, `~/.pgpass`, `config.toml` |
| Container name | `postgres-ai` | `docker run`, all `docker exec` calls |
| Docker volume | `mimir_data` | `docker run` |
| Database name | `mimir` | setup script, `~/.pgpass`, `config.toml` |
| Database user | `mimir` | setup script, `~/.pgpass`, `config.toml` |

On macOS, avoid ports `5000` (AirPlay Receiver) and `6000` (X11) if you change the port.

### Preflight check

Run these before you start. Each line should print `OK`:

```bash
docker info >/dev/null 2>&1 && echo OK                                            # Docker daemon running
! lsof -nP -iTCP:5432 -sTCP:LISTEN 2>/dev/null | grep -q . && echo OK              # port 5432 free
! docker ps -a --format '{{.Names}}' 2>/dev/null | grep -qx postgres-ai && echo OK # container name free
echo "$PATH" | tr ':' '\n' | grep -qx "$HOME/.local/bin" && echo OK                # PATH includes ~/.local/bin
command -v claude >/dev/null && echo OK                                            # Claude Code CLI installed
```

If any line fails:

- **Docker not running** → start Docker Desktop (or your runtime), then re-check.
- **Port 5432 in use** → either stop the conflicting service or pick a different port. If you change the port, update *everything* in this guide that mentions `5432`.
- **Container name `postgres-ai` in use** → either reuse the existing container (if it's a postgres-ai instance from another tool, like muninn) or pick a new name. Do not delete the existing container without checking what it holds.
- **`~/.local/bin` not on PATH** → add `export PATH="$HOME/.local/bin:$PATH"` to your shell's rc file and reload it.
- **`claude` CLI missing** → install [Claude Code](https://claude.ai/code) before continuing; Step 5 needs it.

### Step 1: Start the database

```bash
docker run -d \
  --name postgres-ai \
  --restart always \
  -p 127.0.0.1:5432:5432 \
  -v mimir_data:/var/lib/postgresql/data \
  kamysh/postgres-ai:latest
```

This image has pgvector, Apache AGE, uuid-ossp, and pgcrypto pre-installed, and sets `search_path = ag_catalog, "$user", public` cluster-wide (mimir relies on this — see Troubleshooting if you use a different image).

<details>
<summary>Docker Compose alternative</summary>

```yaml
services:
  postgres:
    image: kamysh/postgres-ai:latest
    container_name: postgres-ai
    restart: always
    ports:
      - "127.0.0.1:5432:5432"
    volumes:
      - mimir_data:/var/lib/postgresql/data

volumes:
  mimir_data:
```

```bash
docker compose up -d
```

</details>

**Verify:**

```bash
docker exec postgres-ai psql -U postgres -c 'SELECT 1' >/dev/null && echo OK
```

### Step 2: Create the database and user

Add your chosen password to `~/.pgpass`:

```
# ~/.pgpass — format: hostname:port:database:username:password
localhost:5432:mimir:mimir:yourpassword
```

```bash
chmod 600 ~/.pgpass
```

Run the setup script (creates the role, database, extensions, and grants):

```bash
curl -fsSL https://raw.githubusercontent.com/kamysh/mimir/main/mimir-setup/create-db-user.sh \
  | bash
```

Or clone the repo and run it locally:

```bash
bash mimir-setup/create-db-user.sh
```

The AGE graph itself is **not** created by this script — mimir's migrations create it on first invocation in Step 4.

**Verify the connection:**

```bash
psql -h localhost -U mimir -d mimir -c '\conninfo' >/dev/null && echo OK
```

### Step 3: Install the mimir binaries

This step installs the two mimir binaries to `~/.local/bin`. It is one of three pieces — see Step 5 for the MCP server registration.

Download the archive for your platform from the [latest release](https://github.com/kamysh/mimir/releases/latest):

| Platform | File |
|---|---|
| Linux x86_64 | `mimir-linux-amd64.tar.gz` |
| Linux ARM64 | `mimir-linux-arm64.tar.gz` |
| macOS Apple Silicon | `mimir-darwin-arm64.tar.gz` |

(Intel Macs are not built; see "Building from source" below.)

```bash
# Linux x86_64
curl -L https://github.com/kamysh/mimir/releases/latest/download/mimir-linux-amd64.tar.gz \
  | tar -xz -C ~/.local/bin

# Linux ARM64
curl -L https://github.com/kamysh/mimir/releases/latest/download/mimir-linux-arm64.tar.gz \
  | tar -xz -C ~/.local/bin

# macOS Apple Silicon
curl -L https://github.com/kamysh/mimir/releases/latest/download/mimir-darwin-arm64.tar.gz \
  | tar -xz -C ~/.local/bin
```

```bash
chmod +x ~/.local/bin/mimir ~/.local/bin/mimir-mcp
```

**macOS only — quarantine flag.** macOS adds a quarantine attribute to files downloaded via a *browser*, which blocks them from running. If you downloaded the archive with a browser, remove it:

```bash
xattr -d com.apple.quarantine ~/.local/bin/mimir ~/.local/bin/mimir-mcp
```

`curl` downloads do **not** set this attribute, so the command above is unnecessary if you used the `curl` snippet. (It will print "Permission denied" or "no such xattr" — that's expected, not a problem.)

**Verify:**

```bash
mimir --help >/dev/null && echo OK
```

### Step 4: Configure mimir

```bash
mimir init
```

This creates `~/.config/mimir/config.toml` and opens it in `$EDITOR`. Fill in the database section:

```toml
[database]
host   = "localhost"
port   = 5432
dbname = "mimir"
user   = "mimir"      # the role you created in Step 2
```

Password comes from `~/.pgpass` — never from the config file.

**Document search (optional):** To use `load_document` and `query_document`, add an `[embeddings]` section. Three backends are available:

```toml
# Local — no API key, works offline, downloads ~120 MB on first use
[embeddings]
backend = "local"

# Voyage AI — best quality, requires api_key from voyageai.com
# [embeddings]
# backend = "voyage"
# model   = "voyage-3-lite"
# api_key = "pa-..."

# OpenAI — requires api_key from platform.openai.com
# [embeddings]
# backend = "openai"
# model   = "text-embedding-3-small"
# api_key = "sk-..."
```

Save and close the editor.

**Verify** — the first `mimir stats` triggers the schema migrations, including creating the AGE graph. Expect a one-second pause on this first run:

```bash
mimir stats >/dev/null && echo OK
```

### Step 5: Connect Claude Code

```bash
claude mcp add --scope user mimir ~/.local/bin/mimir-mcp
```

Use `--scope user` (not `--scope project`) — mimir is a system-wide tool, not project-local.

Restart Claude Code. The mimir tools will appear in its tools panel.

**Verify:**

```bash
claude mcp list 2>&1 | grep -E '^mimir:.*Connected' && echo OK
```

### Step 6: Verify the install

Before relying on mimir, confirm all three pieces are in place. Each line should print `OK`:

```bash
mimir stats >/dev/null                                                            && echo OK  # 1. CLI talks to DB
docker ps --filter "name=^postgres-ai$" --format '{{.Names}}' | grep -qx postgres-ai && echo OK  # 2. DB container running
command -v mimir-mcp >/dev/null                                                    && echo OK  # 3. MCP binary on PATH
psql -h localhost -U mimir -d mimir \
  -c "SELECT 1 FROM ag_catalog.ag_graph WHERE name='mimir'" -tA 2>/dev/null \
  | grep -q 1                                                                      && echo OK  # 4. AGE graph created by migrations
claude mcp list 2>&1 | grep -qE '^mimir:.*Connected'                               && echo OK  # 5. MCP wired up to Claude Code
```

Five `OK`s = good to go. The most common silent failure is line 4: if it's missing, the migrations haven't run yet (run `mimir stats` once) or the role lacks `search_path = ag_catalog, …` — see Troubleshooting.

### Step 7: Install the skill and hooks (recommended)

The skill teaches Claude Code *how* to use the belief graph — when to read from it, when to write back, and how to calibrate probabilities. The hooks ensure beliefs are surfaced automatically on every session and before every file edit.

**Skill** — copy it to the skills directory (or `install.sh` does this for you):

```bash
mkdir -p ~/.claude/skills/mimir
cp skill/SKILL.md ~/.claude/skills/mimir/SKILL.md
```

**Wire the hooks** — merge the following into `~/.claude/settings.json` under the top-level `"hooks"` key. Do **not** blindly overwrite the file — append to existing arrays if you already have hooks for these events.

```json
{
  "hooks": {
    "SessionStart": [
      {
        "hooks": [
          {
            "type": "command",
            "command": "echo 'mcp__mimir tools are available. Invoke the mimir skill now: load the read+write belief-graph protocol (consult before >2-step exploration, errors, or approach choices; write back what recurs).'"
          }
        ]
      }
    ],
    "UserPromptSubmit": [
      {
        "hooks": [
          {
            "type": "command",
            "command": "mimir hook prompt"
          }
        ]
      }
    ],
    "PreToolUse": [
      {
        "matcher": "Edit|Write|Bash",
        "hooks": [
          {
            "type": "command",
            "command": "mimir hook pretooluse"
          }
        ]
      }
    ]
  }
}
```

`mimir hook prompt` reads the hook JSON from stdin, queries the belief graph on the prompt text, and prints matching beliefs as plain text. `mimir hook pretooluse` does the same for the file path or command, emitting `additionalContext` JSON. Both are built into the `mimir` binary — no shell scripts or extra dependencies needed.

Restart Claude Code for the hooks to take effect.

### Sharing the database with muninn

If you also use [muninn](https://github.com/kamysh/muninn), the two tools can share **one** `postgres-ai` container — just create separate roles and databases. The `kamysh/postgres-ai` image is designed for this: pgvector, AGE, and the support extensions are cluster-wide, and the cluster-default `search_path` works for both tools. In that case, run only one `docker run` from Step 1, and run each tool's setup script against the shared container.

### Troubleshooting

A few failure modes are common enough to call out explicitly:

| Symptom | Likely cause | Fix |
|---|---|---|
| `error returned from database: graph "mimir" does not exist` | Migrations haven't run yet — mimir creates the graph on first invocation, not the setup script. | Run any mimir command, e.g. `mimir stats`. The migration will create the graph. |
| `error returned from database: permission denied for table _ag_label_vertex` | `search_path` is missing `ag_catalog`. The `kamysh/postgres-ai` image sets this cluster-wide; a custom postgres does not. | As the postgres superuser: `ALTER DATABASE mimir SET search_path = ag_catalog, "$user", public;` then reconnect. |
| `Cannot connect to the Docker daemon` | Docker Desktop / runtime not running. | Start it. |
| `docker run` fails with "container name in use" | Another container is already named `postgres-ai` (e.g. from muninn). | Either reuse it — see "Sharing the database with muninn" above — or pick a different name. Do not delete the existing container without checking what's in it. |
| `bind: address already in use` on port 5432 | Another postgres or app is using 5432. | Pick a different port. Update `docker run -p`, `~/.pgpass`, the setup script's `--port` flag, and `~/.config/mimir/config.toml` together. |
| `~/.pgpass` ignored, prompts for password | Wrong file permissions. | `chmod 600 ~/.pgpass`. PostgreSQL silently ignores `~/.pgpass` if it is world- or group-readable. |
| `xattr: Permission denied` on macOS | The file does not have a quarantine flag (curl-downloaded). | Skip the `xattr` step. The binaries run fine without it. |
| MCP shows `Failed to connect` instead of `Connected` | `mimir-mcp` is crashing on startup, usually due to a DB / config error. | Run `mimir-mcp` directly in a shell; the error goes to stderr. Common causes: wrong port in `config.toml`, password mismatch with `~/.pgpass`, embeddings block missing a required `model` field. |
| `load_document` or `query_document` returns `embeddings not configured` | `[embeddings]` block missing from `config.toml`. | Add an `[embeddings]` block (see Step 4). The belief-graph tools work without it; only document search needs it. |

If something is broken in a way not listed here, file an [issue](https://github.com/kamysh/mimir/issues) with the output of:

```bash
mimir --version
mimir stats 2>&1
claude mcp list 2>&1 | grep mimir
docker ps --filter name=postgres-ai
```

## MCP tools

| Tool | What it does |
|---|---|
| `insert_belief` | Add a belief with `content`, `probability` [0,1], `confidence` [0,1] |
| `delete_belief` | Remove a belief and all its edges by `id` |
| `insert_pattern` | Add a pattern with `situation`, `approach`, `success_rate` [0,1] |
| `delete_pattern` | Remove a pattern by `id` |
| `delete_project` | Remove all beliefs and document chunks tagged with a `project` |
| `record_support` | Add a SUPPORTS edge from `from_id` to `to_id` with `weight` |
| `record_cause` | Add a CAUSES edge from `from_id` to `to_id` with `weight` (traversed by `query_intervention`; no auto-propagation) |
| `record_defeat` | Add a DEFEATS edge and trigger defeat propagation cascade |
| `record_contradiction` | Add a bidirectional CONTRADICTS relation between `id_a` and `id_b` |
| `get_belief` | Get a belief by `id` |
| `list_beliefs` | List all beliefs |
| `list_patterns` | List all patterns |
| `get_contradictions` | Find all actively contradicting belief pairs |
| `query_relevant` | Hybrid retrieval: text match + graph expansion, ordered by probability |
| `propagate_from` | Run defeat propagation from a seed belief `id` |
| `query_intervention` | Counterfactual `P(downstream \| do(id = value))`: severs the target's incoming edges, propagates along CAUSES only. Read-only — returns `projected_probability` for causal descendants; never mutates |
| `update_confidence` | Update the `confidence` value of a belief |
| `decay_all` | Apply time decay to all beliefs (`decay_factor` defaults to 0.99) |
| `load_document` | Parse a markdown file into chunks, embed, and index for semantic search |
| `query_document` | Semantic search over indexed document chunks |
| `clear_document` | Remove all chunks and embeddings for a document `path` |

## CLI reference

| Command | What it does |
|---|---|
| `mimir init` | Create `~/.config/mimir/config.toml` and open it in `$EDITOR` |
| `mimir stats` | Print belief, pattern, and edge counts |
| `mimir list [--project NAME] [--limit N]` | List beliefs, sorted by probability |
| `mimir patterns [--limit N]` | List patterns, sorted by success rate |
| `mimir query TEXT [--limit N]` | Hybrid search: text match + graph expansion |
| `mimir intervene UUID VALUE` | Counterfactual `do(belief = VALUE)`: read-only projection of causal descendants |
| `mimir delete UUID` | Delete a belief and all its edges |
| `mimir forget PROJECT` | Delete all beliefs and document chunks for a project |
| `mimir decay [--factor 0.99]` | Apply time decay to all belief confidences |
| `mimir contradictions` | List active contradictions in the graph |
| `mimir load PATH [--project NAME]` | Index a markdown file for semantic search |
| `mimir query-doc CONTEXT [--project NAME] [--limit N]` | Semantic search over chunks |
| `mimir clear-doc PATH` | Remove all chunks and embeddings for a document |

## Building from source

Requires [Nix](https://nixos.org/download) with flakes enabled.

```bash
# Enter the dev shell
nix develop

# Build (dynamic)
cargo build --release -p mimir-mcp
cargo build --release -p mimir-cli

# Build static binary (single self-contained executable)
nix build .#mimir-static    # result/bin/mimir-mcp and result/bin/mimir

# Install from source into Nix profile and register with Claude Code
./install.sh
```

## License

Apache License 2.0 — see [LICENSE](LICENSE).

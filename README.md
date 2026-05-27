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

### Step 1: Start the database

```bash
docker run -d \
  --name postgres-ai \
  --restart always \
  -p 127.0.0.1:5432:5432 \
  -v mimir_data:/var/lib/postgresql/data \
  kamysh/postgres-ai:latest
```

This image has pgvector, Apache AGE, uuid-ossp, and pgcrypto pre-installed. No extension setup required.

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

### Step 2: Create the database and user

Add your chosen password to `~/.pgpass`:

```
# ~/.pgpass — format: hostname:port:database:username:password
localhost:5432:mimir:mimir:yourpassword
```

```bash
chmod 600 ~/.pgpass
```

Run the setup script (creates the role, database, extensions, and AGE graph):

```bash
curl -fsSL https://raw.githubusercontent.com/kamysh/mimir/main/mimir-setup/create-db-user.sh \
  | bash
```

Or clone the repo and run it locally:

```bash
bash mimir-setup/create-db-user.sh
```

Verify the connection:

```bash
psql -h localhost -U mimir -d mimir -c '\conninfo'
```

### Step 3: Download mimir

Download the archive for your platform from the [latest release](https://github.com/kamysh/mimir/releases/latest):

| Platform | File |
|---|---|
| Linux x86_64 | `mimir-linux-amd64.tar.gz` |
| Linux ARM64 | `mimir-linux-arm64.tar.gz` |
| macOS Apple Silicon | `mimir-darwin-arm64.tar.gz` |

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

**macOS only** — remove the quarantine flag added to browser downloads (not needed with `curl`):

```bash
xattr -d com.apple.quarantine ~/.local/bin/mimir ~/.local/bin/mimir-mcp
```

Make sure `~/.local/bin` is on your `PATH`. If `mimir --help` does not work, add `export PATH="$HOME/.local/bin:$PATH"` to your shell rc file and reload it.

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

### Step 5: Connect Claude Code

```bash
claude mcp add --scope user mimir ~/.local/bin/mimir-mcp
```

Restart Claude Code. The mimir tools will appear in its tools panel.

### Step 6: Install the skill and hooks (recommended)

The skill teaches Claude Code *how* to use the belief graph — when to read from it, when to write back, and how to calibrate probabilities. The hooks ensure it fires automatically on every session and message.

**Skill:**

```bash
mkdir -p ~/.claude/skills/mimir
cp skill/SKILL.md ~/.claude/skills/mimir/SKILL.md
```

**Hooks** — merge the following into `~/.claude/settings.json` under the top-level `"hooks"` key (create the key if it doesn't exist; append to existing arrays if you already have hooks for these events):

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

The `UserPromptSubmit` hook references both mimir and [muninn](https://github.com/kamysh/muninn) — a companion semantic code-knowledge store. If you are not using muninn, replace the hook command with:

```
"echo 'Before acting: query mimir for relevant rules (mcp__mimir__query_relevant). Do this BEFORE reading files or writing code.'"
```

Restart Claude Code for the hooks to take effect.

## MCP tools

| Tool | What it does |
|---|---|
| `insert_belief` | Add a belief with `content`, `probability` [0,1], `confidence` [0,1] |
| `delete_belief` | Remove a belief and all its edges by `id` |
| `insert_pattern` | Add a pattern with `situation`, `approach`, `success_rate` [0,1] |
| `delete_pattern` | Remove a pattern by `id` |
| `delete_project` | Remove all beliefs and document chunks tagged with a `project` |
| `record_support` | Add a SUPPORTS edge from `from_id` to `to_id` with `weight` |
| `record_defeat` | Add a DEFEATS edge and trigger defeat propagation cascade |
| `record_contradiction` | Add a bidirectional CONTRADICTS relation between `id_a` and `id_b` |
| `get_belief` | Get a belief by `id` |
| `list_beliefs` | List all beliefs |
| `list_patterns` | List all patterns |
| `get_contradictions` | Find all actively contradicting belief pairs |
| `query_relevant` | Hybrid retrieval: text match + graph expansion, ordered by probability |
| `propagate_from` | Run defeat propagation from a seed belief `id` |
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

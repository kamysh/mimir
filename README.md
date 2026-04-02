# Mimir

Persistent belief graph MCP server for Claude Code. Mimir stores beliefs, patterns, and the relationships between them (supports, defeats, contradicts) across sessions, letting Claude reason about its own knowledge over time.

Named after the Norse figure whose well holds all wisdom — consulted at great cost, returned with understanding.

## What it does

Claude Code connects to Mimir via MCP and can:
- Record beliefs and patterns with probability and confidence scores
- Link beliefs via typed edges (SUPPORTS, DEFEATS, CAUSES, CONTRADICTS)
- Query relevant beliefs for the current context
- Propagate defeat cascades through the graph
- Decay belief confidence over time

## Prerequisites

- **Nix** with flakes enabled
- **Docker** running a PostgreSQL image with the [Apache AGE](https://age.apache.org/) extension
- **direnv** (recommended — loads `.envrc` automatically)

## Configuration

All configuration lives in `.envrc` at the project root. This file is gitignored — create it from the template:

```bash
cat > .envrc <<'EOF'
export DBHOST=<postgres host>
export DBPORT=<postgres port>
export DBNAME=mimir
export DBUSER=mimir
export DOCKER_CONTAINER=<docker container name running postgres>
EOF
direnv allow
```

Then add a password entry to `~/.pgpass` so the admin setup script can authenticate:

```bash
echo "${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}:<password>" >> ~/.pgpass
chmod 0600 ~/.pgpass
```

## Installation

```bash
./install.sh
```

This will:
1. Create the `mimir` PostgreSQL role and database
2. Install required extensions (AGE, pgvector, uuid-ossp, pgcrypto)
3. Configure permissions and create the AGE graph
4. Build the `mimir-mcp` binary
5. Write `.mcp.json` so Claude Code finds the server

Restart Claude Code after installation.

### Options

```
./install.sh [--dbhost HOST] [--dbport PORT] [--dbname DB] [--dbuser USER]
             [--docker CONTAINER] [--force]
```

CLI args override `.envrc` values. `--force` overwrites `~/.config/mimir/config.toml` if it already exists.

### Rebuilding the binary

If you update the source, delete the binary and re-run the installer:

```bash
rm target/release/mimir-mcp
./install.sh
```

Or build directly:

```bash
nix develop --command cargo build --release -p mimir-mcp
```

## MCP tools

Once installed, Claude Code has access to these tools:

| Tool | Description |
|------|-------------|
| `insert_belief` | Add a belief with `content`, `probability` [0,1], `confidence` [0,1] |
| `insert_pattern` | Add a pattern with `situation`, `approach`, `success_rate` [0,1] |
| `record_support` | Add a SUPPORTS edge from `from_id` to `to_id` with `weight` |
| `record_defeat` | Add a DEFEATS edge and trigger defeat propagation cascade |
| `record_contradiction` | Add a bidirectional CONTRADICTS relation between `id_a` and `id_b` |
| `get_belief` | Get a belief by `id` |
| `list_beliefs` | List all beliefs |
| `list_patterns` | List all patterns |
| `get_contradictions` | Find all actively contradicting belief pairs |
| `query_relevant` | Hybrid retrieval: text match + graph expansion, ordered by probability |
| `propagate_from` | Run defeat propagation from a seed belief `id` |
| `update_confidence` | Update the confidence value of a belief |
| `decay_all` | Apply time decay to all beliefs (`decay_factor` defaults to 0.99) |

## Running integration tests

```bash
nix develop --command cargo test -p mimir-core --test store_integration
```

`MIMIR_DSN` must be set (the `nix develop` shell constructs it from `.envrc` values).

## Project structure

```
mimir-setup/
  01-admin-db-setup.sh   # Creates DB, role, extensions, AGE graph (run as admin once)
  02-user-setup.sh       # Builds binary, writes .mcp.json (run per user)
install.sh               # Orchestrates both setup steps
crates/
  core/                  # mimir-core: graph types, AGE store, inference engine
  mcp/                   # mimir-mcp: MCP server (stdio JSON-RPC)
spec/
  Mimir.agda             # Formal spec (Agda, --safe mode)
```
# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

Mimir is a persistent belief graph MCP server for Claude Code. It stores beliefs, patterns, and typed edges (SUPPORTS, DEFEATS, CAUSES, CONTRADICTS) in PostgreSQL via the Apache AGE graph extension, and exposes them to Claude via stdio JSON-RPC (MCP protocol).

## Commands

All commands assume you're in a Nix dev shell. Enter it with `nix develop` (direnv does this automatically if `.envrc` is allowed).

```bash
# Build (dynamic, glibc)
# Note: the CLI crate's cargo package name is `mimir` (dir crates/cli), not `mimir-cli`.
cargo build --release -p mimir-mcp
cargo build --release -p mimir

# Build static binary (musl, no external deps) — via Nix
nix build .#mimir-static        # result/bin/mimir-mcp and result/bin/mimir

# Build static binary manually inside devShell (requires musl linker on PATH)
cargo build --release --target x86_64-unknown-linux-musl

# Check (fast, no codegen)
cargo check

# Unit tests (no DB required)
cargo test -p mimir-core

# Run a single test module or function
cargo test -p mimir-core graph::tests
cargo test -p mimir-core inference::tests::test_attenuate_by_defeat

# Integration tests (require live PostgreSQL + MIMIR_DSN)
cargo test -p mimir-core --test store_integration

# Lint
cargo clippy

# Verify Agda spec type-checks
cd spec && agda Mimir.agda

# CLI (after `mimir init` writes ~/.config/mimir/config.toml)
mimir stats
mimir list [--project NAME] [--limit N]
mimir query TEXT [--limit N] [--project NAME] [--prefer-type fact|experiential|working]
mimir delete belief UUID
mimir delete pattern UUID
mimir forget PROJECT
mimir decay [--factor 0.99] [--project NAME]
mimir contradictions [--project NAME]
mimir patterns [--project NAME] [--limit N]
mimir sweep-defeated [--threshold 0.3] [--grace-hours 24] [--project NAME]  # attenuated deletion of defeated beliefs past grace period
mimir reembed                                 # one-time backfill of belief_embeddings for pre-existing beliefs

# Claude Code hook subcommands (invoked by settings.json, not directly)
mimir hook prompt                             # UserPromptSubmit — inject relevant beliefs
mimir hook pretooluse                         # PreToolUse — inject beliefs relevant to the file/command
mimir hook stop [--project NAME]              # Stop — blocks the turn while memory_type=working beliefs are unconsolidated

# Document RAG (requires [embeddings] in config.toml)
mimir doc load PATH [--project NAME]          # parse, embed, and index a markdown file
mimir doc query CONTEXT [--project NAME] [--limit N]  # semantic search over chunks
mimir doc clear PATH                          # remove all chunks for a document

# Full install (DB setup + binary build + .mcp.json registration)
./install.sh
```

## Architecture

**Cargo workspace**: `crates/core` (`mimir-core`), `crates/mcp` (`mimir-mcp`), `crates/cli` (`mimir-cli`).

**Core layer** (`crates/core/src/`):
- `graph.rs` — domain types: `Belief`, `Pattern`, `Edge`, `EdgeType`, `Probability` (validated `[0,1]` newtype). All construction is fallible.
- `store.rs` — `AgeStore`: all graph DB operations. Queries are Cypher strings interpolated into `ag_catalog.cypher(...)` SQL calls.
- `inference.rs` — `InferenceEngine`: pure computation only (no I/O). Defeat attenuation formula: `P(target) × (1 − weight × P(defeater))`. Support boost: `P + (1−P) × weight × P(supporter)`.
- `lib.rs` — `MimirService`: composes `AgeStore` + `InferenceEngine`. This is the public API surface.
- `config.rs` — `Config` / `DatabaseConfig`, loaded from `~/.config/mimir/config.toml`. Passwords come from `~/.pgpass`, never from config.
- `documents.rs` — `DocumentChunk`, `QueryResult`, `parse_markdown`. Splits markdown into heading-bounded chunks with pre-assigned UUIDs for parent tracking.
- `embed.rs` — `EmbeddingProvider` trait + `VoyageBackend`, `OpenAiBackend`, `LocalBackend` (fastembed + BGE-Base-EN-v1.5 via ONNX Runtime). `make_backend()` is the factory. `vec_literal()` formats `Vec<f32>` for pgvector SQL interpolation.
- Document chunks are stored as `DocumentChunk` vertices in AGE + CONTAINS edges; embeddings live in `public.chunk_embeddings` (pgvector). The two-store split is required because AGE's `agtype` cannot hold a `vector` value.

**MCP server** (`crates/mcp/src/main.rs`): single-file stdio JSON-RPC loop. Reads one JSON line → dispatches to `MimirService` → writes one JSON line. Tracing goes to stderr only.

**CLI** (`crates/cli/src/main.rs`): clap-based; thin wrappers around `MimirService`. Shares config loading with MCP.

## AGE / Cypher quirks

AGE 1.x does not support parameterized queries — all values are string-interpolated into Cypher. The `esc()` helper in `store.rs` escapes backslashes then single quotes for safe interpolation. Always use `esc()` for string values.

AGE scalar properties can't be extracted by casting a whole vertex/edge to `TEXT`. Instead, return individual properties (e.g., `RETURN n.id, n.content, …`) and cast each to `text` via the column alias declaration. See `BELIEF_RETURN_COLUMNS` / `PATTERN_RETURN_COLUMNS` constants in `store.rs`.

CONTRADICTS edges are stored bidirectionally (two directed edges per logical pair). The `count_edges` method returns the raw directed count; `MimirStats.contradicts / 2` gives logical pairs.

AGE 1.x does not support `[:A|B]` relationship-type OR syntax. Use UNION inside the Cypher block instead (see `get_downstream_beliefs`).

## Formal spec

`spec/Mimir.agda` and its submodules (`Types`, `Inference`, `Setup`, `Graph`, `Documents`, `Evidence`) are compiled with `--safe` mode. The spec is Agda-only; no Haskell runtime is involved. Run `agda Mimir.agda` inside `spec/` to typecheck. `Inference` proves the do-operator's `intervene-ignores-parents`; `Evidence` proves `propagate-evidence-invariant` (GROUNDS edges never perturb belief inference).

## Configuration and environment

`.envrc` (gitignored) sets `DBHOST`, `DBPORT`, `DBNAME`, `DBUSER`, `DOCKER_CONTAINER`. direnv loads it automatically. Integration tests construct `MIMIR_DSN` from these vars inside the Nix shell.

The MCP server and CLI read `~/.config/mimir/config.toml` at startup; `mimir init` writes a commented template and opens `$EDITOR`.
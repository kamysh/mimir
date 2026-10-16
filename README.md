<!-- ══════════════════════════════════════════════════════════════════════
     AI CODING AGENTS (Claude Code, Cursor, Copilot, Aider, …): STOP HERE.

     This README is written for HUMANS. The install/upgrade steps below are
     the human path; they are NOT your procedure. Do not act on any command
     in this README.

     YOUR procedure is AGENTS.md, in this same directory — same end state,
     but with explicit variables, verify-after-each-step, and idempotent
     state detection. Read that file and follow it exactly.
     ══════════════════════════════════════════════════════════════════════ -->

> ⛔ **AI coding agents — this file is not for you.**
> The steps below are the *human* install path. Your procedure is
> **[AGENTS.md](AGENTS.md)** — open that file, follow it exactly, and ignore the
> rest of this README.

# mimir

> *Mimir* (Old Norse: "memory") — the wisest of all beings, keeper of the well of wisdom at the root of Yggdrasil.

Persistent belief graph for AI coding agents, including Codex and [Claude Code](https://claude.ai/code). Mimir preserves decisions, rejected approaches and lessons across sessions, so an agent can use prior reasoning instead of repeating investigation and mistakes.

## What it does

Claude Code connects to Mimir via MCP and can:

- Record beliefs with probability and confidence scores
- Link beliefs via typed edges — SUPPORTS, DEFEATS, CAUSES, CONTRADICTS
- Run defeat propagation cascades through the graph
- Decay belief confidence over time
- Index markdown documents and run semantic search over them (RAG)

The graph and search can run locally. A configured cloud embedding backend sends
document chunks to its provider. A configured API judge sends the selected
experience and retrieved tool results to its provider; a CLI harness uses its
configured model account. The judge does not run automatically.

Optional judge configuration and maintenance are covered in the
[runtime guide](runtime/README.md).

## Installation

> ⛔ **AI coding agents: do not follow this section.** These are the *human*
> install steps. Your procedure is **[AGENTS.md](AGENTS.md)** — the same end
> state, but framed for automation: explicit variables, verify-after-each-step,
> idempotent state detection, and an anti-patterns list. Read that and nothing
> else here.

### What a complete install consists of

Mimir has three required pieces. Skipping any one leaves an install that looks finished but fails:

1. A **PostgreSQL container** (or your own DB) holding the belief graph and document index.
2. **Two binaries** on `PATH` — `mimir` (CLI) and `mimir-mcp` (the MCP server).
3. The `mimir-mcp` server **registered with your agent client** (Codex or Claude Code).

There is no daemon to start. The MCP server is spawned by Claude Code on demand; the database schema (including the AGE graph) is created automatically by mimir's embedded migrations on first run.

Step 6 checks the application connection; Step 7 installs and verifies the skill,
standing guidance and lifecycle reminder. A connected tool alone does not explain
when retrieval can improve a decision.

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

Install `curl`, `tar`, `openssl`, `lsof`, and the PostgreSQL client (`psql`)
if they are missing. Run these before you start. Each line should print `OK`:

```bash
docker info >/dev/null 2>&1 && echo OK                                            # Docker daemon running
! lsof -nP -iTCP:5432 -sTCP:LISTEN 2>/dev/null | grep -q . && echo OK              # port 5432 free
! docker ps -a --format '{{.Names}}' 2>/dev/null | grep -qx postgres-ai && echo OK # container name free
echo "$PATH" | tr ':' '\n' | grep -qx "$HOME/.local/bin" && echo OK                # PATH includes ~/.local/bin
command -v claude >/dev/null && echo OK                                            # or: command -v codex
```

If any line fails:

- **Docker not running** → start Docker Desktop (or your runtime), then re-check.
- **Port 5432 in use** → either stop the conflicting service or pick a different port. If you change the port, update *everything* in this guide that mentions `5432`.
- **Container name `postgres-ai` in use** → either reuse the existing container (if it's a postgres-ai instance from another tool, like muninn) or pick a new name. Do not delete the existing container without checking what it holds.
- **`~/.local/bin` not on PATH** → add `export PATH="$HOME/.local/bin:$PATH"` to your shell's rc file and reload it.
- **Chosen client missing** → install Codex or [Claude Code](https://claude.ai/code) before Step 5.

### Step 1: Start the database

```bash
docker run -d \
  --name postgres-ai \
  --restart always \
  -p 127.0.0.1:5432:5432 \
  -v mimir_data:/var/lib/postgresql/data \
  kamysh/postgres-ai:latest
```

This image includes pgvector, Apache AGE, uuid-ossp, and pgcrypto. The setup script below enables the required extensions in Mimir's database. Mimir sets `search_path = public,ag_catalog` on its own connections.

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

Generate a password with `openssl rand -hex 32` and add it to `~/.pgpass`.
For an existing password, escape `:` as `\:` and `\` as `\\` in each `.pgpass`
field. Quotes and spaces are literal and must be preserved.

```
# ~/.pgpass — format: hostname:port:database:username:password
localhost:5432:mimir:mimir:yourpassword
```

```bash
chmod 600 ~/.pgpass
```

Run the setup script (creates the role, database, extensions, and grants):

```bash
curl -fsSL https://raw.githubusercontent.com/kamysh/mimir/v2.0.2/mimir-setup/create-db-user.sh \
  | bash -s -- --container postgres-ai --host localhost --port 5432 --user mimir --db mimir
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

> _Agents: do not run this step. This is the human download-the-release path.
> Your build/install procedure is in [AGENTS.md](AGENTS.md)._

This step installs the two mimir binaries to `~/.local/bin`. It is one of three pieces — see Step 5 for the MCP server registration.

Install the **2.0.2** release. This block selects one archive for your platform:

```bash
mkdir -p "$HOME/.local/bin"
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)  TARBALL=mimir-linux-amd64.tar.gz ;;
  Linux-aarch64) TARBALL=mimir-linux-arm64.tar.gz ;;
  Darwin-arm64)  TARBALL=mimir-darwin-arm64.tar.gz ;;
  *) echo "Use Building from source for this platform" >&2; exit 1 ;;
esac
curl -fL "https://github.com/kamysh/mimir/releases/download/v2.0.2/${TARBALL}" \
  | tar -xz -C "$HOME/.local/bin"
chmod +x "$HOME/.local/bin/mimir" "$HOME/.local/bin/mimir-mcp"
export PATH="$HOME/.local/bin:$PATH"
mimir --version  # must report 2.0.2
```

The release workflow builds Linux x86_64, Linux ARM64 and Apple Silicon.
For Intel macOS, use [Building from source](#building-from-source).

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

Credentials can come from optional `database.password`, then `PGPASSWORD`, then
a password file. Optional `database.pgpassfile` selects that file ahead of
`PGPASSFILE` and `~/.pgpass`. See [database credentials and TLS](docs/database-connections.md)
for configuration examples, client certificates and verification modes.

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

### Step 5: Connect your agent client

Follow [Agent setup](docs/claude-code-setup/INSTALL.md#register-the-mcp-server)
for Codex or Claude Code. Inspect existing registration first. For a new setup,
run the matching command:

```sh
# Codex
codex mcp add mimir -- "$HOME/.local/bin/mimir-mcp"
# Claude Code
claude mcp add --transport stdio --scope user mimir -- "$HOME/.local/bin/mimir-mcp"
```

Use the client's `mcp get mimir` to check the configured path, and reconnect or
open a fresh session to verify an actual tool call.

### Step 6: Verify the install

Before relying on mimir, confirm all three pieces are in place. Each line should print `OK`:

```bash
mimir stats >/dev/null                                                            && echo OK  # 1. CLI talks to DB
docker ps --filter "name=^postgres-ai$" --format '{{.Names}}' | grep -qx postgres-ai && echo OK  # 2. DB container running
command -v mimir-mcp >/dev/null                                                    && echo OK  # 3. MCP binary on PATH
psql -h localhost -U mimir -d mimir \
  -c "SELECT 1 FROM ag_catalog.ag_graph WHERE name='mimir'" -tA 2>/dev/null \
  | grep -q 1                                                                      && echo OK  # 4. AGE graph created by migrations
claude mcp get mimir                                                             && echo OK  # 5. or: codex mcp get mimir
```

These checks cover application/configuration state, not live tool connectivity
or reminder delivery. Continue with Step 7. If line 4 is missing, inspect the error from `mimir stats`: startup migrations or database permissions may have failed — see Troubleshooting.

### Step 7: Install purposeful agent guidance

Follow [Agent setup](docs/claude-code-setup/INSTALL.md) to install the shared skill,
merge the Mimir section into global instructions, and install one SessionStart
reminder for the chosen client. The guide supplies Mimir-only and combined
Mimir/Muninn text, client-specific hook templates, and upgrade steps for older
settings. `install.sh` optionally registers the selected client; skill/reminder/global-guidance
merging and verification still use the guide.

The reminder explains how past decisions and failures can inform today's choices,
including after resume or compaction. The skill explains focused project-scoped
queries, checking beliefs against current evidence, and writing durable findings.
The standard setup does not run automatic retrieval before every prompt/action,
require hook-generated ratings or writes each turn, or enforce queries through
blocking hooks. Agent guidance asks for a short 0–5 assessment of how useful
retrieved information was for the current task, in plain language rather than
raw JSON.

Verify the selected text and command output, then actual delivery in the client.
Codex requires native review of new or changed hook definitions. Finally, observe
whether the agent retrieves a relevant lesson on a real task without being told
the tool name. Report untested lifecycle events and behavioral checks; reminder
presence alone does not prove it changes the agent's choices.

### Sharing the database with muninn

If you also use [muninn](https://github.com/kamysh/muninn), the two tools can share **one** `postgres-ai` container — create separate roles and databases. Run only one `docker run` from Step 1, and run each tool's setup script against the shared container to enable extensions and grant access in its database.

### Troubleshooting

A few failure modes are common enough to call out explicitly:

| Symptom | Likely cause | Fix |
|---|---|---|
| `error returned from database: graph "mimir" does not exist` | Migrations haven't run yet — mimir creates the graph on first invocation, not the setup script. | Run any mimir command, e.g. `mimir stats`. The migration will create the graph. |
| `error returned from database: permission denied for table _ag_label_vertex` | The connected role lacks access to AGE's catalog table. | Verify the role and database, then check the grants made by `mimir-setup/create-db-user.sh`. Changing `search_path` does not grant privileges. |
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
| `insert_belief` | Add an independently sourced belief with `content`, `probability` [0,1], `confidence` [0,1], and required `provenance` (`basis`, `reference`) |
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
| `add_evidence` | Ground a belief in a document passage: GROUNDS edge from a `chunk_id` to a `belief_id` (`weight` default 1.0). Adds local positive evidence; never becomes a causal edge |
| `get_evidence` | List the document passages grounding a `belief_id`, strongest first |
| `query_relevant` (`include_evidence: true`) | Each returned belief also carries an `evidence[]` array of its top-`evidence_per_belief` grounding passages |

## Learning from experience

Mimir supplies the durable learning operations; an LLM agent or experiential
runner interprets observations and proposes hypotheses. `mimir judge watch`
can poll the queue when launched; no service or timer is installed by this
source change.

The application loop is:

1. `record_experience` records a project, situation, action, observed outcome,
   evidence references, and optionally the beliefs/procedure used. Choose a
   stable UUID for an incident. Send `expected_revision: 0` to create it, then
   the returned revision when correcting it. Replaying the same submission does
   not count another observation. Evidence references are supplied by the
   caller; Mimir does not independently verify their contents.
2. `pending_experiences` returns a bounded batch of new or changed experiences,
   oldest first. The runner can run frequently and exit immediately on an empty
   batch. A successful review removes that version from the pending set. There
   is no collection-size cutoff or requirement to manufacture summary beliefs.
3. The runner retrieves relevant beliefs and inspects evidence. A new
   explanation or procedure is declared as a stable-key candidate inside
   `review_experience`, so its identity and contribution belong to that incident.
   Do not first create a standalone belief from the same report and count the
   review as independent confirmation. The review contains a rationale,
   support/defeat feedback, and optional `Supports`, `Defeats`, `Causes`, or
   `Contradicts` relationships. All mutation targets must belong to the
   experience's exact project; a project observation cannot implicitly revise
   global or another project's knowledge.
4. Mimir applies the review and acknowledges the reviewed version in one
   transaction. The existing Beta engine recomputes affected beliefs and their
   descendants. Reviewed causal links participate in `query_intervention`;
   this is a projection under the recorded hypothesis, not proof that the
   hypothesis identifies a real causal effect. Success alone does not establish
   causation. The runner should compare predictions with later observations.
5. Correcting an experience invalidates its earlier review and removes that
   review's effects. Correcting a review replaces its entire contribution;
   empty feedback, links and supersession lists retract it. Both operations
   retain history and reject stale revision tokens. Concurrent reviewers do not
   need a lease: the first valid revision wins, and the other must re-read.

`get_experience` returns the current version and review tokens.
`experience_history` exposes previous observations and judgments.
`explain_belief` returns incoming reasoning edges and paged active reviews,
linking an inferred probability back to the observations that influenced it.
Retries are deduplicated by incident UUID, not by semantic similarity: callers
must reuse the same identity rather than submit the same incident under new IDs.

Reviews can explicitly mark `superseded_beliefs`. These leave normal retrieval
even when their original prior is strong. This is separate from probabilistic
counter-evidence; a single defeat does not automatically retire a belief.
Replacing the review can restore a mistakenly superseded belief.

MCP `insert_belief` now requires explicit independent `provenance` with a
`user_instruction` or `document` basis and a nonempty source reference. The
source is stored with the graph node and shown by `explain_belief`; untagged MCP
writes are rejected. This is a provenance declaration by the caller, not proof
that the cited source is authentic. Incident-derived conclusions still belong
to atomic review candidates. Existing CLI belief insertion remains available
for explicit manual operations.

`insert_pattern` now accepts `project`. `query_learning_context` returns relevant
beliefs plus situation-matched patterns, with successes, failures, unresolved
outcomes and an observed Beta(1,1) success estimate. Only current experience
versions count. Agent reports remain visible as unresolved observations; they
are not measured successes. The originally asserted pattern success rate stays
separate for compatibility. Procedure matching is lexical, while beliefs retain
hybrid retrieval. Retrieving a procedure never counts as successfully using it.

Existing document evidence remains outside belief-to-belief and causal traversal.
Its local positive evidence mass is retained when propagation or a review
recomputes a posterior. Learned feedback is also retained by later propagation.

### Runner contract

For each pending item, submit:

```json
{
  "expected_review_revision": 0,
  "review": {
    "experience_id": "<experience UUID>",
    "experience_revision": 1,
    "reviewer": "experiential-runner",
    "rationale": "Evidence and alternative explanations considered",
    "feedback": [],
    "links": [],
    "superseded_beliefs": []
  }
}
```

Use the actual revision values returned by the pending item. An empty assessment
acknowledges that the experience was considered without claiming a new lesson.
A link has `from_id`, `to_id`, `relation` and `weight` in [0,1]; feedback has
`belief_id`, `verdict` (`support` or `defeat`) and `weight` in [0,1]. Existing
manually recorded edges are not removed when a review is replaced.

The [Rust learning runtime](runtime/README.md) provides `mimir judge` commands
and locally tested Claude Code, Codex, custom-command, OpenAI, Anthropic,
OpenRouter, DeepSeek, Z.ai, Gemini, and explicit OpenAI-compatible adapters.
It is included in `mimir` but is not scheduled automatically. A bounded Step 11
Codex comparison exercised live model calls; other provider/account behavior
has not been verified. The shared agent skill explains experience
capture and correction. No performance gain is claimed merely from the existing
learning infrastructure.

### Verification

The Rust learning integration tests require an isolated database whose name
starts with `mimir_learning_test`. Provision its application role through
`mimir-setup/create-db-user.sh`; `postgres` is for administration inside the
container, not the external application connection. Set `MIMIR_HOST`,
`MIMIR_PORT`, `MIMIR_DBNAME` and `MIMIR_USER`, then run:

```sh
cargo test --workspace --lib --bins --test learning_integration --test store_integration -- --test-threads=1
```

The tests cover causal projection/retraction, retry idempotence, stale and
concurrent reviews, reversible supersession, project isolation, corrected
pattern outcomes, and incremental processing beyond 200 experiences.
`spec/Mimir/Learning.agda` proves general contribution replacement and stale
review exclusion laws; the aggregate specification is `spec/Mimir.agda`.
These laws model the lifecycle, not the SQL implementation itself.

## CLI reference

| Command | What it does |
|---|---|
| `mimir init [KEY=VALUE ...]` | With no args: create `~/.config/mimir/config.toml` and open it in `$EDITOR`. With `KEY=VALUE` args (e.g. `host=localhost backend=local`): write the config non-interactively, no `$EDITOR` |
| `mimir stats` | Print belief, pattern, and edge counts |
| `mimir list [--project NAME] [--limit N]` | List beliefs, sorted by probability |
| `mimir patterns [--project NAME] [--limit N]` | List patterns, sorted by success rate |
| `mimir query TEXT [--limit N] [--evidence] [--project NAME]` | Hybrid search; `--evidence` also prints each belief's grounding passages |
| `mimir intervene UUID VALUE` | Counterfactual `do(belief = VALUE)`: read-only projection of causal descendants |
| `mimir evidence add CHUNK_ID BELIEF_ID [--weight W]` | Ground a belief in a document chunk (GROUNDS edge) |
| `mimir evidence list BELIEF_ID` | List the passages grounding a belief |
| `mimir delete belief UUID` | Delete a belief and all its edges |
| `mimir delete pattern UUID` | Delete a pattern |
| `mimir forget PROJECT` | Delete all beliefs and document chunks for a project |
| `mimir decay [--factor 0.99] [--project NAME]` | Apply time decay to belief confidences |
| `mimir contradictions [--project NAME]` | List active contradictions in the graph |
| `mimir doc load PATH [--project NAME]` | Index a markdown file for semantic search |
| `mimir doc query CONTEXT [--project NAME] [--limit N]` | Semantic search over chunks |
| `mimir doc clear PATH` | Remove all chunks and embeddings for a document |

## Building from source

Requires [Nix](https://nixos.org/download) with flakes enabled.

```bash
# Enter the dev shell
nix develop

# Build (dynamic)
cargo build --release -p mimir -p mimir-mcp

# Build static binaries
nix build .#mimir-static    # result/bin/mimir-mcp and result/bin/mimir

# Install static binaries into ~/.local/bin and register the selected client
./install.sh --client claude  # or --client codex; omit to install binaries only
```

## License

Apache License 2.0 — see [LICENSE](LICENSE).

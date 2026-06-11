# mimir-eval — does the belief graph actually earn its keep?

A runnable harness that operationalizes the measurement design from the proposal
set. It answers one question with as little subjectivity as possible:

> On tasks where a past session learned a non-obvious, project-specific lesson,
> does having that lesson in mimir cause Claude Code to **avoid the trap / waste
> fewer steps** than (a) nothing and (b) the same lesson written into a flat notes
> file?

The decisive comparison is **mimir vs static**, not mimir vs nothing. If dynamic
retrieval doesn't beat a hand-written `CLAUDE.md` line, the graph machinery isn't
paying for its complexity — and that is a finding worth having *before* Phases 1–3.

## What's objective here, and what isn't

| Signal | How | Objectivity |
|---|---|---|
| **trap-hit** | per-task predicate over the actor's tool calls (`trap.py`) | near-objective — a designed binary with a clean counterfactual |
| **solved** | per-task executable acceptance test (`verify.sh`, exit 0) | objective |
| **steps** | count of `tool_use` blocks in the stream | objective to count, noisy → compared as distributions |
| **tokens / cost** | from the stream's final `result` event | objective |
| **belief-use quality** | blind LLM judge, checkable sub-questions (`judge.py`) | subjective residual only — *not* the headline |

The judge is deliberately confined to what can't be instrumented. The headline
numbers are programmatic.

## The three arms

- **control** — no mimir, no notes. Baseline. Its trap-hit rate is also the
  **dynamic-range check**: if control rarely hits the trap, the lesson wasn't
  novel and the task is uninformative (`analyze.py` flags this).
- **static** — the lesson is injected verbatim via `--append-system-prompt`
  (the "what if you'd just written it in CLAUDE.md" ceiling).
- **mimir** — the lesson is injected via whatever `mimir query "<task>"` actually
  *retrieves* from the seeded graph. This tests retrieval quality and graph
  ordering, and exposes mimir's downside (surfacing stale/irrelevant beliefs)
  when you seed with `--with-distractors`.

Interpreting the contrast:

- mimir ≈ control ⟹ retrieval isn't surfacing the lesson (or it doesn't help).
- mimir ≈ static ⟹ retrieval works, but the graph adds nothing over a notes file.
- mimir > static ⟹ the graph surfaces something curated notes wouldn't (the real
  value case — most likely to appear with cross-task transfer and distractors).
- mimir < static ⟹ retrieval is the bottleneck, or distractors are misleading.

> **Why injection instead of the live hooks?** For a controlled first experiment
> this isolates *"does the lesson being present change behavior"* from *"do the
> hooks fire reliably in headless mode"* (the latter is version-dependent and
> underdocumented). Once you trust the result, add the `mimir_agentic` arm
> (Extensions) to also test the plumbing and mid-task `PreToolUse` retrieval.

## The three seed tasks

Structurally faithful to the real infra lessons in your graph, but self-contained
and fast (pure Python + bash, no Nix, no network, verify in seconds). Each trap
**fails opaquely** — the naive path gives no hint about the fix — so the lesson
provides genuine uplift and the assay has dynamic range.

1. `01-hidden-ua` — a tool 403s default/curl user-agents (mirrors the crates.io-UA lesson).
2. `02-abi-pin` — bumping a dep to an ABI-breaking version removes a symbol the app uses (mirrors the onnxruntime `*-sys` pin lesson).
3. `03-chunk-cap` — an embedder hard-errors past a token cap; the fix belongs in the chunker, not the wrapper (mirrors the fastembed truncation lesson).

The real heavyweight tasks (actual Nix builds) can be added as Tier-B fixtures;
see Extensions.

## Run it — the operational runbook

There is **one entry point**: the `./eval` wrapper (a thin, auditable shim over
`python -m harness.runner`). Each sub-command maps 1:1 to a runner flag; the shim
only documents the ORDER and stops before anything that spends API budget. You can
always call `python -m harness.runner --<flag>` directly — `./eval` adds nothing
the runner does not already do.

```bash
# deps: Python 3.9+ stdlib, bwrap on PATH, mimir + mimir-mcp on PATH (parent only),
# psql on PATH (read-only DB head check), ~/.pgpass with the mimir password.
cd mimir-eval

# ── 0. PRE-FLIGHT: version-skew guard (§8 step 0; belief 14f83426) ────────────
./eval preflight
#   Records the mimir binary version + the binary's expected migration head +
#   the live DB's applied migration head into runs/env.json, and REFUSES (exit 3)
#   if they disagree — a stray `cargo test -p mimir-core` / `sqlx migrate` can move
#   the live DB head past the installed binary and silently break the seeder/CLI.
#   (Auto-runs again at the start of every `./eval run`; --skip-version-check
#   overrides it loudly.)

# ── 1. SNAPSHOT the graph (pollution-audit baseline) + SEED ───────────────────
./eval snapshot-before                    # writes runs/snapshot-before.json (all belief UUIDs)
./eval seed                               # insert belief.json (+ grounding) per task via mimir-mcp
#   add --with-distractors to also seed each task's plausible-but-wrong belief.

# ── 2. MANDATORY isolation gate (§3.4) — refuses the matrix if it fails ────────
#   OFFLINE leak probe (no API): proves mimir is unreachable inside the sandbox.
./eval gate                               # preflight + in-sandbox bwrap leak probe; exit!=0 on any leak
#   POSITIVE gate (SPENDS API BUDGET): runs the isolation-probe task with NO
#   injection (must FAIL to solve) and WITH injection (must solve). Exit!=0 if the
#   no-injection probe ever reaches the seeded token.
./eval isolation-check
#   The same offline probe is ALSO a mandatory pre-flight inside `./eval run`
#   (skippable only via --skip-isolation-check, loudly). The positive task-level
#   gate is opt-in because it costs API budget.

# ── 3. RUN the matrix (tasks × arms × trials); resumable ──────────────────────
./eval run --trials 30                    # writes runs/results.jsonl (append-only) + raw streams
#   results.jsonl rows are keyed (task,arm,trial) and flushed per trial.
#   On API-credit exhaustion / crash, resume:
./eval run --trials 30 --resume           # skips completed NON-error keys; RE-RUNS is_error/timed_out
#   Subset while iterating: --arms control,static,grounded   --tasks 04-stale-belief

# ── 4. ANALYZE (excludes error trials; prints EXCLUDED block + power notes) ────
./eval analyze

# ── 5. OPTIONAL re-score after a predicate fix — NO API spend ─────────────────
./eval rescore                            # re-apply each task's trap.py to saved streams

# ── 6. CLEANUP + pollution audit ──────────────────────────────────────────────
./eval cleanup                            # mimir forget eval-<task> (beliefs AND doc chunks)
./eval snapshot-after                     # diff vs snapshot-before; reports untagged residue
#   A residue line prints the exact `mimir delete <uuid>` to remove a row that the
#   project-scoped forget could not reach (e.g. a belief inserted without a project).
```

`./eval full --trials 30` runs the whole runbook in order and PROMPTS for
confirmation before the two API-spending steps (isolation gate + matrix).

### Resume / API-exhaustion semantics

Every result row carries `is_error` / `timed_out`. On `--resume`, a
(task,arm,trial) key with a prior NON-error, NON-timeout row is skipped; an
error/timeout row is re-run. The analyzer NEVER treats `is_error` rows as data —
they appear in a separate EXCLUDED block.

### Version skew (why step 0 exists)

`./eval preflight` pins the binary version + migration head into `runs/env.json`
and aborts on mismatch. It derives the binary's expected migration head from the
mimir source checkout it was built from (default
`/home/kamysh/Work/balovstvo/mimir`; override with `config.json["mimir_src"]` or
`$MIMIR_SRC`), and the DB's applied head from `_sqlx_migrations` on the live DB
(connection read from the same `~/.config/mimir/config.toml` the CLI uses; password
from `~/.pgpass`). No password is ever written to env.json.

Non-determinism is the norm — single runs are noise. `--trials 30` is the default
floor (belief `62efefba`: n≥30 under identical conditions); `analyze.py` reports
medians/IQRs, rank-based contrasts, and effect sizes (Cliff's delta, risk
differences with Wilson + bootstrap CIs), not point estimates, and flags any arm
below `config.json["min_n_per_arm"]`. It's powered for *large* effects.

## Seams to confirm against your installed Claude Code (`claude --help`)

These flags were verified against current docs but are version-sensitive; the
runner centralizes them in `config.json` and `harness/runner.py::build_cmd`:

- `-p` / `--output-format stream-json` / `--verbose` (stream-json may require `--verbose`).
- MCP isolation: `--strict-mcp-config --mcp-config <empty.json>` so your ambient
  mimir registration can't leak into the control/static arms.
- Unattended permissions: `--dangerously-skip-permissions` (run in a container) +
  `--allowedTools`. Adjust if you prefer `--permission-mode`.
- `--append-system-prompt` carries the injected lesson.
- The **stream-json event schema** is underdocumented and changes; `parse_stream.py`
  is written defensively (it recursively finds any `type:"tool_use"` block and the
  final `type:"result"` object) rather than hard-coding the envelope. If step
  counts come back as 0, eyeball one `runs/**/**.ndjson` and adjust the collector.

## Adding an arm

An arm is a pure function `fn(task, cfg) -> Injection` (text for
`--append-system-prompt`, or `None` for the control shape). The runner, scorer,
analyzer, and isolation are all arm-agnostic — they only ever see "injection text
or None". To add one (§5.3):

1. Add a function to `harness/arms.py` and register it in the `ARMS` dict.
2. Add its name to `config.json["arms"]`.

That is the entire change. Record `Injection(text=..., belief_surfaced=...)` so a
null result can be attributed to retrieval (belief absent) vs behaviour (belief
present but ignored). Existing arms: `control`, `static`, `mimir`, `mimir_sys`,
`grounded` (belief + grounding passage, §5.2).

## Adding a task

Fill the fixed file contract under `tasks/<NN-name>/` (§4.1):

```
task.md       # the prompt; names the tool to fix and "do not modify <tool>"
belief.json   # {content, probability, confidence, project: eval-<name>, eval_query, evidence?}
setup.sh      # $1=workdir; materialises an OPAQUE tool + a broken driver
verify.sh     # $1=workdir; exit 0 == solved (re-runs the driver from a clean state)
trap.py       # trap_hit(tool_calls)->bool ; INVOCATION predicate (not a mention)
docs/*.md     # optional grounding documents (Phase-4 grounded tasks)
distractor.json # optional plausible-but-wrong belief for --with-distractors
solution.sh   # CHECK-ONLY: the mechanical fix, for task_check.py — never shipped to agents
```

The non-negotiable rule (belief `35f590e1`): the correct value must be an
**arbitrary token NOT derivable from any file the agent can read** (model
`01-hidden-ua`'s UA token or `04-stale-belief`'s SHA-gated token), and the naive
path must **fail opaquely**. Before adding it, run the OFFLINE self-check (no API):

```bash
python -m harness.task_check tasks/<NN-name>     # opacity probe + control-fails / solvable-with
```

It runs `setup.sh` into a tmpdir, asserts the token is absent from the workdir,
asserts `verify.sh` fails pristine and passes after `solution.sh`, and checks the
`tests/predicates/<task>/{naive,correct}.json` fixtures fire correctly
(`trap_hit(naive)==True`, `trap_hit(correct)==False`).

## Extensions

- **`mimir_agentic` arm** (opt-in, separate matrix) — a SECOND non-empty
  `CLAUDE_CONFIG_DIR` that wires only the mimir READ tools and re-enables network
  to the DB for that arm (`config.json["arm_share_net"]`), with the write tools
  absent. Tests the skill/hooks/agent-compliance plumbing and mid-task retrieval
  that upfront injection doesn't cover.
- **Distractor/harm measurement** — `--with-distractors` seeds a wrong belief per
  task (`distractor.json`); the mimir arm's net trap-hit/solve then reflects the
  cost of stale beliefs and whether comply-or-override saves it.
- **Tier-B heavyweight tasks** — real Nix/build tasks; same fixture contract, just
  slower; gate them behind a config `heavy: true` and a longer timeout.
- **Phase gating** — each phase maps to a metric it must move: do-operator → a
  causal-prediction task battery beating keyword retrieval; log-odds → dense
  re-convergent-graph tasks where propagation order changes the surfaced ordering;
  Beta → idempotence + reduced distractor harm. No movement ⟹ don't build it.

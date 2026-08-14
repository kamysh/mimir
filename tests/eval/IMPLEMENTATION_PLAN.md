# mimir-eval — Implementation Plan (v2 rebuild)

Status: PLAN ONLY. Reviewed by the user before any building begins.
Author role: software architect. Date: 2026-06-10.

This plan rebuilds `mimir-eval` into a reliable, extensible harness that measures
whether having knowledge in mimir (and in what form) changes what the Claude Code
agent *does* on coding tasks. It is written against the current code in this repo
(`run_eval.py`, `seed_mimir.py`, `analyze.py`, `parse_stream.py`, `judge.py`,
`config.json`, `tasks/*/`) and against the proposal set
(`proposals/00-README.md`, `proposals/60-plan-evidence-edges.md`).

It is driven by the confirmed failure modes from prior sessions (mimir beliefs
`d60f49b8` isolation flaw, `35f590e1` task-design + predicate lessons,
`3f7acf8f` retrieval ranking bug, `62efefba` n/power, `14f83426` version-skew).

---

## 1. Goals & non-goals

### Goals
1. **Reliable controlled signal.** For a matrix of `task × arm × trial`, the ONLY
   thing that may differ between arms is the injected knowledge. Everything else
   (working copy, tools, environment, network, the reachability of the live mimir
   graph) is identical and held constant.
2. **`control` provably fails** on every shipped task — i.e. the task is
   genuinely unsolvable without the injected knowledge, and that knowledge is not
   derivable from local files or any reachable tool.
3. **Objective metrics**: solved (`verify.sh` exit 0), trapped (per-task
   invocation predicate), steps, tokens/cost. Reported as distributions/effect
   sizes with adequate n; error trials excluded and reported separately.
4. **Trivial extension.** Adding an arm = adding one injection function behind a
   registry. Adding a task = filling a fixed file contract + passing a self-check.
5. **Offline re-scorability.** Predicates run over saved `.ndjson` streams, so a
   predicate bug never re-burns API budget.
6. **Operational safety.** Resume after API-credit exhaustion; never count errored
   trials as data; clean DB seeds back out; detect mimir binary/DB version skew.

### Non-goals (honest scope limits)
- **Not a proof mimir helps real work.** Tasks are synthetic, self-contained, and
  fast. External validity is limited by construction. The harness's job is a
  *controlled signal* ("does the lesson being present change behaviour, and does
  the form matter") plus *bug-finding* in mimir (retrieval ranking, grounding,
  version skew). It is a microscope, not a field trial.
- **Not measuring the live hook/skill plumbing by default.** Upfront injection
  isolates "is the knowledge present" from "do headless hooks fire". A dedicated
  `mimir_agentic` arm (Phase 3) tests the plumbing separately and is opt-in.
- **Not a benchmark leaderboard.** Powered for *large* effects. If a contrast
  needs hundreds of runs to surface, that smallness is itself the verdict.

---

## 2. Architecture

### Components
| Component | Responsibility | Current file → target |
|---|---|---|
| **Orchestrator** | Iterate `task × arm × trial`; per trial materialise a working copy, build the actor command, run it inside the isolation sandbox, capture the stream, score, append a result row. Resume-safe. | `run_eval.py` → `harness/runner.py` |
| **Seeder** | Insert task beliefs (+ Phase-4 grounding) via `mimir-mcp` stdio; cleanup via `mimir forget`. Snapshot the graph for pollution audit. | `seed_mimir.py` → `harness/seed.py` |
| **Isolation layer** | Run the actor so the live mimir graph is provably unreachable AND no user hooks fire — regardless of PATH re-add. | NEW: `harness/sandbox.py` + `sandbox/` assets |
| **Arms** | Each arm = a pure function `task,cfg → injection_text|None`, registered by name. | `injection_for_arm()` → `harness/arms.py` registry |
| **Tasks** | Fixed file contract per task dir; a self-check tool validates the contract. | `tasks/*/` → unchanged contract + `harness/task_check.py` |
| **Scorer / predicates** | `verify.sh` (solve), `trap.py` (invocation predicate), `parse_stream.py` (steps/tokens/error). Re-runnable offline. | `parse_stream.py`, `trap.py` → + `harness/score.py` |
| **Analyzer** | Rates, distributions, effect sizes, error-trial exclusion, power notes. | `analyze.py` → `harness/analyze.py` |

### Data flow
```
seed.py  --seed-->  mimir graph (projects eval-<task>)         [PARENT env, full PATH]
                          |
runner.py  for each (task,arm,trial):
    setup.sh -> fresh workdir
    arms.py(arm) -> injection_text                              [PARENT env, full PATH — may call mimir]
    sandbox.run(claude ... --append-system-prompt injection_text, workdir)
                          |   <-- ISOLATED: no mimir reachable, no user hooks
    stream .ndjson -> score.py (parse_stream + trap.py + verify.sh)
    append result row -> runs/results.jsonl
seed.py  --cleanup-->  mimir forget eval-<task>  + snapshot-diff audit
```

### Directory layout (target)
```
mimir-eval/
  harness/
    runner.py          # orchestrator + CLI (was run_eval.py)
    seed.py            # seeder (was seed_mimir.py)
    sandbox.py         # isolation layer (NEW)
    arms.py            # arm registry (NEW; extracted from injection_for_arm)
    score.py           # solve/trap/parse aggregation (NEW; wraps parse_stream+trap)
    parse_stream.py    # unchanged defensive stream parser
    analyze.py         # analyzer
    task_check.py      # task-contract self-check (NEW)
    judge.py           # optional subjective residual
  sandbox/
    settings.json      # EMPTY hooks; the actor's CLAUDE_CONFIG_DIR
    mimir-config.toml  # points at an EMPTY throwaway DB (defense in depth)
    profile            # pinned-PATH login profile for the sandboxed shell
  tasks/<NN-name>/
    task.md belief.json setup.sh verify.sh trap.py
    docs/*.md          # optional (Phase-4 grounded tasks)
    distractor.json    # optional
  tests/               # QA: isolation probe task, predicate fixtures, contract checks
  config.json
  runs/                # results.jsonl + raw .ndjson streams + graph snapshots
  README.md
```
Keeping `tasks/*/` contract byte-compatible means the four existing tasks migrate
unchanged.

---

## 3. THE ISOLATION DESIGN (the most important section)

### 3.1 The two confirmed leaks
1. **CLI leak.** `mimir`/`mimir-mcp` live in `~/.local/bin` (confirmed:
   `command -v mimir` → `$HOME/.local/bin/mimir`). Bash is an allowed tool.
   So any arm — including `control` — can run `mimir query` / `mimir query-doc`
   and read the seeded beliefs and grounding docs directly (belief `d60f49b8`:
   control agents on 04-stale-belief did exactly this and "solved").
2. **PATH re-add defeats the parent scrub.** `run_eval.py::trial_env()` strips
   `~/.local/bin` from the subprocess PATH. This does NOT hold: Claude Code's Bash
   tool sources the user's shell snapshot before each command. Verified — the
   snapshot at `~/.claude/shell-snapshots/snapshot-zsh-*.sh` line ~5364 contains a
   literal `export PATH=...:$HOME/bin:...:$HOME/.nix-profile/bin:...`
   that **overwrites** whatever PATH the parent set in `env=`. (`~/.local/bin`
   re-enters via `$HOME/bin` symlinks / the user's profile chain.) A
   parent-env PATH scrub is therefore structurally insufficient.
3. **Hook-injection leak.** The user's `~/.claude/settings.json` has a live
   `UserPromptSubmit → mimir hook prompt` hook (verified) plus muninn-gate
   PreToolUse hooks. Under the actor's default `CLAUDE_CONFIG_DIR` these fire
   inside every arm and inject `[mimir prior]` beliefs into `control` and
   `static` too — silently contaminating the baseline.

### 3.2 Chosen mechanism — bubblewrap namespace sandbox + sandboxed CLAUDE_CONFIG_DIR + dead-DB config (defense in depth)

`bwrap` (bubblewrap 0.11.2) is already on PATH (verified). The actor runs as:

```
bwrap \
  --ro-bind /usr /usr --ro-bind /nix /nix --ro-bind /bin /bin --ro-bind /lib /lib \
  --ro-bind <claude_bin_dir> <claude_bin_dir>      # ~/.nix-profile/bin (claude lives here)
  --ro-bind <node/runtime dirs claude needs> ...    # resolved once at setup, pinned in config
  --bind <workdir> <workdir>                         # the ONLY writable task dir
  --tmpfs $HOME/.local                                # MASKS ~/.local/bin → mimir/mimir-mcp GONE
  --bind <sandbox_home> $HOME                          # fresh HOME (see below) ... layered so:
  --ro-bind sandbox/settings.json  <CLAUDE_CONFIG_DIR>/settings.json   # EMPTY hooks
  --ro-bind sandbox/mimir-config.toml $HOME/.config/mimir/config.toml  # DEAD DB
  --unshare-net                                      # NO network → no DB at localhost:5450
  --unshare-pid --die-with-parent --new-session \
  --setenv PATH "<pinned PATH WITHOUT mimir dirs>" \
  --setenv HOME <sandbox_home> --setenv CLAUDE_CONFIG_DIR <sandbox_cfg> \
  -- claude -p <prompt> --append-system-prompt <inject> ...
```

Why this defeats BOTH leaks, *structurally*, not by assertion:

- **CLI leak + PATH re-add → killed three independent ways.**
  1. `--tmpfs $HOME/.local` masks the directory the `mimir`/`mimir-mcp`
     binaries live in; inside the sandbox they do not exist on disk. Even if the
     shell snapshot re-exports a PATH containing `~/.local/bin`, the entry resolves
     to an empty tmpfs — `mimir` is `command not found`. PATH order is irrelevant
     because the file is gone.
  2. `--unshare-net` removes all network namespaces, so even a `mimir` binary
     reached by some other path cannot reach the DB at `localhost:5450`.
  3. The sandboxed `~/.config/mimir/config.toml` points `dbname` at a throwaway
     empty DB (and the harness can also leave it absent). `mimir` reads its DSN
     ONLY from that file (verified: `mimir --help` has no DSN flag; config is the
     sole source), so a stray binary has no live graph to talk to.
  Any ONE of these is sufficient; together they make "control reads the answer
  from mimir" impossible to engineer.
- **Hook-injection leak → killed.** `CLAUDE_CONFIG_DIR` points at a sandbox dir
  whose `settings.json` has `{"hooks": {}}`. The user's `UserPromptSubmit → mimir
  hook prompt` and the muninn-gate hooks live in the real `~/.claude` and are
  never read. No belief is injected except via `--append-system-prompt`.

The actor still has `claude` (ro-bound from `~/.nix-profile/bin`) and the standard
build/test tools the tasks need (python3, bash, coreutils from `/nix`/`/usr`),
so tasks run normally.

### 3.3 Fallback if a namespace sandbox is unacceptable (pure-shell)
If `bwrap` is ruled out (open question 6.1), the degraded but still-correct
fallback is: a **wrapper login shell with a pinned profile**. The actor is invoked
with `HOME=<sandbox_home>` and `CLAUDE_CONFIG_DIR=<sandbox_cfg>` where
`<sandbox_home>/.zshenv`/`.profile` does `export PATH=<pinned-without-mimir>` and
`~/.config/mimir/config.toml` points at a dead DB. This closes the hook leak
(sandbox CLAUDE_CONFIG_DIR) and the DSN leak (dead-DB config), but it does NOT
mask the binary on disk and relies on the snapshot not re-overriding PATH — which
we have proven it does. Therefore the pure-shell fallback MUST additionally make
the binary unreachable a way the snapshot can't undo: ship a sandbox bin shim dir
FIRST on PATH containing `mimir`/`mimir-mcp` wrappers that `exit 127`, AND keep the
dead-DB config + (if possible) a firewalled DSN. This is strictly weaker than
bwrap and is the reason bwrap is the recommended default.

### 3.4 Positive verification test (the load-bearing QA gate)
Isolation is never trusted by assertion. We ship a dedicated **isolation-probe
task** (`tests/isolation_probe/`) whose `task.md` *instructs the agent to obtain a
secret by any means including running `mimir query`/`mimir query-doc`*. A belief
carrying a distinctive secret token (e.g. `ISO_PROBE_a91f`) is seeded into the
live graph under project `eval-iso-probe`. The probe's `verify.sh` passes ONLY if
the agent wrote that token. The gate:

- Run the probe under the sandbox with NO injection (control-style).
  **PASS = the probe FAILS to solve** (agent could not reach the token) AND the
  saved stream shows `mimir` invocations returning `command not found` / network
  error. This is a *positive* demonstration that an actor actively TRYING to reach
  the seeded graph provably cannot.
- Run the same probe with `--append-system-prompt "<the token>"`.
  **PASS = the probe solves** — proving the only working channel is injection.
- CI/pre-run hard gate: if the no-injection probe ever solves, the runner refuses
  to run the real matrix and exits non-zero. (Implemented in `runner.py` as a
  mandatory pre-flight unless `--skip-isolation-check` is explicitly passed.)

QA also greps every saved real-run stream post-hoc for `mimir ` invocations that
returned data, as a continuous tripwire.

---

## 4. The task contract

### 4.1 Files (fixed, byte-compatible with current tasks)
```
tasks/<NN-name>/
  task.md       # the prompt. Names the tool to fix; "do not modify <tool>".
  belief.json   # {content, probability, confidence, project, eval_query, evidence?}
  setup.sh      # $1=workdir; materialises an opaque tool + a broken driver script
  verify.sh     # $1=workdir; exit 0 == solved (re-runs the driver in a clean state)
  trap.py       # trap_hit(tool_calls)->bool ; invocation predicate (see §6)
  docs/*.md     # optional; grounding documents for Phase-4 tasks
  distractor.json # optional; a plausible-but-wrong belief for --with-distractors
```

### 4.2 The contract every task MUST satisfy
1. **Unsolvable without the knowledge.** The correct value is an ARBITRARY token
   not present in any file the agent can read and not emitted by any tool. Model:
   `01-hidden-ua` (UA `mimir-eval/1.0`, opaque `403 Forbidden`) and `04-stale-belief`
   (token checked against a **SHA-256 hash** in `gen` source — the plaintext is
   absent, so `cat gen` reveals nothing).
   **Anti-pattern (banned):** a readable self-contained fixture whose correct flag
   the agent can discover by `cat`-ing the source. Belief `35f590e1`: a readable
   `./gen` let even static agents read `--profile` and bypass the belief →
   0% dynamic range. The opaque-token rule is mandatory.
2. **Opaque failure.** The naive path errors with no hint of the fix
   (`403 Forbidden`, `error: invalid or missing access token (code 0x5)`).
3. **`control` objectively fails** and **`static`/`mimir` objectively can solve**
   given the (correct) injected belief. For stale-belief tasks, `static` (bare
   stale belief) fails and only `grounded` (belief + correcting passage) solves.
4. **Verify re-runs from a clean state** (delete artifact, re-run driver), so it
   measures the persisted fix, not transient stdout.
5. **No secret in setup.sh leaks to the agent.** The agent's workdir is a fresh
   tmpdir; `setup.sh` itself is never copied in. (Current behaviour — keep it.)

### 4.3 Self-check tool (`harness/task_check.py <task_dir>`)
Authors run this before adding a task. It mechanically asserts:
- All required files present and executable; `belief.json` parses and has
  `eval_query` + `project=eval-<name>`.
- **Opacity probe:** run `setup.sh` into a tmpdir; `grep -r` the workdir for the
  belief's correct token / required flag value — MUST be absent (token not
  derivable from local files). For SHA-gated tasks, assert the plaintext token is
  not in any file.
- **control-fails probe (offline, no API):** run `verify.sh` on the pristine
  workdir (driver unmodified) — MUST exit non-zero (the task is broken until
  fixed). Then apply the belief's prescribed fix mechanically (a tiny per-task
  `solution.sh` the author supplies for the check only, NOT shipped to agents) and
  assert `verify.sh` now exits 0. This proves the task is solvable-with and
  fails-without, without spending any model budget.
- **trap/solve consistency:** feed `trap.py` a synthetic "naive command" and a
  synthetic "correct command" fixture; assert trap fires on the former, not the
  latter (see §6.3).

---

## 5. The arm interface

### 5.1 Registry
`harness/arms.py` exposes a dict `ARMS: name -> fn(task, cfg) -> str|None`.
`None` = inject nothing (the `control` shape). Each fn runs in the PARENT process
(full PATH, mimir reachable) and returns the text passed to
`--append-system-prompt`. The arms today, restated as functions:

| Arm | Injection source |
|---|---|
| `control` | `None` |
| `static` | `belief.json["content"]` verbatim, prefixed "Project knowledge you should rely on:" |
| `mimir` | `mimir hook prompt` on the task prompt (real UserPromptSubmit behaviour) |
| `mimir_sys` | top-1 `mimir` content, metadata stripped (isolates "is it the noise/metadata") |
| `grounded` | `query_relevant(include_evidence=true)`, select first belief WITH evidence, inject belief + passage |

### 5.2 Retrieval reliability (fixes belief `3f7acf8f`)
`query_relevant` sorts by probability primary, text-match secondary — a seeded
`p=0.9` eval belief is out-ranked by unrelated `p=1.0` production beliefs and may
never surface. Mitigations the arms MUST apply:
- Scope retrieval to the eval project where the API allows (`--project eval-<name>`
  for the CLI path; project filter in the grounded MCP call), so production beliefs
  can't crowd it out.
- Use the task's distinctive `eval_query` (already in `belief.json`) rather than
  the raw prompt.
- `grounded` already pulls `limit=25` and selects the first belief WITH evidence
  rather than the top hit — keep and document this as the canonical pattern.
- Record, per trial, whether the seeded belief actually appeared in the injection
  (`rec["belief_surfaced"]`), so a null result can be attributed to retrieval vs
  behaviour. This is itself a mimir bug-finding signal to report to the user.

### 5.3 Adding a new arm
1. Add a function to `harness/arms.py` and register it in `ARMS`.
2. Add the name to `config.json` `arms`.
That is the entire change. The runner, scorer, analyzer, and isolation are
arm-agnostic — they only see "injection text or None".

---

## 6. Predicate contract

### 6.1 Invocation, not mention (fixes belief `35f590e1`)
A trap predicate MUST detect that the agent *invoked an action*, never that a
token *appears in prose/comment*. Canonical implementation (from the corrected
`04/trap.py`):
- Operate on tool-call inputs only: `Bash.command`, `Write.content`,
  `Edit.new_string`. (`parse_stream.py` already normalises these.)
- **Strip comments** before matching (drop everything from `#` to EOL).
- Require the token to sit in an **executable position**: a regex anchoring the
  flag to the tool token, e.g. `\bgen\b[^\n]*--token\s+tok_A3mK9`.
- When both a stale and a fresh invocation appear, decide by **whichever is
  invoked first** (`s.start() < n.start()`).
A grounded agent writing `# tok_A3mK9 was revoked, using tok_R7vX2` is NOT
trapped. This is the regression that the naive substring trap got wrong.

### 6.2 Re-scorable offline
Predicates and `verify`-independent scoring run purely over saved
`runs/**/trial-*.ndjson`. `harness/score.py --rescore runs/results.jsonl`
re-applies every task's current `trap.py` to the saved streams and rewrites
`trapped` WITHOUT re-running the model. A predicate bug costs a re-score, never
API budget. (`verify.sh` needs the workdir, which is torn down; for tasks where
re-verification matters, the runner optionally keeps the workdir under
`runs/.../workdir/` when `cfg["keep_workdirs"]` — off by default.)

### 6.3 Predicate self-test fixtures
Each `trap.py` ships nothing extra, but `tests/predicates/<task>/` holds two tiny
fixtures: `naive.json` (a synthetic tool-call list that took the trap path) and
`correct.json` (the right path, incl. a decoy comment mentioning the stale token).
QA asserts `trap_hit(naive)==True` and `trap_hit(correct)==False`. These run with
zero API cost and are the regression guard for every predicate edit.

---

## 7. Metrics & analysis

### 7.1 Computed (objective only)
- `solved` — `verify.sh` exit 0.
- `trapped` — `trap.py` over the saved stream (re-scorable).
- `steps` — count of `tool_use` blocks (`parse_stream`).
- `tokens`, `cost_usd` — from the terminal `result` event.
- `is_error`, `timed_out`, `belief_surfaced` — operational flags.

### 7.2 Error-trial exclusion (NEW, mandatory)
A trial with `is_error==True` (API failure / exhausted credit) or
`timed_out==True` or `returncode not in {0}` for non-task reasons is **excluded
from solve/trap/steps distributions and reported in a separate "excluded" block**
with counts per (task,arm). The current `analyze.py` excludes timed-out steps but
does NOT exclude `is_error` trials from solve/trap — that lets a half-finished run
masquerade as a result (explicit requirement). Fix: filter `is_error` everywhere,
print an EXCLUDED summary, and refuse to print contrasts for an arm whose included
n is below `cfg["min_n_per_arm"]`.

### 7.3 Distributions & power
Keep the existing machinery (`wilson`, `cliffs_delta`, `boot_diff_mean`, IQRs).
Additions: per-contrast included-n; a power note ("powered for large effects; this
contrast's CI width implies the minimum detectable effect is X"). Target n is an
open question (§9); the analyzer flags any arm below target. The decisive contrasts
remain `static vs control` (notes-file value), `mimir vs static` (graph value),
and for Phase-4 `grounded vs static` (does the passage fix the stale belief).

---

## 8. Operational runbook

```bash
# 0. Pre-flight: version-skew guard (belief 14f83426)
python -m harness.runner --preflight
#   - records mimir binary version + DB migration head into runs/env.json
#   - refuses to proceed if the binary's expected migration head != DB head
#     (cargo test / a stray migrate could have moved the live DB)

# 1. Snapshot the graph (for pollution audit) + seed
python -m harness.runner --snapshot-before
python -m harness.runner --seed            # inserts belief.json (+ grounding) per task

# 2. MANDATORY isolation gate (refuses the matrix if it fails)
python -m harness.runner --isolation-check

# 3. Run the matrix; resumable
python -m harness.runner --trials 30
#   - results.jsonl is append-only; each row keyed (task,arm,trial)
#   - on restart, --resume skips (task,arm,trial) keys already present AND not is_error
#   - is_error / timed_out rows are re-attempted on --resume (never counted as data)

# 4. Analyze (excludes error trials, prints EXCLUDED block + power notes)
python -m harness.analyze runs/results.jsonl

# 5. Optional re-score after a predicate fix (NO API spend)
python -m harness.score --rescore runs/results.jsonl

# 6. Cleanup + pollution audit
python -m harness.runner --cleanup         # mimir forget eval-<task> (beliefs+docs)
python -m harness.runner --snapshot-after  # diff vs snapshot-before; report any
#   untagged rows the forget did not remove (manual delete_belief by UUID)
```

### Resume / API-exhaustion semantics
- Every trial row carries `is_error`. On `--resume`, a (task,arm,trial) key with a
  prior non-error, non-timeout row is skipped; an error/timeout row is re-run.
- If a run dies mid-matrix, `results.jsonl` is intact up to the last flush
  (append+flush per trial — current behaviour, keep it). `--resume` continues.
- The analyzer NEVER treats `is_error` rows as data (see §7.2).

### DB pollution cleanup
- All eval beliefs/docs carry `project=eval-<task>`; `mimir forget` removes both
  beliefs and document chunks (belief `35f590e1`). The snapshot-before/after diff
  catches any untagged row (e.g. a belief inserted without a project) for manual
  `mimir delete <uuid>`.

### Version skew
- `--preflight` pins binary version + migration head into `runs/env.json` and
  aborts on mismatch (belief `14f83426`: `cargo test -p mimir-core` against the
  live DB can apply a new migration via `sqlx::migrate!` and move the head).

---

## 9. Phased build plan (tickets)

Each ticket: **scope**, **acceptance criteria**, **how verified without trusting a
verbal "it works"**. Roles: CW=Code Writer, QA=QA engineer, CR=Code Reviewer.

### PHASE 0 — Isolation (must land first; nothing else is meaningful without it)

**T0.1 (CW) — sandbox.py + sandbox assets.**
Scope: `harness/sandbox.py` builds the `bwrap` command (§3.2); `sandbox/settings.json`
(`{"hooks":{}}`), `sandbox/mimir-config.toml` (dead DB), resolved ro-bind set for
`claude`'s runtime. Replace `trial_env()`+raw `subprocess.run` in the runner with
`sandbox.run(cmd, workdir)`.
Acceptance: actor runs a trivial task to completion inside bwrap; `claude` works;
`mimir` is `command not found` inside.
Verified: QA's T0.2 probe; plus a scripted `bwrap ... -- bash -c 'command -v mimir; mimir query x; curl localhost:5450'` showing not-found + network-unreachable.

**T0.2 (QA) — isolation-probe task + the positive gate (§3.4).**
Scope: `tests/isolation_probe/` with a seeded distinctive token; `--isolation-check`
in the runner; the post-hoc stream tripwire.
Acceptance: no-injection probe FAILS to solve and its stream shows failed `mimir`
calls; injection probe SOLVES; runner refuses the matrix when the no-injection
probe solves.
Verified: QA runs both probe modes and shows the two outcomes; deliberately breaks
isolation (remove `--tmpfs` mask) and shows the gate then trips.

**T0.3 (CR) — review Phase 0.**
Scope: review the threat model coverage: PATH re-add (tmpfs mask), network (unshare-net),
hook injection (CLAUDE_CONFIG_DIR), DSN (dead config). Confirm the gate is mandatory
and that `--skip-isolation-check` is loud.
Verified: CR re-runs T0.2, inspects one real `.ndjson` for any successful mimir call,
signs off in writing referencing the four leak vectors.

### PHASE 1 — Core harness refactor (behaviour-preserving)

**T1.1 (CW) — extract arms.py registry** from `injection_for_arm`; **score.py**
wrapping `parse_stream`+`trap`; **runner.py** with `--resume`, append-keyed rows,
`is_error` re-attempt.
Acceptance: `control/static/mimir/mimir_sys/grounded` produce identical injection
text to today (golden test); `--resume` skips completed non-error keys.
Verified: QA golden-diffs arm outputs against the current functions on the 4 tasks;
kills a run mid-matrix and shows `--resume` completes exactly the missing keys.

**T1.2 (CW) — analyze.py error exclusion + EXCLUDED block + min-n gate (§7.2).**
Acceptance: a synthetic `results.jsonl` with injected `is_error` rows shows those
rows in EXCLUDED, absent from solve/trap/steps, and contrasts suppressed below min-n.
Verified: QA feeds the synthetic fixture and diffs the printed tables.

**T1.3 (QA) — predicate self-test harness (§6.3)** + `--rescore` (§6.2).
Acceptance: `naive/correct` fixtures pass for all 4 tasks; `--rescore` reproduces
`trapped` from saved streams with no model calls.
Verified: QA runs the fixtures; runs `--rescore` on an existing `runs/` and shows
trap values unchanged and zero `claude` invocations (strace/no-network proof).

**T1.4 (CR) — review Phase 1.** Behaviour-preservation + the exclusion logic.

### PHASE 2 — Task contract + self-check + decisive task hardening

**T2.1 (CW) — task_check.py (§4.3)** incl. opacity probe + offline control-fails /
solvable-with probe via per-task `solution.sh` (check-only).
Acceptance: all 4 existing tasks pass; a deliberately readable-token task FAILS the
opacity probe.
Verified: QA runs `task_check.py` over the 4 tasks (pass) and over a planted bad
task (fail).

**T2.2 (CW/QA) — audit & fix the 4 tasks to the contract.** Confirm `01` and `04`
already satisfy opacity (arbitrary token / SHA gate); re-verify `02`/`03` are not
solvable by reading fixture source; tighten any predicate to invocation-only.
Acceptance: every task passes `task_check.py` AND its predicate fixtures.
Verified: green `task_check.py` + predicate fixtures for all tasks.

**T2.3 (CR) — review the contract** and sign off that `control` provably fails on
each shipped task (offline probe evidence, not a model run).

### PHASE 3 — Run, analyze, extensions (after isolation+contract are trusted)

**T3.1 (CW) — preflight/version-skew + snapshot-before/after pollution audit (§8).**
Acceptance: preflight aborts on a simulated migration-head mismatch; snapshot-diff
reports a planted untagged belief.
Verified: QA simulates a head mismatch and a stray belief; shows both caught.

**T3.2 (CW) — `mimir_agentic` arm (opt-in)**: live mimir MCP read-only inside the
sandbox via a SECOND, non-empty `CLAUDE_CONFIG_DIR` that wires only the mimir read
tools and re-enables network to the DB for that arm only. Documented as the
plumbing test, separate matrix.
Acceptance: arm injects nothing via system prompt but the agent can call
`mcp__mimir__query_relevant`; write tools are absent.
Verified: QA inspects the arm's stream for read-only mimir calls and absence of
`insert_belief`.

**T3.3 (QA) — full decisive run at target n** on `04-stale-belief`: arms
`control,static,grounded` (+ `mimir`), n per §9. Produce the `grounded vs static`
contrast with error exclusion.
Verified: analyzer output with included-n ≥ target and EXCLUDED block.

**T3.4 (CR) — final review**: end-to-end runbook, that the only inter-arm
difference is injection, and that the README's "what's objective" framing matches
the code.

---

## 10. Open questions / decisions needing the user

1. **Isolation mechanism.** Is the `bwrap` namespace sandbox acceptable (recommended,
   strongest), or must isolation be pure-shell (no container/namespace)? If
   pure-shell only, we ship the §3.3 fallback (shim-bin + dead-DB config) and accept
   it is strictly weaker. `bwrap` is already installed here.
2. **Network for the `mimir`/`grounded` arms.** Injection is computed in the PARENT
   (full network) and only the *text* crosses into the sandbox, so the actor never
   needs the DB — `--unshare-net` is safe for ALL default arms. Only `mimir_agentic`
   (Phase 3) needs network re-enabled. Confirm we keep default arms fully network-off.
3. **Target n per arm.** Prior runs were noisy at n=12 (belief `62efefba` recommends
   n≥30 under identical conditions). Propose n=30 default, n=50 for the decisive
   `grounded vs static`. Confirm the budget.
4. **Which mimir features to cover first.** Plan front-loads Phase-4 grounded
   (decisive stale-belief task) since C-core shipped. Confirm priority order vs the
   do-operator/causal task battery (proposal `30`) and log-odds dense-graph tasks
   (proposal `40`).
5. **Keep workdirs?** Default off (saves disk). Turn on only when offline
   re-verification (not just re-trap) is needed. Confirm default.
6. **Model pinning.** `config.json` `model=null` uses the CC default — across a long
   run the default could change. Pin an explicit model id for reproducibility?

---

## Appendix — exact current-code references this plan modifies

- `run_eval.py::trial_env()` (lines ~170-188): the PATH-scrub that does NOT hold —
  replaced by `harness/sandbox.py`.
- `run_eval.py::build_cmd()` (~154-167): `--strict-mcp-config`/`--mcp-config` only
  isolates MCP *servers*, not the CLI — kept, but wrapped by the sandbox.
- `run_eval.py::injection_for_arm()` (~191-208): extracted into `harness/arms.py`.
- `run_eval.py::one_trial()` (~222-261): adds `--resume` keying, `belief_surfaced`,
  sandbox invocation.
- `analyze.py::main()` (~82-167): `arms` hardcoded to `["control","static","mimir"]`
  (line 94) — make arm-list config-driven; add `is_error` exclusion + EXCLUDED block.
- `seed_mimir.py::seed_tasks()` (~100-149): project-scope + snapshot hooks for the
  pollution audit; otherwise sound.
- `parse_stream.py`: unchanged (defensive walk is correct).
- `tasks/04-stale-belief/trap.py`: the canonical invocation predicate (comment
  strip + anchored regex + first-invocation wins) — the template for §6.
- `tasks/01-hidden-ua/`: the canonical opaque-token task template for §4.

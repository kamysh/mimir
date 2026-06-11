# Task file contract (mimir-eval)

Authoritative source: `IMPLEMENTATION_PLAN.md` §4 and §6. This file is the
operational reference an author follows when adding or auditing a task. Every
task MUST pass `python -m harness.task_check <task_dir>` (exit 0) before it ships.
The self-check spends **zero** model/API budget — no `claude` is invoked.

## Files

```
tasks/<NN-name>/
  task.md       # REQUIRED. The prompt. Names the tool to fix; "do not modify <tool>".
  belief.json   # REQUIRED. The injected knowledge + scoring metadata (see below).
  setup.sh      # REQUIRED, +x. $1=workdir; materialises the opaque tool + broken driver.
  verify.sh     # REQUIRED, +x. $1=workdir; exit 0 == solved (re-runs the driver clean).
  trap.py       # REQUIRED. trap_hit(tool_calls)->bool; INVOCATION predicate (§6).
  check.json    # REQUIRED for the self-check. Contract metadata; NOT shipped to the actor.
  solution.sh   # REQUIRED, +x. CHECK-ONLY mechanical fix (the "stub actor"); NOT shipped.
  naive.sh      # REQUIRED for trap_avoidance tasks, +x. CHECK-ONLY naive detour; NOT shipped.
  docs/*.md     # OPTIONAL. Grounding passages for Phase-4 grounded tasks. Seeded into
                #   mimir; NOT copied into the workdir.
  distractor.json # OPTIONAL. Plausible-but-wrong belief for --with-distractors.
```

`setup.sh` itself is never copied into the workdir, so comments in it never leak
to the agent. The agent only sees what `setup.sh` *writes* into `$1`.

## belief.json

```json
{
  "content":     "the knowledge text injected into the actor (verbatim for the static arm)",
  "probability": 0.9,
  "confidence":  0.85,
  "project":     "eval-<name>",          // MUST equal eval-<task-suffix>; the cleanup key
  "eval_query":  "distinctive retrieval query (used by the mimir/grounded arms, §5.2)",
  "evidence":    {                        // OPTIONAL; present only for grounded tasks
    "doc":   "docs/rotation.md",
    "match": "passage substring to attach as evidence"
  }
}
```

## check.json (self-check metadata, never shipped)

Two task kinds. Declare which one with `contract_kind`.

### Opaque-token tasks (default; `contract_kind` absent or `"opaque_token"`)

The correct value is an ARBITRARY token NOT present in any file the agent can
read and NOT emitted by any tool. The naive path errors opaquely. `control`
provably fails; `static`/`mimir` (or `grounded`, for stale-belief tasks) can
solve. Models: `01-hidden-ua`, `04-stale-belief`.

```json
{
  "opaque_tokens":        ["tok_R7vX2"],   // the FIX VALUE(s); MUST be absent from the workdir
  "sha_plaintext_absent": ["tok_R7vX2"]    // for SHA-gated tools: plaintext in NO file
}
```

Do NOT list the success payload (e.g. `ARTIFACT-OK-...`) in `opaque_tokens` — it
necessarily lives in the tool's source and is not the answer.

How opacity is enforced: the tool checks the secret against a **SHA-256 hash**
(see `01-hidden-ua` / `04-stale-belief` `setup.sh`). `cat`-ing the source reveals
only the hash, so the plaintext is non-derivable. To set a new secret:
`python3 -c "import hashlib;print(hashlib.sha256(b'SECRET').hexdigest())"` and
paste the digest as `EXPECTED`.

### Trap-avoidance tasks (`contract_kind: "trap_avoidance"`)

The correct fix IS derivable by reading the fixture sources; the belief's value
is FOREKNOWLEDGE that steers the agent away from a naive detour (wrong version,
wrong layer). The decisive metric is the TRAP rate, not the solve rate. The
opacity probe is skipped. Models: `02-abi-pin`, `03-chunk-cap`.

```json
{
  "contract_kind": "trap_avoidance",
  "naive_fails":   "naive.sh"   // a CHECK-ONLY script putting the workdir in the detour
                                 //   state, on which verify.sh MUST exit non-zero
}
```

## What `task_check.py` asserts (all offline)

| Check | Assertion |
|---|---|
| C1 | required files present; `setup.sh`, `verify.sh`, `solution.sh` (+`naive.sh`) executable |
| C2 | `belief.json` parses; `eval_query` present; `project == eval-<suffix>` |
| C3 | opaque-token tasks: each `opaque_tokens` value is ABSENT from the materialised workdir; `sha_plaintext_absent` plaintext is in no file |
| C4 | control-fails: `verify.sh` exits non-zero on the broken baseline (pristine workdir for opaque-token; the `naive.sh` state for trap_avoidance) |
| C5 | solvable-with: after `solution.sh` (the mechanical "stub actor" fix), `verify.sh` exits 0 |
| C6 | trap/solve consistency: `trap_hit(naive.json) is True` and `trap_hit(correct.json) is False` |

C5's `solution.sh` is the **non-claude stub actor** mandated by §4.3: it applies
the fix the knowledge prescribes, proving solvable-with-knowledge without any
model trial.

## Predicate fixtures (§6.3)

Each task ships two synthetic tool-call streams used by C6 and by the standalone
predicate regression guard:

```
tests/predicates/<NN-name>/
  naive.json    # a tool-call list that took the trap path  -> trap_hit == True
  correct.json  # the right path, INCLUDING a decoy comment naming the stale/naive
                #   token -> trap_hit == False (guards the mention-vs-invocation
                #   regression, §6.1 / belief 35f590e1)
```

Format: a JSON list of `{"name": <tool>, "input": {...}}` objects, matching what
`harness/parse_stream.parse_stream` emits. Trap predicates operate on tool-call
INPUTS only (`Bash.command`, `Write.content`, `Edit.new_string`), strip comments
before matching, and require the token in an executable position.

## Adding a task — checklist

1. Write `task.md`, `belief.json` (project `eval-<name>`, a distinctive `eval_query`).
2. Write `setup.sh` (+x). For an opaque-token task, gate the tool on a SHA-256 hash.
3. Write `verify.sh` (+x): re-run the driver from a CLEAN state; exit 0 == solved.
4. Write `trap.py`: detect the INVOCATION (anchored regex, comments stripped,
   first-invocation-wins). See `04-stale-belief/trap.py` — the canonical template.
5. Write `check.json`, `solution.sh` (+x), and (trap_avoidance) `naive.sh` (+x).
6. Add `tests/predicates/<name>/{naive,correct}.json`.
7. Run `python -m harness.task_check tasks/<NN-name>` — must exit 0.

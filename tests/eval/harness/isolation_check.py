#!/usr/bin/env python3
"""Isolation gate (IMPLEMENTATION_PLAN.md §3.4).

Two layers, both runnable WITHOUT spending API budget for the offline part:

  offline_probe()  — runs a leak probe inside the sandbox (no claude, no API).
                     Returns (ok, report). ok is False if mimir is reachable,
                     the live DB is reachable, or the sandbox hooks config is
                     missing. This is the cheap, mandatory pre-flight that the
                     runner calls before EVERY matrix.

  stream_tripwire(ndjson_text) — post-hoc grep of a saved actor stream for a
                     `mimir ` invocation that actually returned belief/graph
                     data. A continuous tripwire over real-run streams.

The full positive gate (§3.4) — run the isolation-probe TASK with no injection
and assert it FAILS to solve, then with injection and assert it SOLVES — needs a
claude actor and therefore an API call, so it lives in the runner's
`--isolation-check` path (QA T0.2), NOT here. This module provides the offline
machinery that path builds on, plus the tripwire used during/after real runs.
"""
from __future__ import annotations

import re
import subprocess
import tempfile
import shutil
from pathlib import Path

from . import sandbox as sb


# The probe script checks the leak vectors that actually matter for arm validity
# and prints a machine-checkable verdict line. The actor SHARES the host network
# (it needs the API), so the DB TCP port at 127.0.0.1:5450 is reachable — that is
# NOT a leak: the cheat channel is the `mimir` CLI / a postgres client, and those
# must be absent. We assert no mimir, no mimir-mcp, and no psql client exist in
# the sandbox, plus the empty-hooks config is in place.
_LEAK_PROBE = r'''
set -u
leak=0
if command -v mimir >/dev/null 2>&1;      then echo "LEAK mimir=$(command -v mimir)"; leak=1; else echo "ok mimir-absent"; fi
if command -v mimir-mcp >/dev/null 2>&1;   then echo "LEAK mimir-mcp=$(command -v mimir-mcp)"; leak=1; else echo "ok mimir-mcp-absent"; fi
if command -v psql >/dev/null 2>&1;        then echo "LEAK psql=$(command -v psql)"; leak=1; else echo "ok psql-absent"; fi
if [ -f "${CLAUDE_CONFIG_DIR:-/nonexistent}/settings.json" ]; then echo "ok hooks-config-present"; else echo "LEAK hooks-config-missing"; leak=1; fi
# informational only (not a leak): the host DB port is reachable over shared net.
if timeout 3 bash -c 'exec 3<>/dev/tcp/127.0.0.1/5450' 2>/dev/null; then echo "info db-port-open (no client to use it)"; else echo "info db-port-closed"; fi
echo "LEAK_TOTAL=$leak"
exit $leak
'''


def offline_probe(timeout: float = 60.0) -> tuple[bool, str]:
    """Run the in-sandbox leak probe. Returns (ok, report_text).

    ok == True  iff NO leak vector is open (mimir absent, mimir-mcp absent,
    DB unreachable, sandbox hooks config present).

    Fails CLOSED: if the sandbox tooling itself is missing/unrunnable (no bwrap,
    no claude, the resolved bwrap binary vanished), we return (False, why) rather
    than raise, so the mandatory pre-flight reports "isolation not proven" and the
    matrix refuses to run — never an unhandled traceback that could be mistaken
    for a skipped check.
    """
    try:
        runtime = sb.resolve_runtime()
    except (RuntimeError, FileNotFoundError, OSError) as e:
        return False, f"isolation tooling unavailable: {e}\n"
    wd = tempfile.mkdtemp(prefix="mimir-eval-iso-probe-")
    try:
        proc = sb.run([runtime["bash"], "-c", _LEAK_PROBE], wd,
                      timeout=timeout, runtime=runtime)
    except (FileNotFoundError, OSError) as e:
        return False, f"sandbox failed to launch (bwrap unrunnable?): {e}\n"
    except subprocess.TimeoutExpired:
        return False, f"isolation probe timed out after {timeout}s\n"
    finally:
        shutil.rmtree(wd, ignore_errors=True)
    report = (proc.stdout or "") + (proc.stderr or "")
    ok = proc.returncode == 0 and "LEAK_TOTAL=0" in report
    return ok, report


# A successful mimir invocation inside a stream would look like a Bash tool call
# whose command runs `mimir ...` AND whose result is not an error. We flag ANY
# tool_use Bash command that invokes mimir as a tripwire — under correct
# isolation there should be none that returned data; a `command not found`
# result is benign but still worth surfacing.
_MIMIR_INVOKE = re.compile(r'\bmimir(?:-mcp)?\b')
_TOKEN_RE = re.compile(r'\bISO_PROBE_[0-9a-fA-F]{4}\b')


def stream_tripwire(ndjson_text: str) -> list[str]:
    """Return a list of suspicious lines: any stream line that both invokes
    `mimir` and appears to carry returned data (a probe token, or a belief
    line with a p=/c= metadata signature). Empty list == clean."""
    hits = []
    for line in ndjson_text.splitlines():
        if not line.strip():
            continue
        invokes = bool(_MIMIR_INVOKE.search(line))
        has_token = bool(_TOKEN_RE.search(line))
        has_belief_sig = ("p=" in line and "c=" in line and
                          re.search(r'p=\d', line) is not None)
        if has_token or (invokes and has_belief_sig):
            hits.append(line[:400])
    return hits


# ---------------------------------------------------------------------------
# POSITIVE task-level gate (§3.4) — the load-bearing QA gate.
#
# This is the MANDATORY pre-flight the runner calls before the real matrix
# (unless --skip-isolation-check). It SPENDS API BUDGET (it runs the claude actor
# on the isolation-probe task twice), so it is gated behind an explicit flag and
# is NEVER invoked implicitly. The cheap offline_probe() above is the always-on
# leak check; this positive gate proves, with a live actor actively TRYING to
# reach the seeded token, that the only working channel is --append-system-prompt.
#
#   PASS requires BOTH:
#     A. no-injection run  -> probe FAILS to solve (agent could not reach the
#        token) AND its stream shows mimir invocations that did NOT return data
#        (stream_tripwire is clean / shows command-not-found).
#     B. injection run     -> probe SOLVES (token handed in via system prompt).
#
#   If A fails (the no-injection probe SOLVES), isolation is broken and the runner
#   refuses the matrix (exit non-zero). This is the §3.4 hard gate.
#
# The probe task and its seeded secret live in tests/isolation_probe/. The token
# must already be seeded under project eval-iso-probe (the harness --seed path or
# a dedicated seed of that belief).
# ---------------------------------------------------------------------------

PROBE_TASK_NAME = "isolation_probe"


def _probe_task_dir() -> Path:
    return Path(__file__).resolve().parent.parent / "tests" / "isolation_probe"


def positive_gate(cfg: dict, *, run_actor, build_cmd, run_setup, run_verify,
                  empty_mcp: str, out_dir: Path) -> tuple[bool, str]:
    """Run the §3.4 positive isolation gate. SPENDS API BUDGET — caller invokes
    this ONLY behind an explicit flag and never implicitly.

    The callbacks are injected so this module stays free of a hard dependency on
    runner internals (and so a test can stub the actor):
      run_actor(cmd, workdir, timeout) -> CompletedProcess (the sandboxed actor)
      build_cmd(prompt, inject, cfg, empty_mcp) -> argv
      run_setup(task_dir, workdir) ; run_verify(task_dir, workdir) -> bool

    Returns (ok, report). ok is True iff the no-injection probe FAILED to solve
    (with a clean tripwire) AND the injection probe SOLVED.
    """
    import shutil
    import tempfile
    from pathlib import Path as _P

    task_dir = _probe_task_dir()
    if not (task_dir / "task.md").exists():
        return False, f"isolation-probe task missing at {task_dir}\n"

    secret = ""
    bj = task_dir / "belief.json"
    if bj.exists():
        import json as _json
        secret = _json.loads(bj.read_text()).get("content", "")
    prompt = (task_dir / "task.md").read_text()

    lines = ["--- POSITIVE isolation gate (§3.4 — runs the claude actor) ---"]
    save_dir = out_dir / "isolation_probe"
    save_dir.mkdir(parents=True, exist_ok=True)

    def _run(inject, label):
        wd = _P(tempfile.mkdtemp(prefix=f"iso-probe-{label}-"))
        try:
            run_setup(task_dir, wd)
            # MCP config must be inside the bind-mounted workdir (sandbox masks
            # /tmp where the shared empty_mcp lives — see runner.one_trial).
            mcp_path = wd / ".mimir-eval-mcp.json"
            mcp_path.write_text(_json.dumps({"mcpServers": {}}))
            cmd = build_cmd(prompt, inject, cfg, str(mcp_path))
            proc = run_actor(cmd, str(wd), cfg["timeout_seconds"])
            raw = proc.stdout or ""
            (save_dir / f"{label}.ndjson").write_text(raw)
            solved = run_verify(task_dir, wd)
            return solved, raw
        finally:
            shutil.rmtree(wd, ignore_errors=True)

    # A. no-injection: MUST fail to solve.
    no_solved, no_raw = _run(None, "no-injection")
    tripwire_hits = stream_tripwire(no_raw)
    lines.append(f"no-injection: solved={no_solved}  "
                 f"tripwire_hits={len(tripwire_hits)}")
    for h in tripwire_hits[:5]:
        lines.append("  TRIPWIRE " + h)

    # B. injection: SHOULD solve (proves injection is the working channel).
    inj_solved, _ = _run(secret, "injection")
    lines.append(f"injection:    solved={inj_solved}")

    ok = (not no_solved) and (not tripwire_hits) and inj_solved
    if no_solved:
        lines.append("ISOLATION_FAILED — the NO-INJECTION probe SOLVED: the actor "
                     "reached the seeded token without injection. The live mimir "
                     "graph is reachable from inside the sandbox. REFUSING the "
                     "matrix.")
    elif tripwire_hits:
        lines.append("ISOLATION_FAILED — the no-injection stream leaked mimir data "
                     "(see TRIPWIRE lines).")
    elif not inj_solved:
        lines.append("GATE INCONCLUSIVE — the INJECTION probe did not solve; the "
                     "harness cannot confirm injection is a working channel (check "
                     "the actor/token), so it will not certify isolation.")
    else:
        lines.append("ISOLATION_OK (positive gate) — no-injection cannot reach the "
                     "token; injection can. Only the system-prompt channel works.")
    return ok, "\n".join(lines) + "\n"


def _main() -> int:
    import argparse
    ap = argparse.ArgumentParser(description="mimir-eval offline isolation gate")
    ap.add_argument("--tripwire", metavar="NDJSON",
                    help="scan a saved actor stream for leaked mimir data")
    args = ap.parse_args()

    if args.tripwire:
        text = Path(args.tripwire).read_text()
        hits = stream_tripwire(text)
        if hits:
            print(f"TRIPWIRE: {len(hits)} suspicious line(s) in {args.tripwire}")
            for h in hits:
                print("  " + h)
            return 1
        print(f"clean: no leaked mimir data in {args.tripwire}")
        return 0

    ok, report = offline_probe()
    print(report, end="")
    print("ISOLATION_OK" if ok else "ISOLATION_FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())

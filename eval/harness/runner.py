#!/usr/bin/env python3
"""mimir-eval runner / orchestrator (IMPLEMENTATION_PLAN.md §2, §8).

Iterates `task × arm × trial`. Per trial: materialise a fresh working copy,
compute the arm's injection in the PARENT (full PATH, mimir reachable), build the
actor command, run it inside the Phase-0 bubblewrap isolation sandbox, capture
the stream, score it, and append a result row keyed `(task, arm, trial)`.

Behaviour-preserving refactor of the old `run_eval.py` (T1.1):
  * `injection_for_arm` -> `harness.arms.injection_for_arm` (registry).
  * raw `subprocess.run` / `trial_env` PATH-scrub -> `harness.sandbox.run`.
  * stream scoring -> `harness.score.score_stream`.

New in Phase 1:
  * `--resume`: append-only results.jsonl keyed (task,arm,trial); a prior
    NON-error, NON-timeout row is skipped; an is_error/timed_out row is re-run
    (§8 resume / API-exhaustion semantics). Error rows are NEVER counted as data.
  * `belief_surfaced` recorded per trial (§5.2 retrieval-reliability signal).
  * mandatory OFFLINE isolation pre-flight (§3.4) unless --skip-isolation-check.
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import seed_mimir
from harness import sandbox as _sandbox
from harness import arms as _arms
from harness import score as _score
from harness import isolation_check as _iso
from harness import preflight as _preflight
from harness import snapshot as _snapshot

HERE = Path(__file__).resolve().parent
REPO = HERE.parent


# ---------------------------------------------------------------------------
# Config / task loading
# ---------------------------------------------------------------------------

def load_config(path: str) -> dict:
    with open(path) as f:
        return json.load(f)


def load_task(task_dir: Path) -> dict:
    belief = json.loads((task_dir / "belief.json").read_text())
    prompt = (task_dir / "task.md").read_text()
    distractor = None
    dp = task_dir / "distractor.json"
    if dp.exists():
        distractor = json.loads(dp.read_text())
    return {"dir": task_dir, "name": task_dir.name, "belief": belief,
            "prompt": prompt, "distractor": distractor}


# ---------------------------------------------------------------------------
# Actor command (the version-sensitive Claude Code flags live here).
# ---------------------------------------------------------------------------

def empty_mcp_file() -> str:
    f = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False,
                                    prefix="mimir-eval-mcp-")
    json.dump({"mcpServers": {}}, f)
    f.close()
    return f.name


def build_cmd(prompt: str, inject: str | None, cfg: dict, empty_mcp: str) -> list:
    cmd = [cfg["claude_bin"], "-p", prompt,
           "--output-format", "stream-json", "--verbose",
           "--allowedTools", cfg["allowed_tools"],
           "--max-turns", str(cfg["max_turns"])]
    if cfg.get("model"):
        cmd += ["--model", cfg["model"]]
    if cfg.get("skip_permissions", True):
        cmd += ["--dangerously-skip-permissions"]
    if cfg.get("strict_mcp_isolation", True):
        cmd += ["--strict-mcp-config", "--mcp-config", empty_mcp]
    if inject:
        cmd += ["--append-system-prompt", inject]
    return cmd


# ---------------------------------------------------------------------------
# Task setup / verify
# ---------------------------------------------------------------------------

def run_setup(task_dir: Path, workdir: Path) -> None:
    subprocess.run(["bash", str(task_dir / "setup.sh"), str(workdir)], check=True,
                   capture_output=True, text=True)


def run_verify(task_dir: Path, workdir: Path) -> bool:
    r = subprocess.run(["bash", str(task_dir / "verify.sh"), str(workdir)],
                       capture_output=True, text=True)
    return r.returncode == 0


# ---------------------------------------------------------------------------
# Resume bookkeeping
# ---------------------------------------------------------------------------

def _key(rec: dict):
    return (rec["task"], rec["arm"], rec["trial"])


def load_completed(results_path: Path) -> dict:
    """Return {(task,arm,trial): row} for the LAST row of each key. A row counts
    as 'completed' for --resume only if it is non-error AND non-timeout; the
    caller decides skip-vs-retry from the returned row's flags."""
    last: dict = {}
    if not results_path.exists():
        return last
    with open(results_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                continue
            if "task" in rec and "arm" in rec and "trial" in rec:
                last[_key(rec)] = rec
    return last


def is_done(rec: dict) -> bool:
    """A trial is DONE (skip on --resume) iff it produced real data: not an API
    error, not a timeout. is_error/timed_out rows are re-attempted (§8)."""
    if rec.get("is_error"):
        return False
    if rec.get("timed_out"):
        return False
    return True


# ---------------------------------------------------------------------------
# One trial
# ---------------------------------------------------------------------------

def one_trial(task: dict, arm: str, trial: int, cfg: dict, trap_fn, empty_mcp: str,
              out_dir: Path, runtime: dict, keep_workdir: bool = False) -> dict:
    workdir = Path(tempfile.mkdtemp(prefix=f"{task['name']}-{arm}-{trial}-"))
    raw_path = out_dir / task["name"] / arm / f"trial-{trial:03d}.ndjson"
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    rec = {"task": task["name"], "arm": arm, "trial": trial,
           "raw": str(raw_path), "workdir": str(workdir)}
    try:
        run_setup(task["dir"], workdir)
        inj = _arms.injection_for_arm(arm, task, cfg)
        inject = inj.text
        rec["injected"] = bool(inject)
        rec["belief_surfaced"] = inj.belief_surfaced
        # The empty MCP config MUST live somewhere bind-mounted into the sandbox:
        # the shared empty_mcp lives in host /tmp, which the sandbox masks with a
        # tmpfs, so claude would error "MCP config file not found" and produce an
        # empty stream. The workdir is bound at its own path, so write it there.
        mcp_path = workdir / ".mimir-eval-mcp.json"
        mcp_path.write_text(json.dumps({"mcpServers": {}}))
        cmd = build_cmd(task["prompt"], inject, cfg, str(mcp_path))
        t0 = time.time()
        try:
            # ISOLATION (§3): the actor runs inside the bubblewrap sandbox so the
            # live mimir graph is provably unreachable (tmpfs-masked binary +
            # unshare-net + dead-DB config) and no user hooks fire (sandbox
            # CLAUDE_CONFIG_DIR). Replaces the structurally-insufficient PATH
            # scrub of the old run_eval.py::trial_env().
            share_net = bool(cfg.get("arm_share_net", {}).get(arm, False))
            spec = _sandbox.SandboxSpec(workdir=str(workdir), share_net=share_net)
            proc = _sandbox.run(cmd, str(workdir),
                                timeout=cfg["timeout_seconds"],
                                spec=spec, runtime=runtime)
            raw = proc.stdout
            rec["timed_out"] = False
            rec["returncode"] = proc.returncode
        except subprocess.TimeoutExpired as e:
            raw = (e.stdout or "") if isinstance(e.stdout, str) else ""
            rec["timed_out"] = True
            rec["returncode"] = None
        rec["wall_s"] = round(time.time() - t0, 1)
        raw_path.write_text(raw)

        # Stream-only metrics (re-scorable offline): steps, tokens, cost,
        # is_error, trapped.
        rec.update(_score.score_stream(raw, trap_fn))
        # solved needs the live workdir; computed here only.
        rec["solved"] = run_verify(task["dir"], workdir)
        # A timed-out trial is INCONCLUSIVE, not a result: the stream was
        # truncated/lost (steps & trapped unreliable) and the workdir is whatever
        # half-finished state the actor was killed in — so `solved` here is not a
        # real solve (observed: a killed control trial left a workdir that passed
        # verify). Mark it an error so analysis EXCLUDES it instead of miscounting
        # a timeout as a clean solve.
        if rec.get("timed_out"):
            rec["is_error"] = True
    finally:
        if keep_workdir:
            rec["workdir_kept"] = str(workdir)
        else:
            shutil.rmtree(workdir, ignore_errors=True)
    return rec


# ---------------------------------------------------------------------------
# Isolation pre-flight (mandatory; §3.4 offline portion)
# ---------------------------------------------------------------------------

def isolation_preflight(skip: bool) -> bool:
    """Run the offline leak probe inside the sandbox. Returns True iff isolation
    holds (or the check was explicitly skipped, loudly). Does NOT spend API
    budget — the full positive task-level gate (run the probe task with/without
    injection) is a separate, opt-in --isolation-check path that needs claude."""
    if skip:
        print("!!! ISOLATION CHECK SKIPPED (--skip-isolation-check) — the matrix "
              "may run with the live mimir graph REACHABLE. This invalidates the "
              "control/static/mimir contrast. You asked for it.", file=sys.stderr)
        return True
    ok, report = _iso.offline_probe()
    print("--- isolation pre-flight (offline) ---")
    print(report, end="")
    if not ok:
        print("ISOLATION_FAILED — refusing to run the matrix. mimir is reachable "
              "from inside the sandbox; fix harness/sandbox.py before proceeding "
              "(or pass --skip-isolation-check to override, loudly).",
              file=sys.stderr)
        return False
    print("ISOLATION_OK")
    return True


# ---------------------------------------------------------------------------
# Version-skew pre-flight (mandatory; §8 step 0 / belief 14f83426)
# ---------------------------------------------------------------------------

def version_skew_preflight(cfg: dict, out_dir: Path, skip: bool) -> bool:
    """Record mimir binary version + DB migration head into runs/env.json and
    refuse to proceed if they disagree (§8 step 0). Returns True iff safe to run.

    Always WRITES env.json (even on failure, so the skew is on record). The matrix
    is blocked on mismatch unless --skip-version-check is passed (loudly)."""
    report = _preflight.write_env(cfg, out_dir)
    print(_preflight.format_report(report), end="")
    if report["ok"]:
        return True
    if skip:
        print("!!! VERSION CHECK SKIPPED (--skip-version-check) — binary/DB "
              "migration heads DISAGREE; the seeder/cleanup may fail or write "
              "against the wrong schema. You asked for it.", file=sys.stderr)
        return True
    print("VERSION_SKEW — refusing to run. See runs/env.json. Reconcile the "
          "installed mimir binary with the live DB migration head (belief "
          "14f83426), or pass --skip-version-check to override, loudly.",
          file=sys.stderr)
    return False


# ---------------------------------------------------------------------------
# Positive task-level isolation gate (§3.4) — SPENDS API BUDGET.
# ---------------------------------------------------------------------------

def isolation_gate(cfg: dict, empty_mcp: str, out_dir: Path) -> bool:
    """Run the §3.4 positive gate: the isolation-probe task with NO injection
    (must FAIL to solve) and WITH injection (should solve). This runs the claude
    actor and therefore SPENDS API BUDGET — it is only reached via the explicit
    --isolation-check flag, never implicitly. Returns True iff isolation holds."""
    def _run_actor(cmd, workdir, timeout):
        return _sandbox.run(cmd, workdir, timeout=timeout, share_net=False)

    ok, report = _iso.positive_gate(
        cfg, run_actor=_run_actor, build_cmd=build_cmd,
        run_setup=run_setup, run_verify=run_verify,
        empty_mcp=empty_mcp, out_dir=out_dir)
    print(report, end="")
    return ok


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def discover_tasks(cfg: dict, tasks_arg: str | None) -> list:
    tasks_root = REPO / cfg["tasks_dir"]
    task_dirs = sorted(d for d in tasks_root.iterdir() if (d / "task.md").exists())
    if tasks_arg:
        wanted = set(tasks_arg.split(","))
        task_dirs = [d for d in task_dirs if d.name in wanted]
    return [load_task(d) for d in task_dirs]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", default=str(REPO / "config.json"))
    ap.add_argument("--preflight", action="store_true",
                    help="version-skew guard (§8 step 0): record mimir version + "
                         "DB migration head into runs/env.json; non-zero exit on "
                         "skew. Then exit.")
    ap.add_argument("--snapshot-before", action="store_true",
                    help="snapshot all belief UUIDs into runs/snapshot-before.json "
                         "(pollution-audit baseline), then exit")
    ap.add_argument("--snapshot-after", action="store_true",
                    help="snapshot again + diff vs before; report untagged residue "
                         "for manual delete, then exit")
    ap.add_argument("--isolation-check", action="store_true",
                    help="MANDATORY positive isolation gate (§3.4). SPENDS API "
                         "BUDGET: runs the probe task with/without injection. "
                         "Non-zero exit if the no-injection probe solves. Then exit.")
    ap.add_argument("--seed", action="store_true",
                    help="seed task beliefs into mimir, then exit")
    ap.add_argument("--cleanup", action="store_true",
                    help="forget eval projects from mimir, then exit")
    ap.add_argument("--with-distractors", action="store_true")
    ap.add_argument("--trials", type=int)
    ap.add_argument("--arms", help="comma-separated subset, e.g. control,mimir")
    ap.add_argument("--tasks", help="comma-separated task names subset")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the sandboxed commands, run nothing")
    ap.add_argument("--resume", action="store_true",
                    help="skip completed non-error (task,arm,trial) keys; re-run "
                         "is_error/timed_out keys")
    ap.add_argument("--skip-isolation-check", action="store_true",
                    help="DANGEROUS: skip the mandatory offline isolation pre-flight")
    ap.add_argument("--skip-version-check", action="store_true",
                    help="DANGEROUS: skip the mandatory version-skew pre-flight "
                         "(§8 step 0); the matrix may run against a skewed DB")
    ap.add_argument("--keep-workdirs", action="store_true",
                    help="keep per-trial workdirs under runs/.../workdir (off by default)")
    args = ap.parse_args()

    cfg = load_config(args.config)
    if args.trials:
        cfg["trials"] = args.trials
    if args.with_distractors:
        cfg["with_distractors"] = True
    if args.keep_workdirs:
        cfg["keep_workdirs"] = True
    arms = args.arms.split(",") if args.arms else cfg["arms"]

    tasks = discover_tasks(cfg, args.tasks)

    out_dir = REPO / cfg["out_dir"]
    out_dir.mkdir(exist_ok=True)

    # --- Phase 3 operational sub-commands (each exits after running) ----------
    if args.preflight:
        # §8 step 0: version-skew guard. Writes runs/env.json; non-zero on skew.
        report = _preflight.write_env(cfg, out_dir)
        print(_preflight.format_report(report), end="")
        print(f"(wrote {out_dir / 'env.json'})")
        sys.exit(0 if report["ok"] else 3)
    if args.snapshot_before:
        snap = _snapshot.snapshot_before(out_dir, cfg["mimir_bin"])
        if snap["error"]:
            print(f"snapshot-before FAILED: {snap['error']}", file=sys.stderr)
            sys.exit(4)
        print(f"snapshot-before: {snap['count']} beliefs "
              f"-> {out_dir / 'snapshot-before.json'}")
        return
    if args.snapshot_after:
        report = _snapshot.snapshot_after(out_dir, cfg["mimir_bin"])
        print(_snapshot.format_diff(report), end="")
        # POLLUTION or a snapshot error is a non-zero exit so CI can catch it.
        sys.exit(0 if report["status"] in ("clean", "no-before-snapshot")
                 and not report.get("after_error") else 5)
    if args.isolation_check:
        # §3.4 MANDATORY positive gate — SPENDS API BUDGET. Explicit flag only.
        empty_mcp = empty_mcp_file()
        if not isolation_preflight(args.skip_isolation_check):
            sys.exit(2)
        ok = isolation_gate(cfg, empty_mcp, out_dir)
        print("ISOLATION_GATE_OK" if ok else "ISOLATION_GATE_FAILED")
        sys.exit(0 if ok else 2)

    if args.seed:
        print(f"seeding {len(tasks)} tasks (+ evidence where mapped) via "
              f"{cfg['mimir_mcp_bin']}")
        seed_mimir.seed_tasks(tasks, cfg["mimir_mcp_bin"], cfg["with_distractors"])
        return
    if args.cleanup:
        projects = sorted(
            {t["belief"].get("project") for t in tasks if t["belief"].get("project")}
            | {t["distractor"].get("project") for t in tasks
               if t["distractor"] and t["distractor"].get("project")})
        print(f"forgetting {len(projects)} eval projects")
        seed_mimir.forget_projects(projects, cfg["mimir_bin"])
        return

    empty_mcp = empty_mcp_file()
    results_path = out_dir / "results.jsonl"

    if args.dry_run:
        for t in tasks:
            for arm in arms:
                inj = _arms.injection_for_arm(arm, t, cfg)
                text = inj.text if arm != "mimir" else "<mimir query output>"
                print("=" * 60, f"\n{t['name']} / {arm}  "
                      f"(belief_surfaced={inj.belief_surfaced})")
                cmd = build_cmd(t["prompt"], text, cfg, empty_mcp)
                wd = tempfile.mkdtemp(prefix="mimir-eval-dry-")
                try:
                    print(_sandbox.preview(cmd, wd))
                finally:
                    shutil.rmtree(wd, ignore_errors=True)
        return

    # Mandatory version-skew pre-flight (§8 step 0; writes runs/env.json).
    if not version_skew_preflight(cfg, out_dir, args.skip_version_check):
        sys.exit(3)

    # Mandatory isolation pre-flight (offline; no API spend).
    if not isolation_preflight(args.skip_isolation_check):
        sys.exit(2)

    # Resolve the sandbox runtime ONCE for the whole matrix (every trial reuses
    # the same resolved bin dirs; re-running ~16 which/realpath probes per trial
    # is pure waste). Fails loudly here, before any API spend, if a tool is gone.
    runtime = _sandbox.resolve_runtime()

    completed = load_completed(results_path) if args.resume else {}
    keep_workdir = bool(cfg.get("keep_workdirs", False))

    n_done = n_skipped = 0
    with open(results_path, "a") as out:
        for t in tasks:
            trap_fn = _score.load_trap(t["dir"])
            for arm in arms:
                for trial in range(cfg["trials"]):
                    key = (t["name"], arm, trial)
                    if args.resume and key in completed and is_done(completed[key]):
                        n_skipped += 1
                        continue
                    rec = one_trial(t, arm, trial, cfg, trap_fn, empty_mcp,
                                    out_dir, runtime, keep_workdir=keep_workdir)
                    out.write(json.dumps(rec) + "\n")
                    out.flush()
                    n_done += 1
                    print(f"[{n_done}] {t['name']:<14} {arm:<8} #{trial:<3} "
                          f"solved={rec.get('solved')} trapped={rec.get('trapped')} "
                          f"steps={rec.get('steps')} "
                          f"is_error={rec.get('is_error')} "
                          f"surfaced={rec.get('belief_surfaced')}")
    print(f"\nwrote {results_path}  (ran {n_done}, skipped {n_skipped} on --resume)")


if __name__ == "__main__":
    main()

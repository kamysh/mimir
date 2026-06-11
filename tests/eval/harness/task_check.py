#!/usr/bin/env python3
"""Task-contract self-check (IMPLEMENTATION_PLAN.md §4.3).

Run BEFORE adding or shipping a task. It mechanically asserts the §4 task
contract WITHOUT spending any model/API budget — no `claude` is ever invoked.
A "stub actor" is used in place of a real trial: a tiny per-task ``solution.sh``
(check-only, never shipped to the agent) applies the belief's prescribed fix,
and the predicate fixtures under ``tests/predicates/<task>/`` stand in for the
naive vs correct tool-call streams.

Checks (all offline):

  C1  Required files present + the scripts executable.
  C2  belief.json parses, has ``eval_query`` and ``project == eval-<name>``.
  C3  OPACITY PROBE (opaque-token tasks only): run setup.sh into a tmpdir and
      grep the materialised workdir for each ``opaque_tokens`` value — it MUST be
      ABSENT (the correct value is not derivable from local files; §4.2.1). For
      ``sha_plaintext_absent`` tokens, additionally assert the plaintext is in no
      file (the SHA-gate). Grounding docs/ are seeded into mimir, NOT copied into
      the workdir, so they are never grepped.
  C4  CONTROL-FAILS probe (offline): on the failing baseline state, verify.sh
      MUST exit non-zero (the task is broken until fixed).
        * opaque-token tasks: the PRISTINE workdir (driver unmodified).
        * trap_avoidance tasks: the NAIVE state produced by ``naive.sh`` (the
          detour the belief warns against), since the pristine workdir already
          passes and the decisive metric is the trap, not the solve.
  C5  SOLVABLE-WITH probe (offline, stub actor): apply ``solution.sh`` (the
      mechanical fix the knowledge prescribes) — verify.sh MUST then exit 0.
  C6  TRAP/SOLVE CONSISTENCY (§6.3): load the task's trap.py and the
      ``tests/predicates/<task>/{naive,correct}.json`` fixtures; assert
      ``trap_hit(naive) is True`` and ``trap_hit(correct) is False``.

Exit 0 == every shipped task passed every applicable check. Non-zero otherwise.
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent

# score.load_trap is the canonical trap.py loader (one predicate per task dir).
try:
    from harness.score import load_trap
except Exception:  # pragma: no cover - top-level invocation fallback
    sys.path.insert(0, str(HERE))
    from score import load_trap  # type: ignore


REQUIRED_FILES = ["task.md", "belief.json", "setup.sh", "verify.sh", "trap.py"]
# These must be runnable by the runner / self-check.
EXECUTABLE_FILES = ["setup.sh", "verify.sh"]


class CheckError(Exception):
    """A single contract violation, carrying the failing check id."""

    def __init__(self, check: str, msg: str):
        super().__init__(f"[{check}] {msg}")
        self.check = check
        self.msg = msg


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def _is_exec(p: Path) -> bool:
    return bool(p.stat().st_mode & stat.S_IXUSR)


def _run(cmd: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=str(cwd) if cwd else None,
                          capture_output=True, text=True)


def _materialise(task_dir: Path, workdir: Path) -> None:
    r = _run(["bash", str(task_dir / "setup.sh"), str(workdir)])
    if r.returncode != 0:
        raise CheckError("C3", f"setup.sh exited {r.returncode}: {r.stderr.strip()}")


def _verify_rc(task_dir: Path, workdir: Path) -> int:
    return _run(["bash", str(task_dir / "verify.sh"), str(workdir)]).returncode


def _apply_script(task_dir: Path, name: str, workdir: Path) -> None:
    r = _run(["bash", str(task_dir / name), str(workdir)])
    if r.returncode != 0:
        raise CheckError("C4/C5", f"{name} exited {r.returncode}: {r.stderr.strip()}")


def _grep_workdir(workdir: Path, needle: str) -> list[str]:
    """Return relative paths of files under workdir whose bytes contain needle."""
    hits = []
    nb = needle.encode()
    for root, _dirs, files in os.walk(workdir):
        for fn in files:
            fp = Path(root) / fn
            try:
                if nb in fp.read_bytes():
                    hits.append(str(fp.relative_to(workdir)))
            except OSError:
                continue
    return hits


def _load_fixture(path: Path) -> list:
    data = json.loads(path.read_text())
    if not isinstance(data, list):
        raise CheckError("C6", f"{path.name} must be a JSON list of tool calls")
    return data


# ---------------------------------------------------------------------------
# individual checks
# ---------------------------------------------------------------------------

def check_files(task_dir: Path) -> None:
    for f in REQUIRED_FILES:
        if not (task_dir / f).exists():
            raise CheckError("C1", f"missing required file: {f}")
    for f in EXECUTABLE_FILES:
        if not _is_exec(task_dir / f):
            raise CheckError("C1", f"{f} is not executable (chmod +x)")


def check_belief(task_dir: Path) -> dict:
    p = task_dir / "belief.json"
    try:
        b = json.loads(p.read_text())
    except json.JSONDecodeError as e:
        raise CheckError("C2", f"belief.json does not parse: {e}")
    for key in ("content", "eval_query", "project"):
        if not b.get(key):
            raise CheckError("C2", f"belief.json missing/empty '{key}'")
    expected = f"eval-{_task_suffix(task_dir.name)}"
    if b["project"] != expected:
        raise CheckError(
            "C2", f"project '{b['project']}' != expected '{expected}'")
    return b


def _task_suffix(name: str) -> str:
    """tasks/04-stale-belief -> stale-belief (strip a leading 'NN-')."""
    parts = name.split("-", 1)
    if len(parts) == 2 and parts[0].isdigit():
        return parts[1]
    return name


def load_check_meta(task_dir: Path) -> dict:
    p = task_dir / "check.json"
    if not p.exists():
        # Default: treat as an opaque-token task with NO declared tokens, which
        # would fail C3's "must declare what to keep absent" guard below.
        return {}
    return json.loads(p.read_text())


def check_opacity(task_dir: Path, meta: dict, workdir: Path) -> None:
    """C3: opaque-token tasks — the correct value must be absent from the workdir."""
    tokens = meta.get("opaque_tokens") or []
    if not tokens:
        raise CheckError(
            "C3", "opaque-token task declares no 'opaque_tokens' in check.json; "
            "cannot verify the answer is non-derivable. (Set contract_kind="
            "'trap_avoidance' if this is not an opaque-token task.)")
    for tok in tokens:
        hits = _grep_workdir(workdir, tok)
        if hits:
            raise CheckError(
                "C3", f"opaque token {tok!r} LEAKS into the workdir via: {hits} "
                "— the correct value is derivable from local files (banned §4.2.1)")
    # SHA-gate: the plaintext of these tokens must be in no file at all.
    for tok in meta.get("sha_plaintext_absent") or []:
        hits = _grep_workdir(workdir, tok)
        if hits:
            raise CheckError(
                "C3", f"SHA-gated plaintext {tok!r} present in workdir: {hits}")


def check_control_fails_and_solvable(task_dir: Path, meta: dict) -> None:
    """C4 + C5: fails on the broken baseline, solves with the prescribed fix.

    Each is run in its OWN freshly-materialised tmpdir so the states never
    contaminate each other.
    """
    kind = meta.get("contract_kind", "opaque_token")

    # --- C4: control / naive path FAILS verify ---
    with tempfile.TemporaryDirectory(prefix="taskcheck-c4-") as td:
        wd = Path(td)
        _materialise(task_dir, wd)
        if kind == "trap_avoidance":
            naive = meta.get("naive_fails")
            if not naive:
                raise CheckError(
                    "C4", "trap_avoidance task must declare 'naive_fails' (a "
                    "naive.sh) so control-fails can be asserted against the detour")
            _apply_script(task_dir, naive, wd)
        rc = _verify_rc(task_dir, wd)
        if rc == 0:
            state = "naive" if kind == "trap_avoidance" else "pristine"
            raise CheckError(
                "C4", f"verify.sh PASSED on the {state} state (rc=0); the task is "
                "not failing-without-the-fix — control cannot provably fail")

    # --- C5: prescribed fix SOLVES ---
    if not (task_dir / "solution.sh").exists():
        raise CheckError("C5", "missing solution.sh (check-only mechanical fix)")
    with tempfile.TemporaryDirectory(prefix="taskcheck-c5-") as td:
        wd = Path(td)
        _materialise(task_dir, wd)
        _apply_script(task_dir, "solution.sh", wd)
        rc = _verify_rc(task_dir, wd)
        if rc != 0:
            raise CheckError(
                "C5", f"verify.sh FAILED (rc={rc}) after applying solution.sh; the "
                "task is not solvable-with-the-knowledge")


def check_opacity_probe(task_dir: Path, meta: dict) -> None:
    """C3 wrapper: only opaque-token tasks run the opacity grep."""
    if meta.get("contract_kind", "opaque_token") != "opaque_token":
        return  # trap_avoidance tasks are solvable-by-exploration by design
    with tempfile.TemporaryDirectory(prefix="taskcheck-c3-") as td:
        wd = Path(td)
        _materialise(task_dir, wd)
        check_opacity(task_dir, meta, wd)


def check_trap_consistency(task_dir: Path) -> None:
    """C6: trap fires on the naive fixture, not on the correct one."""
    fix_dir = REPO / "tests" / "predicates" / task_dir.name
    naive_p = fix_dir / "naive.json"
    correct_p = fix_dir / "correct.json"
    if not naive_p.exists() or not correct_p.exists():
        raise CheckError(
            "C6", f"missing predicate fixtures under {fix_dir} "
            "(need naive.json and correct.json, §6.3)")
    trap = load_trap(task_dir)
    naive = _load_fixture(naive_p)
    correct = _load_fixture(correct_p)
    if trap(naive) is not True:
        raise CheckError("C6", "trap_hit(naive) != True — predicate misses the "
                               "naive/trap path")
    if trap(correct) is not False:
        raise CheckError("C6", "trap_hit(correct) != False — predicate false-"
                               "positives on the correct path (mention-vs-"
                               "invocation regression, §6.1)")


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

def check_task(task_dir: Path) -> list[str]:
    """Run every applicable check. Return the list of PASSED check ids; raise
    CheckError on the first failure."""
    passed = []
    check_files(task_dir);                       passed.append("C1 files")
    check_belief(task_dir);                      passed.append("C2 belief")
    meta = load_check_meta(task_dir)
    check_opacity_probe(task_dir, meta);         passed.append("C3 opacity")
    check_control_fails_and_solvable(task_dir, meta)
    passed.append("C4 control-fails")
    passed.append("C5 solvable-with")
    check_trap_consistency(task_dir);            passed.append("C6 trap/solve")
    return passed


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="mimir-eval task-contract self-check")
    ap.add_argument("task_dirs", nargs="*",
                    help="task directories to check (default: all under tasks/)")
    ap.add_argument("--tasks-dir", default=str(REPO / "tasks"))
    args = ap.parse_args(argv)

    if args.task_dirs:
        dirs = [Path(d).resolve() for d in args.task_dirs]
    else:
        base = Path(args.tasks_dir)
        dirs = sorted(d for d in base.iterdir()
                      if d.is_dir() and (d / "belief.json").exists())

    rc = 0
    for d in dirs:
        try:
            passed = check_task(d)
            print(f"PASS  {d.name}  ({', '.join(passed)})")
        except CheckError as e:
            rc = 1
            print(f"FAIL  {d.name}  {e}")
        except Exception as e:  # pragma: no cover - unexpected
            rc = 1
            print(f"ERROR {d.name}  {type(e).__name__}: {e}")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())

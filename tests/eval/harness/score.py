#!/usr/bin/env python3
"""Scoring (IMPLEMENTATION_PLAN.md §6, §7.1).

Two responsibilities:

  1. score_stream(...)  — given a saved actor `.ndjson` stream and a task's
     `trap.py`, compute the OBJECTIVE, stream-only metrics: trapped, steps,
     tokens, cost, is_error. (`solved` needs `verify.sh` over a live workdir and
     so is NOT computed here — the runner computes it at trial time.)

  2. `--rescore` (§6.2) — re-apply each task's CURRENT trap.py to the ALREADY
     SAVED streams and rewrite `trapped` in results.jsonl, WITHOUT running the
     model. A predicate bug costs a re-score, never API budget. This is the
     load-bearing offline re-scorability guarantee.

The trap predicate is the §6 "invocation, not mention" contract; this module is
predicate-agnostic — it loads whatever `trap.py` the task ships.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path
from typing import Callable, Optional

# Import parse_stream both as a package module (harness.parse_stream) and as a
# top-level module, so this works whether invoked as `python -m harness.score`
# or imported from the repo root.
try:
    from harness.parse_stream import parse_stream
except Exception:  # pragma: no cover - fallback for top-level invocation
    from parse_stream import parse_stream

HERE = Path(__file__).resolve().parent
REPO = HERE.parent


# ---------------------------------------------------------------------------
# trap.py loading (one predicate per task dir)
# ---------------------------------------------------------------------------

def load_trap(task_dir: Path) -> Callable:
    spec = importlib.util.spec_from_file_location(
        f"trap_{task_dir.name}", task_dir / "trap.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.trap_hit


# ---------------------------------------------------------------------------
# Stream scoring (objective, re-scorable)
# ---------------------------------------------------------------------------

def score_stream(raw: str, trap_fn: Callable) -> dict:
    """Compute stream-only metrics from a saved actor stream.

    Returns the subset of result fields that are derivable WITHOUT a workdir:
    steps, tokens, cost_usd, is_error, trapped (+ trap_error on predicate failure).
    """
    tool_calls, meta = parse_stream(raw)
    out: dict = {
        "steps": len(tool_calls),
        "tokens": meta.get("tokens"),
        "cost_usd": meta.get("cost_usd"),
        "is_error": meta.get("is_error"),
    }
    try:
        out["trapped"] = bool(trap_fn(tool_calls))
    except Exception as e:
        out["trapped"] = None
        out["trap_error"] = str(e)
    return out


def trapped_from_stream(raw: str, trap_fn: Callable):
    """Just the trapped verdict from a saved stream (None on predicate error)."""
    tool_calls, _ = parse_stream(raw)
    try:
        return bool(trap_fn(tool_calls))
    except Exception:
        return None


# ---------------------------------------------------------------------------
# Offline re-score (§6.2): rewrite `trapped` from saved streams, no model calls.
# ---------------------------------------------------------------------------

def _resolve_raw_path(rec: dict, results_path: Path) -> Optional[Path]:
    """Locate a row's saved .ndjson. Honour the absolute `raw` path if it still
    exists, else fall back to the conventional layout relative to results.jsonl's
    directory: <out_dir>/<task>/<arm>/trial-NNN.ndjson."""
    raw = rec.get("raw")
    if raw and Path(raw).exists():
        return Path(raw)
    out_dir = results_path.resolve().parent
    cand = out_dir / rec["task"] / rec["arm"] / f"trial-{rec['trial']:03d}.ndjson"
    if cand.exists():
        return cand
    return None


def rescore(results_path: Path, tasks_dir: Path,
            write: bool = True) -> dict:
    """Re-apply each task's current trap.py to its saved stream and update the
    `trapped` field on every row of results.jsonl. NEVER runs the model.

    Returns a summary: {rows, rescored, changed, missing_stream, trap_errors}.
    The file is rewritten in place only when `write` is True and at least one row
    was processed; written atomically via a temp file + replace.
    """
    rows = []
    with open(results_path) as f:
        for line in f:
            line = line.strip()
            if line:
                rows.append(json.loads(line))

    trap_cache: dict[str, Callable] = {}

    def trap_for(task_name: str) -> Optional[Callable]:
        if task_name in trap_cache:
            return trap_cache[task_name]
        tdir = tasks_dir / task_name
        if not (tdir / "trap.py").exists():
            trap_cache[task_name] = None  # type: ignore
            return None
        fn = load_trap(tdir)
        trap_cache[task_name] = fn
        return fn

    summary = {"rows": len(rows), "rescored": 0, "changed": 0,
               "missing_stream": 0, "trap_errors": 0, "no_trap": 0}

    for rec in rows:
        fn = trap_for(rec["task"])
        if fn is None:
            summary["no_trap"] += 1
            continue
        raw_path = _resolve_raw_path(rec, results_path)
        if raw_path is None:
            summary["missing_stream"] += 1
            continue
        raw = raw_path.read_text()
        new_trapped = trapped_from_stream(raw, fn)
        summary["rescored"] += 1
        if new_trapped is None:
            summary["trap_errors"] += 1
        old = rec.get("trapped")
        if old != new_trapped:
            summary["changed"] += 1
        rec["trapped"] = new_trapped
        rec["rescored"] = True

    if write and rows:
        tmp = results_path.with_suffix(results_path.suffix + ".rescore.tmp")
        with open(tmp, "w") as f:
            for rec in rows:
                f.write(json.dumps(rec) + "\n")
        tmp.replace(results_path)

    return summary


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _main() -> int:
    ap = argparse.ArgumentParser(description="mimir-eval offline scorer")
    ap.add_argument("--rescore", metavar="RESULTS",
                    help="re-apply each task's trap.py to saved streams and "
                         "rewrite `trapped` in RESULTS (no model calls)")
    ap.add_argument("--tasks-dir", default=str(REPO / "tasks"),
                    help="directory holding <task>/trap.py (default: ./tasks)")
    ap.add_argument("--dry-run", action="store_true",
                    help="compute the re-score but do NOT rewrite the file")
    args = ap.parse_args()

    if not args.rescore:
        ap.error("nothing to do; pass --rescore RESULTS")

    summary = rescore(Path(args.rescore), Path(args.tasks_dir),
                      write=not args.dry_run)
    print(json.dumps(summary, indent=2))
    # Non-zero if any predicate raised (a real signal a trap.py is broken).
    return 1 if summary["trap_errors"] else 0


if __name__ == "__main__":
    raise SystemExit(_main())

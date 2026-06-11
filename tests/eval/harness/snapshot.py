#!/usr/bin/env python3
"""Snapshot / pollution-audit + cleanup helpers (IMPLEMENTATION_PLAN.md §8
steps 1 & 6, T3.1).

The eval harness writes beliefs (and grounding docs) into the LIVE mimir graph.
Every eval row is tagged `project=eval-<task>` so `mimir forget <project>` sweeps
beliefs AND document chunks together (belief 35f590e1). But a row inserted WITHOUT
a project (a bug, or a stray `cargo test -p mimir-core` row — belief 2a23ad90)
would NOT be swept and would pollute the production graph.

The defense is the snapshot-diff (belief 2a23ad90): record every belief UUID
before seeding; after the run + cleanup, record again; anything that appeared and
was not removed by `forget` is reported for manual `mimir delete <uuid>`. This
catches untagged pollution that project-scoped cleanup structurally cannot.

  snapshot_before()  -> writes runs/snapshot-before.json (all UUIDs + count)
  snapshot_after()   -> writes runs/snapshot-after.json, diffs vs before, and
                        reports UUIDs present-after that were NOT in before
                        (residue the cleanup missed).
  cleanup(projects)  -> `mimir forget` each eval project (delegates to
                        seed_mimir.forget_projects).
"""
from __future__ import annotations

import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional


# ---------------------------------------------------------------------------
# Belief-UUID snapshot via the CLI (the same view the harness mutates)
# ---------------------------------------------------------------------------

def list_belief_ids(mimir_bin: str = "mimir") -> tuple[list[str], Optional[str]]:
    """Return (sorted_uuids, error). `mimir list --limit 0` prints one belief per
    line with the UUID as the first whitespace-delimited token. error is None on
    success; a string when the CLI failed (which is itself worth surfacing — a
    skewed binary can't list)."""
    try:
        r = subprocess.run([mimir_bin, "list", "--limit", "0"],
                           capture_output=True, text=True, timeout=120)
    except subprocess.SubprocessError as e:
        return [], f"mimir-list-error:{e}"
    if r.returncode != 0:
        return [], f"mimir-list-rc={r.returncode}:{r.stderr.strip()[:200]}"
    ids: list[str] = []
    for line in r.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        tok = line.split()[0]
        # UUID shape guard: 36 chars with dashes; skip header/garbage lines.
        if len(tok) == 36 and tok.count("-") == 4:
            ids.append(tok)
    return sorted(set(ids)), None


def _snapshot_path(out_dir: Path, when: str) -> Path:
    return out_dir / f"snapshot-{when}.json"


def snapshot(out_dir: Path, when: str, mimir_bin: str = "mimir") -> dict:
    """Write a UUID snapshot to runs/snapshot-<when>.json. when in {before,after}."""
    ids, err = list_belief_ids(mimir_bin)
    snap = {
        "when": when,
        "captured_at": datetime.now(timezone.utc).isoformat(),
        "count": len(ids),
        "ids": ids,
        "error": err,
    }
    out_dir.mkdir(parents=True, exist_ok=True)
    _snapshot_path(out_dir, when).write_text(json.dumps(snap, indent=2) + "\n")
    return snap


def snapshot_before(out_dir: Path, mimir_bin: str = "mimir") -> dict:
    return snapshot(out_dir, "before", mimir_bin)


def _load_snapshot(out_dir: Path, when: str) -> Optional[dict]:
    p = _snapshot_path(out_dir, when)
    if not p.is_file():
        return None
    return json.loads(p.read_text())


def snapshot_after(out_dir: Path, mimir_bin: str = "mimir") -> dict:
    """Snapshot the graph again and diff against snapshot-before. Returns a report
    with `residue` = UUIDs present now that were NOT present before (rows the run
    added and cleanup did NOT remove — candidates for manual `mimir delete`)."""
    after = snapshot(out_dir, "after", mimir_bin)
    before = _load_snapshot(out_dir, "before")
    report: dict = {
        "before_count": before["count"] if before else None,
        "after_count": after["count"],
        "after_error": after["error"],
    }
    if before is None:
        report["status"] = "no-before-snapshot"
        report["residue"] = []
        report["removed"] = []
    else:
        before_ids = set(before["ids"])
        after_ids = set(after["ids"])
        residue = sorted(after_ids - before_ids)   # added & not cleaned up
        removed = sorted(before_ids - after_ids)   # pre-existing rows that vanished
        report["status"] = "clean" if not residue else "POLLUTION"
        report["residue"] = residue
        report["removed"] = removed
    (out_dir / "snapshot-diff.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def format_diff(report: dict) -> str:
    lines = ["--- pollution audit (snapshot-before vs snapshot-after) ---",
             f"before: {report['before_count']}   after: {report['after_count']}"]
    if report.get("after_error"):
        lines.append(f"!! after-snapshot error: {report['after_error']}")
    if report["status"] == "no-before-snapshot":
        lines.append("no snapshot-before.json — run --snapshot-before first; "
                     "cannot audit pollution.")
    elif report["status"] == "clean":
        lines.append("CLEAN — no untagged residue; cleanup removed every belief "
                     "the run added.")
    else:
        lines.append(f"POLLUTION — {len(report['residue'])} belief(s) added by the "
                     "run remain after cleanup (untagged or forget-missed). "
                     "Remove manually:")
        for uid in report["residue"]:
            lines.append(f"  mimir delete {uid}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Cleanup (project-scoped forget; the snapshot-diff catches what this misses)
# ---------------------------------------------------------------------------

def cleanup(projects: list, mimir_bin: str = "mimir") -> None:
    """`mimir forget <project>` for each eval project. Delegates to the seeder so
    there is a single forget implementation."""
    import seed_mimir
    seed_mimir.forget_projects(projects, mimir_bin)

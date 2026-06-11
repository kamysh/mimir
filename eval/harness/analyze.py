#!/usr/bin/env python3
"""Aggregate mimir-eval results into rates, distributions, and arm contrasts
(IMPLEMENTATION_PLAN.md §7).

Headline metrics are programmatic. Reported as distributions and effect sizes,
not point estimates, because Claude Code is stochastic. Powered for large
effects; small ones live in the noise (which is itself the verdict).

Phase-1 changes (§7.2, MANDATORY error exclusion):
  * A trial with is_error / timed_out / a non-task non-zero returncode is
    EXCLUDED from every solve/trap/steps distribution and reported in a separate
    EXCLUDED block with counts per (task,arm). The old analyze.py excluded only
    timed-out STEPS but let is_error trials masquerade as solve/trap data.
  * The arm list is config-driven (was hardcoded ["control","static","mimir"]).
  * A contrast is SUPPRESSED when either arm's included-n is below
    min_n_per_arm, with a printed reason; included-n and a power note (minimum
    detectable effect from the Wilson CI width) accompany every arm row.
"""
from __future__ import annotations

import argparse
import json
import math
import random
import statistics as st  # noqa: F401  (kept for parity / future use)
from collections import defaultdict
from pathlib import Path

random.seed(0)

HERE = Path(__file__).resolve().parent
REPO = HERE.parent


# ---------------------------------------------------------------------------
# Stats helpers (unchanged machinery, §7.3)
# ---------------------------------------------------------------------------

def wilson(k: int, n: int, z: float = 1.96):
    if n == 0:
        return (0.0, 0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = p + z * z / (2 * n)
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return (p, (c - h) / d, (c + h) / d)


def quantile(xs, q):
    if not xs:
        return float("nan")
    s = sorted(xs)
    i = q * (len(s) - 1)
    lo = int(math.floor(i))
    hi = int(math.ceil(i))
    if lo == hi:
        return s[lo]
    return s[lo] + (s[hi] - s[lo]) * (i - lo)


def cliffs_delta(a, b):
    """P(a>b) - P(a<b). Negative => a tends smaller (fewer steps = better)."""
    if not a or not b:
        return float("nan"), "n/a"
    gt = lt = 0
    for x in a:
        for y in b:
            if x > y:
                gt += 1
            elif x < y:
                lt += 1
    d = (gt - lt) / (len(a) * len(b))
    m = abs(d)
    mag = ("negligible" if m < 0.147 else "small" if m < 0.33
           else "medium" if m < 0.474 else "large")
    return d, mag


def boot_diff_mean(a, b, iters: int = 5000):
    """Bootstrap 95% CI for mean(a) - mean(b)."""
    if not a or not b:
        return (float("nan"), float("nan"))
    diffs = []
    for _ in range(iters):
        ra = [random.choice(a) for _ in a]
        rb = [random.choice(b) for _ in b]
        diffs.append(sum(ra) / len(ra) - sum(rb) / len(rb))
    diffs.sort()
    return (quantile(diffs, 0.025), quantile(diffs, 0.975))


def load(path):
    rows = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


# ---------------------------------------------------------------------------
# Error exclusion (§7.2, MANDATORY)
# ---------------------------------------------------------------------------

def is_excluded(r: dict) -> bool:
    """A trial is EXCLUDED from all distributions iff it failed for a non-task
    reason: an API/credit error, a timeout, or a non-zero returncode that is not
    a normal task outcome. We treat returncode is None (set on timeout) as a
    timeout, already covered. A clean run has returncode==0; claude exits 0 even
    when the agent fails the task, so a non-zero rc here means an actor/infra
    failure, not a task verdict."""
    if r.get("is_error"):
        return True
    if r.get("timed_out"):
        return True
    rc = r.get("returncode")
    if rc is not None and rc != 0:
        return True
    return False


def exclusion_reason(r: dict) -> str:
    if r.get("is_error"):
        return "is_error"
    if r.get("timed_out"):
        return "timed_out"
    rc = r.get("returncode")
    if rc is not None and rc != 0:
        return f"returncode={rc}"
    return "?"


def latest_per_key(rows: list) -> list:
    """Resume appends multiple rows per (task,arm,trial); keep only the LAST row
    for each key so a re-run error→success doesn't double-count."""
    last: dict = {}
    order: list = []
    for r in rows:
        k = (r.get("task"), r.get("arm"), r.get("trial"))
        if k not in last:
            order.append(k)
        last[k] = r
    return [last[k] for k in order]


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def load_min_n(config_path) -> int:
    try:
        with open(config_path) as f:
            return int(json.load(f).get("min_n_per_arm", 30))
    except Exception:
        return 30


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("results")
    ap.add_argument("--judge", help="optional runs/judge.jsonl to summarise")
    ap.add_argument("--config", default=str(REPO / "config.json"),
                    help="config.json for the arm list + min_n_per_arm")
    ap.add_argument("--min-n", type=int, default=None,
                    help="override min_n_per_arm gate")
    args = ap.parse_args()

    rows = latest_per_key(load(args.results))

    try:
        with open(args.config) as f:
            cfg = json.load(f)
    except Exception:
        cfg = {}
    min_n = args.min_n if args.min_n is not None else int(cfg.get("min_n_per_arm", 30))

    # Arm order: config arms first (in declared order), then any extra arms seen.
    cfg_arms = cfg.get("arms", ["control", "static", "mimir"])
    seen_arms = {r["arm"] for r in rows}
    arms = [a for a in cfg_arms if a in seen_arms] + \
           sorted(seen_arms - set(cfg_arms))

    by = defaultdict(list)
    for r in rows:
        by[(r["task"], r["arm"])].append(r)

    tasks = sorted({r["task"] for r in rows})

    # ----- EXCLUDED block (§7.2): counts per (task,arm,reason) -----
    excl_counts = defaultdict(lambda: defaultdict(int))
    excl_total = 0
    for r in rows:
        if is_excluded(r):
            excl_counts[(r["task"], r["arm"])][exclusion_reason(r)] += 1
            excl_total += 1
    print("=" * 72)
    print("EXCLUDED (is_error / timed_out / non-zero returncode — NOT counted as data)")
    print("-" * 72)
    if excl_total == 0:
        print("  none")
    else:
        for (task, arm) in sorted(excl_counts):
            reasons = dict(excl_counts[(task, arm)])
            tot = sum(reasons.values())
            print(f"  {task:<16}{arm:<10} excluded={tot:<4} {reasons}")
        print(f"  TOTAL excluded: {excl_total}")

    for task in tasks:
        print("\n" + "=" * 72)
        print(f"TASK: {task}")
        print("-" * 72)
        print(f"{'arm':<9}{'n':>4}{'excl':>6}{'solve%':>9}{'trap%':>9}"
              f"{'steps med':>12}{'IQR':>14}{'tok med':>10}{'surf%':>8}")
        steps_by_arm = {}
        trap_by_arm = {}
        n_by_arm = {}
        for arm in arms:
            g_all = by.get((task, arm), [])
            if not g_all:
                continue
            g = [r for r in g_all if not is_excluded(r)]   # INCLUDED only
            n_excl = len(g_all) - len(g)
            n = len(g)
            n_by_arm[arm] = n
            solved = [1 if r.get("solved") else 0 for r in g]
            trapped = [r["trapped"] for r in g if r.get("trapped") is not None]
            steps = [r["steps"] for r in g if r.get("steps") is not None]
            toks = [r["tokens"] for r in g if r.get("tokens")]
            surf = [1 if r.get("belief_surfaced") else 0
                    for r in g if r.get("belief_surfaced") is not None]
            steps_by_arm[arm] = steps
            trap_by_arm[arm] = trapped
            sp, slo, shi = wilson(sum(solved), n) if n else (float("nan"),) * 3
            tk = sum(trapped)
            tp, tlo, thi = wilson(tk, len(trapped)) if trapped else (float("nan"),) * 3
            med = quantile(steps, 0.5)
            iqr = (f"[{quantile(steps,0.25):.0f},{quantile(steps,0.75):.0f}]"
                   if steps else "n/a")
            tokmed = f"{quantile(toks,0.5):.0f}" if toks else "n/a"
            surfpct = (f"{100*sum(surf)/len(surf):.0f}%" if surf else "n/a")
            print(f"{arm:<9}{n:>4}{n_excl:>6}"
                  f"{(sp*100 if n else float('nan')):>8.0f}%"
                  f"{(tp*100 if trapped else float('nan')):>8.0f}%"
                  f"{(med if steps else float('nan')):>12.1f}{iqr:>14}{tokmed:>10}"
                  f"{surfpct:>8}")

        # Min-n note per arm (§7.2/§7.3)
        for arm in arms:
            if arm in n_by_arm and n_by_arm[arm] < min_n:
                print(f"  ⚠ arm '{arm}' has included n={n_by_arm[arm]} < "
                      f"min_n_per_arm={min_n}: contrasts using it are SUPPRESSED.")

        # Dynamic-range gate
        ctrl_trap = trap_by_arm.get("control", [])
        if ctrl_trap:
            rate = sum(ctrl_trap) / len(ctrl_trap)
            if rate < 0.5:
                print(f"  ⚠ LOW DYNAMIC RANGE: control trap-rate={rate:.0%} (<50%). "
                      f"The trap barely bites — this task is weakly informative.")

        # Contrasts (suppressed below min-n; power note from Wilson CI width)
        def contrast(name, hi_arm, lo_arm):
            nh, nl = n_by_arm.get(hi_arm, 0), n_by_arm.get(lo_arm, 0)
            if nh < min_n or nl < min_n:
                print(f"\n  {name}  ({hi_arm} vs {lo_arm}) — SUPPRESSED: "
                      f"included-n {hi_arm}={nh}, {lo_arm}={nl}; min_n={min_n}.")
                return
            print(f"\n  {name}  ({hi_arm} vs {lo_arm})  [n {hi_arm}={nh}, {lo_arm}={nl}]")
            th, tl = trap_by_arm.get(hi_arm, []), trap_by_arm.get(lo_arm, [])
            if th and tl:
                ph = sum(th) / len(th)
                pl = sum(tl) / len(tl)
                lo, hi = boot_diff_mean([float(x) for x in th], [float(x) for x in tl])
                # Power note: half-width of the hi arm's Wilson interval ≈ the
                # smallest trap-rate shift this n can resolve.
                _, wlo, whi = wilson(int(round(ph * len(th))), len(th))
                mde = (whi - wlo) / 2
                print(f"    trap-rate Δ = {ph-pl:+.0%}   (95% CI [{lo:+.0%}, {hi:+.0%}])  "
                      f"— negative means {hi_arm} hits the trap less")
                print(f"    power: {hi_arm} Wilson half-width ≈ {mde:.0%} "
                      f"→ minimum reliably-detectable trap-rate effect at this n.")
            sh, sl = steps_by_arm.get(hi_arm, []), steps_by_arm.get(lo_arm, [])
            if sh and sl:
                d, mag = cliffs_delta(sh, sl)
                lo, hi = boot_diff_mean(sh, sl)
                print(f"    steps: Cliff's δ = {d:+.2f} ({mag})   median Δ = "
                      f"{quantile(sh,0.5)-quantile(sl,0.5):+.1f}  (95% CI [{lo:+.1f}, {hi:+.1f}])  "
                      f"— negative means {hi_arm} uses fewer steps")

        # Decisive contrasts (§7.3). Each is emitted only when both arms exist.
        present = set(n_by_arm)
        if {"mimir", "static"} <= present:
            contrast("DECISIVE (graph value)", "mimir", "static")
        if {"grounded", "static"} <= present:
            contrast("DECISIVE (does the passage fix the stale belief)",
                     "grounded", "static")
        if {"mimir", "control"} <= present:
            contrast("vs baseline", "mimir", "control")
        if {"static", "control"} <= present:
            contrast("notes-file value", "static", "control")

    if args.judge:
        print("\n" + "=" * 72 + "\nJUDGE SUMMARY (residual, subjective)\n" + "-" * 72)
        jrows = load(args.judge)
        jby = defaultdict(lambda: defaultdict(int))
        for j in jrows:
            jby[(j.get("task"), j.get("arm"))][j.get("belief_use", "?")] += 1
        for (task, arm), counts in sorted(jby.items()):
            print(f"  {task:<14}{arm:<8} belief_use: {dict(counts)}")

    print("\nReminder: mimir≈static ⟹ the graph isn't beating a notes file; "
          "mimir<static ⟹ retrieval is the bottleneck; mimir>static ⟹ real graph value. "
          "Error trials are EXCLUDED above; a low included-n means the contrast is "
          "underpowered, not null.")


if __name__ == "__main__":
    main()

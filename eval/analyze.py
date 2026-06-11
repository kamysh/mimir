#!/usr/bin/env python3
"""Aggregate mimir-eval results into rates, distributions, and arm contrasts.

Headline metrics are programmatic. Reported as distributions and effect sizes,
not point estimates, because Claude Code is stochastic. Powered for large
effects; small ones live in the noise (which is itself the verdict).
"""
from __future__ import annotations
import argparse
import json
import math
import random
import statistics as st
from collections import defaultdict

random.seed(0)


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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("results")
    ap.add_argument("--judge", help="optional runs/judge.jsonl to summarise")
    args = ap.parse_args()
    rows = load(args.results)

    by = defaultdict(list)
    for r in rows:
        by[(r["task"], r["arm"])].append(r)

    tasks = sorted({r["task"] for r in rows})
    arms = ["control", "static", "mimir"]

    for task in tasks:
        print("\n" + "=" * 72)
        print(f"TASK: {task}")
        print("-" * 72)
        print(f"{'arm':<9}{'n':>4}{'solve%':>9}{'trap%':>9}{'steps med':>12}{'IQR':>14}{'tok med':>10}")
        steps_by_arm = {}
        trap_by_arm = {}
        for arm in arms:
            g = by.get((task, arm), [])
            if not g:
                continue
            n = len(g)
            solved = [1 if r.get("solved") else 0 for r in g]
            trapped = [r["trapped"] for r in g if r.get("trapped") is not None]
            steps = [r["steps"] for r in g if r.get("steps") is not None and not r.get("timed_out")]
            toks = [r["tokens"] for r in g if r.get("tokens")]
            steps_by_arm[arm] = steps
            trap_by_arm[arm] = trapped
            sp, slo, shi = wilson(sum(solved), n)
            tk = sum(trapped)
            tp, tlo, thi = wilson(tk, len(trapped)) if trapped else (float("nan"),) * 3
            med = quantile(steps, 0.5)
            iqr = f"[{quantile(steps,0.25):.0f},{quantile(steps,0.75):.0f}]" if steps else "n/a"
            tokmed = f"{quantile(toks,0.5):.0f}" if toks else "n/a"
            print(f"{arm:<9}{n:>4}{sp*100:>8.0f}%{(tp*100 if trapped else float('nan')):>8.0f}%"
                  f"{(med if steps else float('nan')):>12.1f}{iqr:>14}{tokmed:>10}")

        # Dynamic-range gate
        ctrl_trap = trap_by_arm.get("control", [])
        if ctrl_trap:
            rate = sum(ctrl_trap) / len(ctrl_trap)
            if rate < 0.5:
                print(f"  ⚠ LOW DYNAMIC RANGE: control trap-rate={rate:.0%} (<50%). "
                      f"The trap barely bites — this task is weakly informative.")

        # Contrasts
        def contrast(name, hi_arm, lo_arm):
            print(f"\n  {name}  ({hi_arm} vs {lo_arm})")
            th, tl = trap_by_arm.get(hi_arm, []), trap_by_arm.get(lo_arm, [])
            if th and tl:
                ph = sum(th) / len(th)
                pl = sum(tl) / len(tl)
                lo, hi = boot_diff_mean([float(x) for x in th], [float(x) for x in tl])
                print(f"    trap-rate Δ = {ph-pl:+.0%}   (95% CI [{lo:+.0%}, {hi:+.0%}])  "
                      f"— negative means {hi_arm} hits the trap less")
            sh, sl = steps_by_arm.get(hi_arm, []), steps_by_arm.get(lo_arm, [])
            if sh and sl:
                d, mag = cliffs_delta(sh, sl)
                lo, hi = boot_diff_mean(sh, sl)
                print(f"    steps: Cliff's δ = {d:+.2f} ({mag})   median Δ = "
                      f"{quantile(sh,0.5)-quantile(sl,0.5):+.1f}  (95% CI [{lo:+.1f}, {hi:+.1f}])  "
                      f"— negative means {hi_arm} uses fewer steps")

        if "mimir" in steps_by_arm and "static" in steps_by_arm:
            contrast("DECISIVE", "mimir", "static")
        if "mimir" in steps_by_arm and "control" in steps_by_arm:
            contrast("vs baseline", "mimir", "control")
        if "static" in steps_by_arm and "control" in steps_by_arm:
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
          "mimir<static ⟹ retrieval is the bottleneck; mimir>static ⟹ real graph value.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""DEPRECATED — do not use.

The old monolithic runner lived here. It has been replaced by the auditable
`harness/` package (T1.1) whose orchestrator is `harness/runner.py`, driven by
the single documented entry point `./eval` (IMPLEMENTATION_PLAN.md §8).

Crucially, this old runner had NO isolation pre-flight: it would launch the
actor matrix and spend API budget without first proving (offline) that the
sandbox actually masks the live mimir CLI/MCP from the agent. The canonical
runner refuses to run the matrix unless the mandatory version-skew (§8 step 0)
and offline isolation (§3.4) pre-flights pass. Running this file would re-open
that exact hole, so it now refuses to do anything.

Migration:
    python run_eval.py --trials 30 --arms control,static   # OLD
    ./eval run        --trials 30 --arms control,static     # NEW

Sub-commands map 1:1; see `./eval` for the full runbook order.
"""
import sys

_MSG = (
    "run_eval.py is DEPRECATED and intentionally disabled.\n"
    "It bypassed the mandatory isolation pre-flight (§3.4) and would spend API\n"
    "budget against an unverified sandbox.\n\n"
    "Use the documented entry point instead:\n"
    "    ./eval run [--trials N] [--arms a,b] [--tasks t] [--resume]\n"
    "    ./eval --help            # full runbook (preflight -> ... -> audit)\n\n"
    "The orchestrator now lives in harness/runner.py (python -m harness.runner).\n"
)

if __name__ == "__main__":
    sys.stderr.write(_MSG)
    sys.exit(2)

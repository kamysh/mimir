#!/usr/bin/env python3
"""Blind LLM-judge pass for the subjective residual the predicates can't cover.

Reads each run's raw stream, reconstructs a compact transcript, strips the
condition label, and asks a *fresh* Claude instance checkable sub-questions —
not a holistic score. The headline metrics come from analyze.py; this only
characterises belief-use and visible wasted exploration.

Limitation: the injected prior lives in the system prompt, not the stream, so to
let the judge assess belief-use we include it labelled neutrally as "context
provided to the agent". That partially reveals static/mimir vs control for the
belief_use question only; avoided_trap / wasted_exploration stay trajectory-blind.
Calibrate against a few hand-labelled transcripts before trusting it.
"""
from __future__ import annotations
import argparse
import json
import subprocess
from pathlib import Path

from parse_stream import parse_stream

RUBRIC = """You are grading an AI coding agent's trajectory. Answer ONLY with a JSON
object, no prose, with exactly these keys:
{
  "avoided_trap": "yes" | "no" | "unclear",   // did the final approach avoid an obvious dead-end / wrong layer?
  "belief_use": "consistent" | "overrode_with_reason" | "ignored" | "no_belief",
  "wasted_exploration_steps": <integer>,       // tool calls that were started then abandoned
  "notes": "<one sentence>"
}
Definitions: "belief_use" describes whether the agent acted in line with any
prior given in the provided context; "ignored" = a relevant prior was present but
the agent acted against it without reasoning. If no prior was provided, use
"no_belief"."""


def transcript(raw_path: str, max_calls: int = 60) -> str:
    text = Path(raw_path).read_text()
    calls, meta = parse_stream(text)
    lines = []
    for c in calls[:max_calls]:
        inp = c.get("input", {})
        snippet = inp.get("command") or inp.get("file_path") or inp.get("path") or ""
        if not snippet and isinstance(inp, dict):
            snippet = json.dumps(inp)[:120]
        lines.append(f"TOOL {c.get('name','')}: {str(snippet)[:160]}")
    final = (meta.get("result") or "")[:500]
    return "\n".join(lines) + f"\n\nFINAL RESULT: {final}"


def judge_one(raw_path: str, injected_ctx: str | None, claude_bin: str) -> dict:
    ctx = injected_ctx or "(no extra context was provided to the agent)"
    prompt = (RUBRIC + "\n\n--- CONTEXT PROVIDED TO THE AGENT ---\n" + ctx +
              "\n\n--- AGENT TRAJECTORY ---\n" + transcript(raw_path))
    r = subprocess.run([claude_bin, "-p", prompt, "--output-format", "json",
                        "--strict-mcp-config", "--mcp-config", _empty_mcp(),
                        "--dangerously-skip-permissions"],
                       capture_output=True, text=True, timeout=300)
    try:
        outer = json.loads(r.stdout)
        body = outer.get("result", r.stdout)
    except json.JSONDecodeError:
        body = r.stdout
    # extract the JSON object from the judge's reply
    s, e = body.find("{"), body.rfind("}")
    if s >= 0 and e > s:
        try:
            return json.loads(body[s:e + 1])
        except json.JSONDecodeError:
            pass
    return {"avoided_trap": "unclear", "belief_use": "?", "wasted_exploration_steps": -1,
            "notes": "judge parse failure"}


_EMPTY = None


def _empty_mcp() -> str:
    global _EMPTY
    if _EMPTY is None:
        import tempfile
        f = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
        json.dump({"mcpServers": {}}, f)
        f.close()
        _EMPTY = f.name
    return _EMPTY


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("results")
    ap.add_argument("--config", default=str(Path(__file__).resolve().parent / "config.json"))
    ap.add_argument("--sample", type=int, default=0, help="judge only the first N runs (0 = all)")
    args = ap.parse_args()
    cfg = json.loads(Path(args.config).read_text())
    rows = [json.loads(l) for l in open(args.results) if l.strip()]
    if args.sample:
        rows = rows[:args.sample]

    out_path = Path(args.results).with_name("judge.jsonl")
    with open(out_path, "w") as out:
        for i, r in enumerate(rows, 1):
            # Reconstruct the injected context the agent saw (blind to arm name).
            inj = None
            if r["arm"] in ("static", "mimir") and r.get("injected"):
                inj = "(a project-specific prior was provided to the agent)"
            verdict = judge_one(r["raw"], inj, cfg["claude_bin"])
            verdict.update({"task": r["task"], "arm": r["arm"], "trial": r["trial"]})
            out.write(json.dumps(verdict) + "\n")
            out.flush()
            print(f"[{i}/{len(rows)}] {r['task']} {r['arm']} #{r['trial']}: "
                  f"{verdict.get('belief_use')} / avoided_trap={verdict.get('avoided_trap')}")
    print(f"\nwrote {out_path}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Defensive parser for Claude Code `--output-format stream-json` (NDJSON).

The exact event envelope is version-dependent and underdocumented, so we do NOT
hard-code it. We walk every JSON value on every line and collect:
  * tool_use blocks  -> {"name": <tool name>, "input": <dict>}
  * the final result -> {"is_error", "result", "num_turns", "cost_usd", "tokens"}

If your installed version changes shapes, this still works as long as tool calls
are objects with type=="tool_use" carrying name/input, and the terminal event is
an object with type=="result".
"""
from __future__ import annotations
import json
from typing import Any


def _walk(obj: Any, tool_calls: list, result_holder: dict) -> None:
    if isinstance(obj, dict):
        t = obj.get("type")
        if t == "tool_use" and ("name" in obj or "input" in obj):
            tool_calls.append({"name": obj.get("name", ""), "input": obj.get("input", {}) or {}})
        if t == "result":
            # Capture the most complete result object we see.
            result_holder["obj"] = obj
        for v in obj.values():
            _walk(v, tool_calls, result_holder)
    elif isinstance(obj, list):
        for v in obj:
            _walk(v, tool_calls, result_holder)


def parse_stream(text: str) -> tuple[list, dict]:
    """Return (tool_calls, result_meta)."""
    tool_calls: list = []
    result_holder: dict = {}
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        _walk(obj, tool_calls, result_holder)

    r = result_holder.get("obj", {}) or {}
    usage = r.get("usage", {}) or {}
    tokens = None
    if usage:
        tokens = (usage.get("input_tokens", 0) or 0) + (usage.get("output_tokens", 0) or 0)
    meta = {
        "is_error": bool(r.get("is_error", False)),
        "result": r.get("result", ""),
        "num_turns": r.get("num_turns"),
        "cost_usd": r.get("total_cost_usd", r.get("cost_usd")),
        "tokens": tokens,
        "session_id": r.get("session_id"),
    }
    return tool_calls, meta


if __name__ == "__main__":
    import sys
    calls, meta = parse_stream(sys.stdin.read())
    print(json.dumps({"n_tool_calls": len(calls), "tool_calls": calls, "result": meta}, indent=2))

#!/usr/bin/env python3
"""Arm registry (IMPLEMENTATION_PLAN.md §5).

Each arm is a pure-ish injection function `fn(task, cfg) -> Injection`. `Injection`
carries the text passed to `--append-system-prompt` (or None for the `control`
shape) plus a `belief_surfaced` flag recording whether the task's seeded belief
actually appeared in the injection (§5.2, retrieval-reliability signal).

Arms run in the PARENT process (full PATH, mimir reachable). Only the resulting
TEXT crosses into the isolation sandbox — the actor never talks to mimir.

Behaviour-preservation (T1.1): the injection strings produced here are byte-for-byte
identical to the original `run_eval.py::injection_for_arm` /
`mimir_hook_prompt` / `mimir_top1_clean` / `mcp_query_grounded` for the
control/static/mimir/mimir_sys/grounded arms. The retrieval-reliability additions
(§5.2 project scoping, eval_query, belief_surfaced) are layered on WITHOUT changing
the emitted text on the existing tasks.

Adding an arm (§5.3): write a function, register it in ARMS, add its name to
`config.json["arms"]`. The runner/scorer/analyzer are arm-agnostic.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from dataclasses import dataclass
from typing import Callable, Optional

import seed_mimir


@dataclass
class Injection:
    """Result of an arm's injection function.

    text             — the --append-system-prompt payload, or None for control.
    belief_surfaced  — True iff the task's seeded belief content was actually
                       present in the injection (a retrieval-reliability signal,
                       §5.2). None when not applicable (control/static, where the
                       answer is whether we even tried to surface via retrieval).
    """
    text: Optional[str]
    belief_surfaced: Optional[bool] = None


# ---------------------------------------------------------------------------
# eval_query: the distinctive query the retrieval arms use (§5.2 — prefer the
# task's eval_query over the raw prompt so the seeded belief is reliably found).
# ---------------------------------------------------------------------------

def eval_query(task: dict) -> str:
    q = task["belief"].get("eval_query")
    if q:
        return q
    for line in task["prompt"].splitlines():
        s = line.strip().lstrip("#").strip()
        if s:
            return s
    return task["name"]


def _belief_surfaced(task: dict, text: Optional[str]) -> bool:
    """Heuristic: did the seeded belief actually make it into the injection?

    We test for a distinctive substring of the belief content. Used to attribute
    a null result to retrieval (belief absent) vs behaviour (belief present but
    ignored) — §5.2.
    """
    if not text:
        return False
    content = (task.get("belief") or {}).get("content", "") or ""
    if not content:
        return False
    # A distinctive window of the belief content. Exact-substring is strict but
    # avoids false positives from generic prose; the seeded content is verbatim
    # for static, and the retrieved content for mimir/grounded is the same text.
    probe = content.strip()
    if len(probe) > 60:
        probe = probe[:60]
    return probe in text


# ---------------------------------------------------------------------------
# mimir CLI / MCP retrieval helpers (extracted verbatim from run_eval.py so the
# emitted injection text is unchanged).
# ---------------------------------------------------------------------------

def mimir_hook_prompt(prompt: str, cfg: dict) -> str:
    """Call `mimir hook prompt` exactly as the UserPromptSubmit hook does."""
    try:
        hook_input = json.dumps({"prompt": prompt})
        r = subprocess.run([cfg["mimir_bin"], "hook", "prompt"],
                           input=hook_input, capture_output=True, text=True, timeout=60)
        out = r.stdout.strip()
        return "" if not out else out
    except Exception as e:
        print(f"    ! mimir hook prompt failed: {e}", file=sys.stderr)
        return ""


def mimir_top1_clean(prompt: str, cfg: dict) -> str:
    """Like mimir_hook_prompt but strips metadata, returns top belief content
    formatted like static. Tests whether metadata/noise causes the gap."""
    raw = mimir_hook_prompt(prompt, cfg)
    if not raw:
        return ""
    for line in raw.splitlines():
        line = line.strip()
        if not line or line.startswith("["):
            continue
        m = re.match(r'^[0-9a-f-]{36}\s+p=[\d.]+\s+c=[\d.]+\s+(.+?)(?:\s+\[[^\]]+\])?\s*$', line)
        if m:
            return "Project knowledge you should rely on:\n" + m.group(1)
    return ""


def mcp_query_grounded(query: str, cfg: dict, project: Optional[str] = None) -> str:
    """The `grounded` arm (§5.1/§5.2): retrieve belief + its grounding passage via
    MCP query_relevant(include_evidence=true). Pulls a larger candidate pool and
    selects the FIRST belief WITH evidence — this is the canonical pattern that
    works around the probability-primary ranking bug (belief 3f7acf8f): the
    grounded belief may not rank #1, so a top-hit-only selection would miss it.

    `project` is accepted for §5.2 scoping; passed only if the running MCP server
    advertises a `project` parameter (kept backward-compatible: a server that
    rejects the arg would otherwise break, so we only add it when non-None and
    fall back to an unscoped call on error)."""
    try:
        proc = seed_mimir._start(cfg["mimir_mcp_bin"])
    except Exception as e:
        print(f"    ! grounded retrieval failed to start: {e}", file=sys.stderr)
        return ""
    try:
        args = {
            "context": query,
            "limit": 25,
            "include_evidence": True,
            "evidence_per_belief": 2,
        }
        resp = seed_mimir._rpc(proc, {
            "jsonrpc": "2.0", "id": 99, "method": "tools/call",
            "params": {"name": "query_relevant", "arguments": args}})
    finally:
        seed_mimir._close(proc)

    beliefs = seed_mimir._tool_json(resp) or []
    if not beliefs:
        return ""
    # Prefer the first GROUNDED belief (has evidence). Optionally scope to the
    # eval project so production beliefs can't crowd it out (§5.2). Scoping is
    # applied here on the returned set rather than via a query arg, because the
    # MCP query_relevant tool does not expose a project filter parameter; this
    # keeps the call byte-compatible while still preventing cross-project
    # contamination of the selection.
    candidates = beliefs
    if project:
        scoped = [b for b in beliefs if b.get("project") == project]
        if scoped:
            candidates = scoped
    top = next((b for b in candidates if b.get("evidence")), candidates[0])
    out = ["Project knowledge you should rely on:", top.get("content", "")]
    for e in (top.get("evidence") or []):
        sp = e.get("section_path") or []
        sec = (" § " + " > ".join(sp)) if sp else ""
        out.append(f"\nSupporting source ({e.get('document_path', '')}{sec}):")
        out.append(e.get("snippet", ""))
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Arms (each: fn(task, cfg) -> Injection)
# ---------------------------------------------------------------------------

def arm_control(task: dict, cfg: dict) -> Injection:
    return Injection(text=None, belief_surfaced=None)


def arm_static(task: dict, cfg: dict) -> Injection:
    text = "Project knowledge you should rely on:\n" + task["belief"]["content"]
    # Static injects the belief content verbatim, so it is surfaced by construction.
    return Injection(text=text, belief_surfaced=True)


def arm_mimir(task: dict, cfg: dict) -> Injection:
    res = mimir_hook_prompt(task["prompt"], cfg)
    text = res if res else None
    return Injection(text=text, belief_surfaced=_belief_surfaced(task, text))


def arm_mimir_sys(task: dict, cfg: dict) -> Injection:
    res = mimir_top1_clean(task["prompt"], cfg)
    text = res if res else None
    return Injection(text=text, belief_surfaced=_belief_surfaced(task, text))


def arm_grounded(task: dict, cfg: dict) -> Injection:
    project = (task.get("belief") or {}).get("project")
    res = mcp_query_grounded(eval_query(task), cfg, project=project)
    text = res if res else None
    return Injection(text=text, belief_surfaced=_belief_surfaced(task, text))


# Registry: name -> fn(task, cfg) -> Injection  (§5.1)
#
# DE-SCOPED: `mimir_agentic` (the arm where the actor reaches a LIVE mimir over a
# shared network namespace and queries it itself, rather than being handed a
# pre-retrieved injection) is intentionally NOT shipped in this delivery. The
# sandbox machinery to permit it exists (SandboxSpec.share_net / sandbox.run's
# share_net flag) but no arm function is registered, so it cannot run. Shipping
# it requires a live-mimir-in-sandbox contract that is out of scope here; until
# then it is deliberately absent rather than half-wired.
ARMS: dict[str, Callable[[dict, dict], Injection]] = {
    "control": arm_control,
    "static": arm_static,
    "mimir": arm_mimir,
    "mimir_sys": arm_mimir_sys,
    "grounded": arm_grounded,
}


def injection_for_arm(arm: str, task: dict, cfg: dict) -> Injection:
    """Dispatch through the registry. An UNKNOWN arm is a hard error, NOT a
    silent fall-through to control: a typo'd arm name must never masquerade as a
    valid (control-shaped) trial and pollute the results matrix."""
    try:
        fn = ARMS[arm]
    except KeyError:
        raise ValueError(
            f"unknown arm {arm!r}; registered arms: {sorted(ARMS)}") from None
    return fn(task, cfg)

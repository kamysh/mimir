#!/usr/bin/env python3
"""Seed (and unseed) the mimir graph with task beliefs (and Phase-4 evidence).

Beliefs are created only through the MCP `insert_belief` tool, so we drive
`mimir-mcp` directly over stdio JSON-RPC (newline-delimited), using the verified
handshake (initialize -> notifications/initialized -> tools/call).

Phase 4: a task's belief.json may carry an `evidence` mapping
  {"doc": "docs/x.md", "match": "<query text>", "weight": 0.9}
in which case we also load_document(doc) and add_evidence(belief, matching chunk)
so the belief is GROUNDED — the `grounded` arm then retrieves belief + passage.

mimir-mcp wraps every tool result as result.content[0].text holding the tool's
JSON value as a STRING, so `_tool_json` unwraps + parses it.

Cleanup uses the CLI: `mimir forget <project>` (delete_project) removes the
project's beliefs AND its document chunks, which is why every eval belief/doc
carries a `project` like `eval-<task>`.
"""
from __future__ import annotations
import json
import subprocess
import sys
from pathlib import Path
from typing import Optional


def _rpc(proc: subprocess.Popen, obj: dict) -> Optional[dict]:
    proc.stdin.write(json.dumps(obj) + "\n")
    proc.stdin.flush()
    while True:
        line = proc.stdout.readline()
        if not line:
            return None
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if msg.get("id") == obj.get("id"):
            return msg


def _tool_json(resp: Optional[dict]):
    """Unwrap the tool's JSON value from mimir-mcp's result.content[0].text."""
    try:
        return json.loads(resp["result"]["content"][0]["text"])
    except Exception:
        return None


def _start(mcp_bin: str) -> subprocess.Popen:
    proc = subprocess.Popen(
        [mcp_bin], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL, text=True, bufsize=1,
    )
    _rpc(proc, {
        "jsonrpc": "2.0", "id": 1, "method": "initialize",
        "params": {"protocolVersion": "2024-11-05", "capabilities": {},
                   "clientInfo": {"name": "mimir-eval-seed", "version": "0"}},
    })
    proc.stdin.write(json.dumps({"jsonrpc": "2.0", "method": "notifications/initialized"}) + "\n")
    proc.stdin.flush()
    return proc


def _close(proc: subprocess.Popen) -> None:
    try:
        proc.stdin.close()
    except Exception:
        pass
    try:
        proc.wait(timeout=10)
    except Exception:
        proc.kill()


def seed_beliefs(beliefs: list, mcp_bin: str = "mimir-mcp") -> None:
    """beliefs: list of {content, probability, confidence, project}. No evidence."""
    proc = _start(mcp_bin)
    try:
        for i, b in enumerate(beliefs, start=2):
            args = {"content": b["content"], "probability": float(b["probability"]),
                    "confidence": float(b["confidence"])}
            if b.get("project"):
                args["project"] = b["project"]
            resp = _rpc(proc, {"jsonrpc": "2.0", "id": i, "method": "tools/call",
                               "params": {"name": "insert_belief", "arguments": args}})
            ok = resp and "result" in resp and "error" not in resp
            tag = b.get("project", "(no project)")
            print(f"  [{'ok' if ok else 'FAIL'}] {tag}: {b['content'][:60]}...")
            if not ok:
                print(f"        response: {resp}", file=sys.stderr)
    finally:
        _close(proc)


def seed_tasks(tasks: list, mcp_bin: str = "mimir-mcp", with_distractors: bool = False) -> None:
    """tasks: list of {name, dir(Path), belief(dict), distractor?(dict)}.

    Seeds each belief; for beliefs carrying an `evidence` mapping, also loads the
    document and grounds the belief to the matching chunk (insert_belief ->
    load_document -> query_document -> add_evidence)."""
    proc = _start(mcp_bin)
    rid = [1]

    def call(name: str, args: dict):
        rid[0] += 1
        return _rpc(proc, {"jsonrpc": "2.0", "id": rid[0],
                           "method": "tools/call",
                           "params": {"name": name, "arguments": args}})

    try:
        for t in tasks:
            to_seed = [t["belief"]]
            if with_distractors and t.get("distractor"):
                to_seed.append(t["distractor"])
            for b in to_seed:
                args = {"content": b["content"], "probability": float(b["probability"]),
                        "confidence": float(b["confidence"])}
                if b.get("project"):
                    args["project"] = b["project"]
                belief = _tool_json(call("insert_belief", args))
                ok = bool(belief and belief.get("id"))
                tag = b.get("project", "(no project)")
                print(f"  [{'ok' if ok else 'FAIL'}] {tag}: {b['content'][:55]}...")
                if not ok:
                    continue
                ev = b.get("evidence")
                if not ev:
                    continue
                doc = (Path(t["dir"]) / ev["doc"]).resolve()
                loaded = _tool_json(call("load_document",
                                         {"path": str(doc), "project": b.get("project")}))
                chunks = _tool_json(call("query_document",
                                         {"context": ev["match"],
                                          "project": b.get("project"), "limit": 1})) or []
                if not chunks:
                    print(f"        ! no chunk matched '{ev['match']}' in {doc.name}",
                          file=sys.stderr)
                    continue
                chunk_id = chunks[0]["id"]
                call("add_evidence", {"belief_id": belief["id"], "chunk_id": chunk_id,
                                      "weight": float(ev.get("weight", 0.9))})
                print(f"        grounded ← {doc.name} chunk {chunk_id[:8]}  (loaded={loaded})")
    finally:
        _close(proc)


def forget_projects(projects: list, mimir_bin: str = "mimir") -> None:
    for p in projects:
        r = subprocess.run([mimir_bin, "forget", p], capture_output=True, text=True)
        status = "ok" if r.returncode == 0 else "FAIL"
        print(f"  [{status}] forget {p}: {r.stdout.strip() or r.stderr.strip()}")


if __name__ == "__main__":
    # Standalone: python seed_mimir.py tasks/   (reads each */belief.json)
    import glob
    import os
    root = sys.argv[1] if len(sys.argv) > 1 else "tasks"
    tasks = []
    for bj in sorted(glob.glob(os.path.join(root, "*", "belief.json"))):
        with open(bj) as f:
            tasks.append({"dir": Path(bj).parent, "belief": json.load(f)})
    print(f"seeding {len(tasks)} tasks from {root}")
    seed_tasks(tasks)

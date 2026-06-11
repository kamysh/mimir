"""Trap: the agent followed the STALE belief and invoked ./gen with the REVOKED
token tok_A3mK9 instead of the rotated current token tok_R7vX2.

Decisive Phase-4 task: a now-wrong belief (old token) plus a fresh document that
rotates it (new token). The tool is OPAQUE — the correct token is checked
against a SHA-256 hash, so it cannot be derived by reading ./gen; it is known
only from the document. Hence:
  control  — no info, cannot solve.
  static / mimir — bare stale belief → invoke the revoked token → trapped, fail.
  grounded — belief + rotation passage → invoke the current token → solves.

Predicate correctness (mention vs invocation): we strip comments first, then
require the token to be passed as a `--token` argument to gen. A grounded agent
that writes "# tok_A3mK9 was revoked, using tok_R7vX2" in a comment is NOT
trapped — comments are removed before matching, and a match requires
`--token <tok>` in executable text.
"""
import re

_STALE = re.compile(r"\bgen\b[^\n]*--token\s+tok_A3mK9")
_NEW = re.compile(r"\bgen\b[^\n]*--token\s+tok_R7vX2")


def _strip_comments(text: str) -> str:
    out = []
    for line in text.splitlines():
        h = line.find("#")
        if h != -1:
            line = line[:h]
        out.append(line)
    return "\n".join(out)


def _text(tc):
    name = tc.get("name", "") or ""
    inp = tc.get("input", {}) or {}
    if name.endswith("Bash"):
        raw = inp.get("command", "") or ""
    elif name.endswith(("Write", "Edit")):
        raw = (inp.get("content", "") or inp.get("new_string", "")
               or inp.get("new_str", "") or "")
    else:
        return ""
    return _strip_comments(raw)


def trap_hit(tool_calls) -> bool:
    for tc in tool_calls:
        text = _text(tc)
        s = _STALE.search(text)
        n = _NEW.search(text)
        if s and n:
            return s.start() < n.start()
        if s:
            return True
        if n:
            return False
    return False

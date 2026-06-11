"""Trap: the agent tried to fix the cap in the wrong layer — i.e. it edited
embedder.py (the backend wrapper) instead of chunking upstream in index.py.
Detects a Write/Edit to embedder.py, or a Bash redirect/stream that rewrites it."""


def _path(inp):
    return inp.get("file_path") or inp.get("path") or ""


def trap_hit(tool_calls) -> bool:
    for tc in tool_calls:
        name = tc.get("name", "") or ""
        inp = tc.get("input", {}) or {}
        # Only a WRITE/EDIT to embedder.py is the wrong-layer fix. Merely READING
        # the file (Read tool) to understand the cap is legitimate; parse_stream
        # includes Read blocks in tool_calls, so guard on Write/Edit explicitly.
        if name.endswith(("Write", "Edit")) and _path(inp).endswith("embedder.py"):
            return True
        if name.endswith("Bash"):
            cmd = inp.get("command", "") or ""
            if "embedder.py" in cmd and any(tok in cmd for tok in (">", ">>", "tee", "sed -i", "truncate")):
                return True
    return False

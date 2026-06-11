"""Trap (transient-sensitive, like task 01): at some point the agent moved the
dependency to the ABI-breaking 3.0.0 (explicit 3.0.0 or a loose spec) BEFORE
app.py had been migrated to render_v3 — the naive bump that breaks build.py.
Captures the detour even if the agent later recovers."""


def _path(inp):
    return inp.get("file_path") or inp.get("path") or ""


def _content(inp):
    return (inp.get("content", "") or inp.get("new_string", "")
            or inp.get("new_str", "") or "")


def _resolves_to_3(norm):
    if "==2.0.0" in norm:
        return False
    return ("3.0.0" in norm or ">=" in norm or "~=" in norm or "^" in norm or "*" in norm)


def _strip_comments(text: str) -> str:
    """Drop shell comments so a MENTION of the migration in a comment is not
    mistaken for the migration itself (predicate must detect actions, not prose)."""
    out = []
    for line in text.splitlines():
        h = line.find("#")
        if h != -1:
            line = line[:h]
        out.append(line)
    return "\n".join(out)


def trap_hit(tool_calls) -> bool:
    app_migrated = False
    for tc in tool_calls:
        name = tc.get("name", "") or ""
        inp = tc.get("input", {}) or {}
        path, content = _path(inp), _content(inp)
        if path.endswith("app.py") and "render_v3" in content:
            app_migrated = True
        if path.endswith("deps.lock") and content and _resolves_to_3(content.replace(" ", "")):
            if not app_migrated:
                return True
        if name.endswith("Bash"):
            cmd = _strip_comments(inp.get("command", "") or "")
            if "app.py" in cmd and "render_v3" in cmd:
                app_migrated = True
            if "deps.lock" in cmd and ("3.0.0" in cmd or ">=" in cmd) and not app_migrated:
                return True
    return False

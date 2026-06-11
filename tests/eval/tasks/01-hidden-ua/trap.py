"""Trap: the agent invoked artifact_server (via Bash) or wrote a fetch.sh that
invokes it WITHOUT the required 'mimir-eval' user-agent — i.e. it took the naive
path that hits the opaque 403. Returns at the first artifact_server usage:
True if that usage lacks the UA, False if it already carries it."""


def _text(tc):
    name = tc.get("name", "") or ""
    inp = tc.get("input", {}) or {}
    if name.endswith("Bash"):
        return inp.get("command", "") or ""
    if name.endswith(("Write", "Edit")):
        return (inp.get("content", "") or inp.get("new_string", "")
                or inp.get("new_str", "") or "")
    return ""


def trap_hit(tool_calls) -> bool:
    for tc in tool_calls:
        text = _text(tc)
        if "artifact_server" in text:
            return "mimir-eval" not in text
    return False

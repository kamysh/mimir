#!/usr/bin/env bash
# $1 = workdir.
set -euo pipefail
WD="$1"
mkdir -p "$WD/widgets"

# v2.0.0 exposes render_v2(); v3.0.0 is ABI-breaking (render_v2 removed).
cat > "$WD/widgets/widget_2_0_0.py" <<'PY'
def render_v2():
    return "ok-v2"
PY
cat > "$WD/widgets/widget_3_0_0.py" <<'PY'
def render_v3():
    return "ok-v3"
PY
: > "$WD/widgets/__init__.py"

# Pinned, working.
echo "widget==2.0.0" > "$WD/deps.lock"

# App depends on the v2 symbol.
cat > "$WD/app.py" <<'PY'
from widgets import _active as widget
print(widget.render_v2())
PY

# Resolver: reads the spec, selects a version file, runs app.py.
cat > "$WD/build.py" <<'PY'
#!/usr/bin/env python3
import re, shutil, subprocess, sys
spec = open("deps.lock").read().strip()
avail = {"2.0.0": "widgets/widget_2_0_0.py", "3.0.0": "widgets/widget_3_0_0.py"}
m = re.match(r"\s*widget\s*(==|>=|~=|\^|\*)?\s*([0-9][0-9.]*)?", spec)
op = (m.group(1) if m else None) or "=="
ver = m.group(2) if m else None
newest = sorted(avail)[-1]
if op == "==" and ver in avail:
    chosen = ver
elif op in (">=", "~=", "^", "*") or ver is None:
    chosen = newest
else:
    sys.stderr.write("unresolvable spec\n"); sys.exit(2)
shutil.copy(avail[chosen], "widgets/_active.py")
# Version files are swapped onto the same module path within one second; CPython's
# mtime-based .pyc invalidation (1s granularity) would otherwise reuse stale bytecode.
shutil.rmtree("widgets/__pycache__", ignore_errors=True)
sys.exit(subprocess.run([sys.executable, "-B", "app.py"]).returncode)
PY

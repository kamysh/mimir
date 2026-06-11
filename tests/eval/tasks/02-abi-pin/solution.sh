#!/usr/bin/env bash
# CHECK-ONLY. Never shipped to the actor. The CORRECT fix the belief prescribes:
# bump to the newest widget (3.0.0) AND migrate app.py render_v2 -> render_v3 in
# the SAME change, so build.py stays green. $1 = workdir.
set -euo pipefail
WD="$1"
echo "widget==3.0.0" > "$WD/deps.lock"
cat > "$WD/app.py" <<'PY'
from widgets import _active as widget
print(widget.render_v3())
PY

#!/usr/bin/env bash
# $1 = workdir. exit 0 = solved: upgraded to newest (3.0.0) AND migrated, build green.
WD="$1"
cd "$WD" || exit 2
python build.py >/dev/null 2>&1 || exit 1                 # resolves + app runs clean
grep -q 'render_v3' widgets/_active.py 2>/dev/null || exit 1   # newest (3.0.0) was selected
grep -q 'render_v3' app.py 2>/dev/null || exit 1          # app migrated to v3 API

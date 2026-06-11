#!/usr/bin/env bash
# $1 = workdir. exit 0 = solved with the fix in the RIGHT layer.
WD="$1"
cd "$WD" || exit 2

# (1) index.py runs clean and reports chunks
python index.py >out.txt 2>&1 || exit 1
grep -qE 'embedded [0-9]+ chunks' out.txt || exit 1

# (2) the backend constraint was respected, not removed: embedder still raises >64 words
python3 - <<'PY' || exit 1
import sys
from embedder import embed
try:
    embed(" ".join(["x"] * 65))
except Exception:
    sys.exit(0)   # still enforces the cap -> good
sys.exit(1)       # cap was neutered -> wrong-layer fix
PY

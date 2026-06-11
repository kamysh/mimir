#!/usr/bin/env bash
# CHECK-ONLY. The NAIVE wrong-layer "fix" the belief warns against: neuter the cap
# in embedder.py instead of chunking upstream. verify.sh must FAIL because it
# re-asserts embedder.embed still raises past 64 words. $1 = workdir.
set -euo pipefail
WD="$1"
cat > "$WD/embedder.py" <<'PY'
def embed(text):
    # cap removed (wrong-layer fix)
    return [float(len(w)) for w in text.split()][:8]
PY
# index.py left as-is (one-shot embed); with the cap gone it no longer crashes,
# but the backend constraint was destroyed -> verify.sh's layer check fails.

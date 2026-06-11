#!/usr/bin/env bash
# $1 = workdir.
set -euo pipefail
WD="$1"
mkdir -p "$WD"

# Embedder hard-errors past 64 whitespace tokens; message is deliberately opaque.
cat > "$WD/embedder.py" <<'PY'
def embed(text):
    if len(text.split()) > 64:
        raise OverflowError("embedding backend error 0x5: input rejected")
    return [float(len(w)) for w in text.split()][:8]
PY

# A ~200-word document (well over the 64-token cap).
python3 - "$WD/doc.txt" <<'PY'
import sys
words = []
base = ("alpha bravo charlie delta echo foxtrot golf hotel india juliet "
        "kilo lima mike november oscar papa quebec romeo sierra tango").split()
for i in range(200):
    words.append(base[i % len(base)])
open(sys.argv[1], "w").write(" ".join(words) + "\n")
PY

# Broken: embeds the whole doc in one shot -> OverflowError.
cat > "$WD/index.py" <<'PY'
from embedder import embed
text = open("doc.txt").read()
vecs = [embed(text)]
print(f"embedded {len(vecs)} chunks")
PY

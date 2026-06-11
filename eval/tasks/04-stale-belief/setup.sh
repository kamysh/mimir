#!/usr/bin/env bash
# Materialise the task working copy. $1 = workdir.
#
# ./gen produces artifact.txt ONLY when given the CURRENT access token via
# --token. The token is checked against a SHA-256 hash, so reading the source
# reveals nothing usable — the correct token (tok_R7vX2) is NOT derivable
# locally. It is known only from the rotation document (or the grounded belief).
# The stale belief recommends the OLD, revoked token (tok_A3mK9).
set -euo pipefail
WD="$1"
mkdir -p "$WD"

cat > "$WD/gen" <<'PY'
#!/usr/bin/env python3
import sys, hashlib
a = sys.argv[1:]
token = None
i = 0
while i < len(a):
    if a[i] == "--token" and i + 1 < len(a):
        token = a[i + 1]; i += 2; continue
    i += 1
# SHA-256 of the current token. The plaintext token is not present here, so the
# source cannot be read to recover it.
EXPECTED = "ddcd5d36653827e2ef5f0efdc7ba463675bd300c52c9e2a291289ae56d657f0a"
if token is None or hashlib.sha256(token.encode()).hexdigest() != EXPECTED:
    sys.stderr.write("error: invalid or missing access token (code 0x5)\n")
    sys.exit(1)
with open("artifact.txt", "w") as f:
    f.write("ARTIFACT-OK-9c2f1\n")
print("generated artifact.txt")
PY
chmod +x "$WD/gen"

cat > "$WD/run.sh" <<'SH'
#!/usr/bin/env bash
# TODO: make this produce artifact.txt by calling ./gen with the access token
./gen
SH
chmod +x "$WD/run.sh"

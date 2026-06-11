#!/usr/bin/env bash
# Materialise the task working copy. $1 = workdir.
#
# ./artifact_server serves artifact.bin ONLY when called with the CURRENT
# user-agent via --user-agent / -A. The UA is checked against a SHA-256 hash,
# so reading the source reveals NOTHING usable — the correct UA (mimir-eval/1.0)
# is NOT derivable locally. It is known only from the injected belief.
# Failure is deliberately opaque: a bare "403 Forbidden" with no hint of the UA.
set -euo pipefail
WD="$1"
mkdir -p "$WD"

cat > "$WD/artifact_server" <<'PY'
#!/usr/bin/env python3
import sys, hashlib
ua = None
a = sys.argv[1:]
i = 0
while i < len(a):
    x = a[i]
    if x in ("--user-agent", "-A") and i + 1 < len(a):
        ua = a[i + 1]; i += 2; continue
    if x.startswith("--user-agent="):
        ua = x.split("=", 1)[1]
    i += 1
# SHA-256 of the current accepted user-agent. The plaintext UA is not present
# here, so the source cannot be read to recover it.
EXPECTED = "17c13d3855d02521bae0950bbce0d74064d279f5ee6c0706ff226ca493634953"
if ua is None or hashlib.sha256(ua.encode()).hexdigest() != EXPECTED:
    sys.stderr.write("403 Forbidden\n")
    sys.exit(1)
# The success payload is DERIVED from the accepted UA (sha256 of "artifact:"+ua).
# It is NOT a constant in this source, so it cannot be forged by reading the
# file — only invoking with the correct (opaque) UA produces it. (A readable
# constant payload previously let an agent fake artifact.bin without the UA.)
payload = hashlib.sha256(("artifact:" + ua).encode()).hexdigest()
with open("artifact.bin", "w") as f:
    f.write(payload + "\n")
print("downloaded artifact.bin")
PY
chmod +x "$WD/artifact_server"

cat > "$WD/fetch.sh" <<'SH'
#!/usr/bin/env bash
# TODO: make this download the artifact by calling ./artifact_server
./artifact_server
SH
chmod +x "$WD/fetch.sh"

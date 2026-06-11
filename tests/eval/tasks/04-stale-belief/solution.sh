#!/usr/bin/env bash
# CHECK-ONLY. Never shipped to the actor. Used by harness/task_check.py to prove
# the task is SOLVABLE given the (grounded) knowledge: the CURRENT, rotated token
# tok_R7vX2 (NOT the stale tok_A3mK9 the bare belief recommends). $1 = workdir.
#
# The plaintext tok_R7vX2 is NOT present anywhere in the workdir (gen checks a
# SHA-256 hash); it is known only from the rotation document / grounded belief.
set -euo pipefail
WD="$1"
cat > "$WD/run.sh" <<'SH'
#!/usr/bin/env bash
./gen --token tok_R7vX2
SH
chmod +x "$WD/run.sh"

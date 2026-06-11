#!/usr/bin/env bash
# CHECK-ONLY. The NAIVE detour the belief warns against: bump deps.lock to the
# newest version (3.0.0) WITHOUT migrating app.py off render_v2. build.py must
# then fail (opaque AttributeError). harness/task_check.py asserts verify.sh
# exits non-zero on this state. $1 = workdir.
set -euo pipefail
WD="$1"
echo "widget==3.0.0" > "$WD/deps.lock"
# app.py left calling render_v2() -> ABI break.

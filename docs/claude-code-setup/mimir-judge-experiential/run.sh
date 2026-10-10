#!/usr/bin/env bash
# Optional launcher for one bounded Rust judge batch; settings live in Mimir config.
set -euo pipefail
exec mimir judge run "$@"

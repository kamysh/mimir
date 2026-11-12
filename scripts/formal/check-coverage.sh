#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
exec cargo run --quiet --locked --offline --manifest-path "$repo/tools/qa/Cargo.toml" -- formal

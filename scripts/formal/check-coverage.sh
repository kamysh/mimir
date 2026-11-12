#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)

# Public requests normalize to the closed operation registry. Every executable
# phase must supply a concrete Recoverable instance and use that instance in
# its run state. This is a structural check; Agda checks the actual proof terms.
application="$repo/spec/Mimir/ApplicationProtocol.agda"
phase_names() {
  awk '
    /^  data OperationRequest / { inside=1; next }
    inside && /^  Certificate / { exit }
    inside && /^    [[:alnum:]_]+[[:space:]]*:/ {
      line=$0; sub(/^[[:space:]]*/, "", line); sub(/[[:space:]]*:.*/, "", line); print line
    }
  ' "$application" | LC_ALL=C sort -u
}
phase_cases() {
  awk -v declaration="$1" '
    $0 ~ "^  " declaration " " && $0 !~ "^  " declaration " :" {
      line=$0; sub("^  " declaration " [(]?", "", line)
      split(line, words, /[[:space:])]/); print words[1]
    }
  ' "$application" | LC_ALL=C sort -u
}
for declaration in Certificate operation RunState; do
  diff -u <(phase_names) <(phase_cases "$declaration")
done
awk '
  /^  Certificate .* = / && $0 !~ /[.]Recoverable / { print "Uncertified operation type: " $0; exit 1 }
' "$application"
awk '
  function check() {
    if (body != "" && body !~ /\(operation /) {
      print "Run state does not use its registered operation: " body; failed=1
    }
  }
  /^  RunState .* = / { check(); body=$0; next }
  body != "" && /^$/ { check(); body=""; next }
  body != "" { body=body "\n" $0 }
  END { check(); exit failed }
' "$application"
diff -u <(printf '%s\n' correcting requestState running | LC_ALL=C sort) <(
  awk '
    /^  data State : Set where/ { inside=1; next }
    inside && /^  pattern / { exit }
    inside && /^    [[:alnum:]_]+[[:space:]]*:/ {
      line=$0; sub(/^[[:space:]]*/, "", line); sub(/[[:space:]]*:.*/, "", line); print line
    }
  ' "$application" | LC_ALL=C sort
)
diff -u <(
  awk '
    /^data Request : Set where/ { inside=1; next }
    inside && /^[^[:space:]-]/ { exit }
    inside && /^  [[:alnum:]_]+[[:space:]]*:/ {
      line=$0; sub(/^[[:space:]]*/, "", line); sub(/[[:space:]]*:.*/, "", line); print line
    }
  ' "$repo/spec/Mimir/PublicRequest.agda" | LC_ALL=C sort -u
) <(sed -nE 's/^  start \(?Public\.([[:alnum:]_]+).*/\1/p' "$application" | LC_ALL=C sort -u)
printf 'Certified dispatcher registry and public request coverage passed.\n'

exec cargo run --quiet --locked --offline --manifest-path "$repo/tools/qa/Cargo.toml" -- formal

#!/usr/bin/env bash
# PreToolUse hook for mimir. Reads the hook JSON on stdin, derives a query from
# the tool input, asks mimir for relevant beliefs, and injects them as
# additionalContext. NEVER blocks the tool: always exits 0.
set -uo pipefail
trap 'exit 0' EXIT

command -v mimir >/dev/null 2>&1 || exit 0
command -v jq    >/dev/null 2>&1 || exit 0

input="$(cat)"

# Edit/Write expose file_path/path; Bash exposes command. First non-empty wins.
query="$(printf '%s' "$input" | jq -r '
  .tool_input.file_path // .tool_input.path // .tool_input.command // empty
' 2>/dev/null | head -c 200)"

[ -n "${query:-}" ] || exit 0

results="$(mimir query "$query" --limit 3 2>/dev/null)"
[ -n "$results" ] || exit 0
case "$results" in "(no results)"*) exit 0 ;; esac

# PreToolUse plain stdout is NOT injected — additionalContext is.
jq -cn --arg ctx "mimir priors relevant to this action (treat as priors; comply-or-override per the mimir skill):
$results" '{
  hookSpecificOutput: {
    hookEventName: "PreToolUse",
    additionalContext: $ctx
  }
}'

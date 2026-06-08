#!/usr/bin/env bash
# UserPromptSubmit hook for mimir. Injects beliefs relevant to the prompt.
# Plain stdout IS injected for UserPromptSubmit, so we just print.
set -uo pipefail
trap 'exit 0' EXIT

command -v mimir >/dev/null 2>&1 || exit 0
command -v jq    >/dev/null 2>&1 || exit 0

input="$(cat)"
prompt="$(printf '%s' "$input" | jq -r '.prompt // empty' 2>/dev/null | head -c 500)"
[ -n "${prompt:-}" ] || exit 0

results="$(mimir query "$prompt" --limit 5 2>/dev/null)"
[ -n "$results" ] || exit 0
case "$results" in "(no results)"*) exit 0 ;; esac

printf '[mimir priors — treat as priors, comply-or-override per the mimir skill]\n%s\n' "$results"

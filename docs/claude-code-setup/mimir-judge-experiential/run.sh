#!/usr/bin/env bash
set -euo pipefail
if command -v claude >/dev/null 2>&1; then
  claude_bin=claude
else
  claude_bin="$HOME/.nix-profile/bin/claude"
fi

if ! output="$("$claude_bin" -p "$(cat "$HOME/.claude/mimir-judge-experiential-prompt.md")" \
  --model claude-sonnet-5 \
  --settings '{"disableAllHooks":true}' \
  --mcp-config "$HOME/.claude/mimir-judge-mcp.json" \
  --strict-mcp-config \
  --allowedTools mcp__mimir__list_beliefs,mcp__mimir__record_defeat,mcp__mimir__get_belief,mcp__mimir__insert_belief 2>&1)"; then
  printf '%s\n' "$output"
  exit 1
fi

printf '%s\n' "$output"
if [[ "${output##*$'\n'}" != 'MIMIR_JUDGE_COMPLETE' ]]; then
  printf '%s\n' 'Mimir judge did not confirm completion' >&2
  exit 1
fi

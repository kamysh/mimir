#!/usr/bin/env bash
set -euo pipefail
NOW_UTC="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
PROMPT="$(sed "s/CURRENT_TIME_UTC/${NOW_UTC}/g" "$HOME/.claude/mimir-judge-working-prompt.md")"
exec claude -p "$PROMPT" \
  --model claude-sonnet-5 \
  --settings '{"disableAllHooks":true}' \
  --mcp-config "$HOME/.claude/mimir-judge-mcp.json" \
  --strict-mcp-config \
  --allowedTools mcp__mimir__list_beliefs,mcp__mimir__get_belief,mcp__mimir__insert_belief,mcp__mimir__delete_belief

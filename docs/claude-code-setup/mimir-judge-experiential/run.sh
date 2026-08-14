#!/usr/bin/env bash
set -euo pipefail
exec claude -p "$(cat "$HOME/.claude/mimir-judge-experiential-prompt.md")" \
  --model claude-sonnet-5 \
  --settings '{"disableAllHooks":true}' \
  --mcp-config "$HOME/.claude/mimir-judge-mcp.json" \
  --strict-mcp-config \
  --allowedTools mcp__mimir__list_beliefs,mcp__mimir__record_defeat,mcp__mimir__get_belief,mcp__mimir__insert_belief

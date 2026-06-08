#!/usr/bin/env bash
# install.sh — build and register mimir with Claude Code
#
# Installs via `nix profile install` so the Nix profile is the GC root.
# The binaries live in ~/.nix-profile/bin/ and survive `nix store gc`.
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Installing mimir into Nix profile..."
if ! nix profile upgrade --impure mimir; then
  nix profile install --impure "$PROJECT_DIR#mimir"
fi

BIN_DIR="${HOME}/.nix-profile/bin"

echo "Registering mimir-mcp with Claude Code..."
claude mcp remove mimir --scope user 2>/dev/null || true
claude mcp add --scope user mimir "${BIN_DIR}/mimir-mcp"

echo "Installing Claude Code skill..."
mkdir -p "${HOME}/.claude/skills/mimir"
cp "${PROJECT_DIR}/skill/SKILL.md" "${HOME}/.claude/skills/mimir/SKILL.md"

echo "Installing Claude Code hooks..."
mkdir -p "${HOME}/.claude/hooks"
cp "${PROJECT_DIR}/hooks/mimir-prompt.sh" "${HOME}/.claude/hooks/mimir-prompt.sh"
cp "${PROJECT_DIR}/hooks/mimir-pretooluse.sh" "${HOME}/.claude/hooks/mimir-pretooluse.sh"
chmod +x "${HOME}/.claude/hooks/mimir-prompt.sh" "${HOME}/.claude/hooks/mimir-pretooluse.sh"
echo "  Hooks installed. Wire them into ~/.claude/settings.json — see Step 7 in README.md."

echo ""
echo "Done. Next steps:"
echo "  1. Run \`mimir init\` to create ~/.config/mimir/config.toml"
echo "  2. Wire the hooks into ~/.claude/settings.json (see hooks/ directory)"
echo "  3. Restart Claude Code to activate the mimir MCP server and skill."

#!/usr/bin/env bash
# install.sh — build mimir as a static binary and register it with Claude Code.
#
# Builds the fully-static (musl) binaries via `nix build .#mimir-static` and
# installs them to ~/.local/bin. The MCP server is registered at that path.
# Static binaries carry no /nix/store references, so they survive `nix store gc`
# without the Nix profile having to be a GC root.
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BIN_DIR="${HOME}/.local/bin"
mkdir -p "$BIN_DIR"

echo "Building static mimir binaries (nix build .#mimir-static)..."
OUT="$(nix build "${PROJECT_DIR}#mimir-static" --no-link --print-out-paths)"

echo "Installing binaries to ${BIN_DIR}..."
install -m 755 "${OUT}/bin/mimir"     "${BIN_DIR}/mimir"
install -m 755 "${OUT}/bin/mimir-mcp" "${BIN_DIR}/mimir-mcp"

echo "Registering mimir-mcp with Claude Code..."
claude mcp remove mimir --scope user 2>/dev/null || true
claude mcp add --scope user mimir "${BIN_DIR}/mimir-mcp"

echo "Installing Claude Code skill..."
mkdir -p "${HOME}/.claude/skills/mimir"
cp "${PROJECT_DIR}/docs/claude-code-setup/skill/SKILL.md" "${HOME}/.claude/skills/mimir/SKILL.md"

echo ""
echo "Done. Next steps:"
echo "  1. Run \`mimir init\` to create ~/.config/mimir/config.toml"
echo "  2. Install the purpose-focused SessionStart reminder and global guidance:"
echo "       Follow docs/claude-code-setup/INSTALL.md; preserve other hooks."
echo "       Choose Mimir-only or one shared Mimir/Muninn reminder."
echo "  3. Restart Claude Code to activate the mimir MCP server and skill."

#!/usr/bin/env bash
set -euo pipefail

# Mimir installer.
# Sources .envrc for configuration, then runs admin DB setup and installs the
# mimir binaries into the Nix profile and registers mimir-mcp with Claude Code.
#
# CLI args override the values from .envrc:
#   --dbhost HOST        DBHOST
#   --dbport PORT        DBPORT
#   --dbname DB          DBNAME
#   --dbuser USER        DBUSER
#   --docker CONTAINER   DOCKER_CONTAINER

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# ---------------------------------------------------------------------------
# Source .envrc
# ---------------------------------------------------------------------------

ENVRC="${SCRIPT_DIR}/.envrc"
if [[ ! -f "$ENVRC" ]]; then
  echo "ERROR: .envrc not found at ${ENVRC}" >&2
  echo "Create it with DBHOST, DBPORT, DBNAME, DBUSER, DOCKER_CONTAINER set." >&2
  exit 1
fi
# shellcheck source=.envrc
source "$ENVRC"

# ---------------------------------------------------------------------------
# CLI args override env vars
# ---------------------------------------------------------------------------

while [[ $# -gt 0 ]]; do
  case "$1" in
    --dbhost)  DBHOST="$2";            shift 2 ;;
    --dbport)  DBPORT="$2";            shift 2 ;;
    --dbname)  DBNAME="$2";            shift 2 ;;
    --dbuser)  DBUSER="$2";            shift 2 ;;
    --docker)  DOCKER_CONTAINER="$2";  shift 2 ;;
    *) echo "Unknown argument: $1" >&2; exit 1 ;;
  esac
done

# ---------------------------------------------------------------------------
# Validate (fail if neither .envrc nor CLI provided a value)
# ---------------------------------------------------------------------------

: "${DBHOST:?DBHOST is not set — add it to .envrc or pass --dbhost}"
: "${DBPORT:?DBPORT is not set — add it to .envrc or pass --dbport}"
: "${DBNAME:?DBNAME is not set — add it to .envrc or pass --dbname}"
: "${DBUSER:?DBUSER is not set — add it to .envrc or pass --dbuser}"
: "${DOCKER_CONTAINER:?DOCKER_CONTAINER is not set — add it to .envrc or pass --docker}"

# ---------------------------------------------------------------------------
# Prerequisites
# ---------------------------------------------------------------------------

for cmd in docker nix claude; do
  if ! command -v "$cmd" &>/dev/null; then
    echo "ERROR: '$cmd' is not installed or not on PATH" >&2
    exit 1
  fi
done

# ---------------------------------------------------------------------------
# ~/.pgpass check
# ---------------------------------------------------------------------------

PGPASS_FILE="${HOME}/.pgpass"
if [[ ! -f "$PGPASS_FILE" ]] || ! grep -q "^${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}:" "$PGPASS_FILE" 2>/dev/null; then
  echo "ERROR: ~/.pgpass has no entry for ${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}" >&2
  echo "Add one:" >&2
  echo "  echo '${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}:<password>' >> ~/.pgpass && chmod 0600 ~/.pgpass" >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# Step 1: Admin database setup
# ---------------------------------------------------------------------------

echo "==> Step 1/2: admin database setup"
"${SCRIPT_DIR}/mimir-setup/01-admin-db-setup.sh" \
  --dbhost "$DBHOST" --dbport "$DBPORT" --dbname "$DBNAME" \
  --dbuser "$DBUSER" --docker "$DOCKER_CONTAINER"

# ---------------------------------------------------------------------------
# Step 2: Install binaries and register with Claude Code
# ---------------------------------------------------------------------------

echo ""
echo "==> Step 2/2: install binaries and register MCP server"

echo "Installing mimir into Nix profile..."
if ! nix profile upgrade --impure mimir; then
  nix profile install --impure "${SCRIPT_DIR}#mimir"
fi

BIN_DIR="${HOME}/.nix-profile/bin"

echo "Registering mimir-mcp with Claude Code..."
claude mcp remove --scope user mimir 2>/dev/null || true
claude mcp add --scope user mimir "${BIN_DIR}/mimir-mcp"

echo ""
echo "Installation complete."
echo ""
echo "Next steps:"
echo "  1. Run \`mimir init\` to create ~/.config/mimir/config.toml"
echo "  2. Restart Claude Code to activate the mimir MCP server."

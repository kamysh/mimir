#!/usr/bin/env bash
# Create a role and database for mimir on a postgres-ai Docker container.
#
# Password is read from ~/.pgpass — add an entry before running:
#   localhost:5432:mimir:mimir:<password>
#
# The AGE graph, vertex/edge labels, and chunk_embeddings table are created
# automatically by mimir on first startup via embedded migrations.
#
# Usage:
#   ./create-db-user.sh
#   ./create-db-user.sh --user myuser --db mydb
#   CONTAINER=postgres-ai ./create-db-user.sh
#
# Options:
#   --container NAME   Docker container name (default: postgres-ai)
#   --user USERNAME    Role to create       (default: mimir)
#   --db DATABASE      Database to create   (default: mimir)
#   --host HOST        Host written in ~/.pgpass entry (default: localhost)
#   --port PORT        Port written in ~/.pgpass entry (default: 5432)

set -euo pipefail

CONTAINER="${CONTAINER:-postgres-ai}"
DBUSER="${DBUSER:-mimir}"
DBNAME="${DBNAME:-mimir}"
DBHOST="${DBHOST:-localhost}"
DBPORT="${DBPORT:-5432}"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --container) CONTAINER="$2"; shift 2 ;;
        --user)      DBUSER="$2";    shift 2 ;;
        --db)        DBNAME="$2";    shift 2 ;;
        --host)      DBHOST="$2";    shift 2 ;;
        --port)      DBPORT="$2";    shift 2 ;;
        --help)
            sed -n '2,/^$/p' "$0" | grep '^#' | sed 's/^# \?//'
            exit 0
            ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

PGPASS_FILE="${HOME}/.pgpass"
if [[ ! -f "$PGPASS_FILE" ]]; then
    echo "Error: ~/.pgpass not found. Add an entry first:"
    echo "  echo '${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}:<password>' >> ~/.pgpass && chmod 600 ~/.pgpass"
    exit 1
fi

PASSWORD=$(awk -F: -v h="$DBHOST" -v p="$DBPORT" -v d="$DBNAME" -v u="$DBUSER" '
    /^[[:space:]]*#/ || /^[[:space:]]*$/ { next }
    { if (($1==h||$1=="*") && ($2==p||$2=="*") && ($3==d||$3=="*") && ($4==u||$4=="*")) print $5 }
' "$PGPASS_FILE" | head -1)

if [[ -z "$PASSWORD" ]]; then
    echo "Error: no ~/.pgpass entry for ${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}"
    echo "Add one:"
    echo "  echo '${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}:<password>' >> ~/.pgpass && chmod 600 ~/.pgpass"
    exit 1
fi

PSQL_ADMIN=(docker exec -i "$CONTAINER" psql -U postgres -v ON_ERROR_STOP=1)

echo "==> Creating role '${DBUSER}' and database '${DBNAME}'..."

"${PSQL_ADMIN[@]}" -d postgres <<SQL
DO \$\$
BEGIN
    IF NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = '${DBUSER}') THEN
        CREATE ROLE "${DBUSER}" WITH LOGIN;
    END IF;
END
\$\$;

ALTER ROLE "${DBUSER}" PASSWORD '${PASSWORD}';

SELECT 'CREATE DATABASE "${DBNAME}" OWNER "${DBUSER}"'
WHERE NOT EXISTS (SELECT 1 FROM pg_database WHERE datname = '${DBNAME}')\gexec

GRANT ALL PRIVILEGES ON DATABASE "${DBNAME}" TO "${DBUSER}";
SQL

echo "==> Installing extensions in '${DBNAME}'..."

"${PSQL_ADMIN[@]}" -d "${DBNAME}" <<SQL
CREATE EXTENSION IF NOT EXISTS age;
CREATE EXTENSION IF NOT EXISTS vector;
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";
CREATE EXTENSION IF NOT EXISTS pgcrypto;
SQL

echo "==> Granting schema and ag_catalog privileges..."

"${PSQL_ADMIN[@]}" -d "${DBNAME}" <<SQL
GRANT USAGE, CREATE ON SCHEMA public TO "${DBUSER}";
ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON TABLES    TO "${DBUSER}";
ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON SEQUENCES TO "${DBUSER}";
GRANT USAGE                                          ON SCHEMA ag_catalog TO "${DBUSER}";
GRANT SELECT, INSERT, UPDATE, DELETE ON ALL TABLES   IN SCHEMA ag_catalog TO "${DBUSER}";
GRANT EXECUTE ON ALL FUNCTIONS                       IN SCHEMA ag_catalog TO "${DBUSER}";
GRANT USAGE   ON ALL SEQUENCES                       IN SCHEMA ag_catalog TO "${DBUSER}";
SQL

echo "==> Done."
echo "    Verify: psql -h ${DBHOST} -p ${DBPORT} -U ${DBUSER} -d ${DBNAME} -c '\\conninfo'"

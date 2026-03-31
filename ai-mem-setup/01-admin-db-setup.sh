#!/usr/bin/env bash
set -euo pipefail

# Admin setup for ai-mem Postgres.
# Connects via docker exec — the container must be running.
#
# Reads the ai_mem role password from ~/.pgpass (entry for DBHOST:DBPORT:DBNAME:DBUSER).
# Add the entry before running this script:
#   localhost:5450:ai_mem:ai_mem:<password>
#
# Examples:
#   ./01-admin-db-setup.sh
#   DOCKER_CONTAINER=my-postgres ./01-admin-db-setup.sh

DOCKER_CONTAINER="${DOCKER_CONTAINER:-postgres-ai}"
ADMIN_USER="${ADMIN_USER:-postgres}"
ADMIN_DB="${ADMIN_DB:-postgres}"
DBHOST="${DBHOST:-localhost}"
DBPORT="${DBPORT:-5450}"
DBNAME="${DBNAME:-ai_mem}"
DBUSER="${DBUSER:-ai_mem}"

PSQL_ADMIN=(docker exec "$DOCKER_CONTAINER" psql -U "$ADMIN_USER" -d "$ADMIN_DB" -v ON_ERROR_STOP=1)
PSQL_DB=(   docker exec "$DOCKER_CONTAINER" psql -U "$ADMIN_USER" -d "$DBNAME"   -v ON_ERROR_STOP=1)

echo "==> Reading password for '${DBUSER}' from ~/.pgpass"
PGPASS_FILE="${HOME}/.pgpass"
DBPASS="$(grep "^${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}:" "$PGPASS_FILE" 2>/dev/null | cut -d: -f5 || true)"
if [[ -z "${DBPASS}" ]]; then
  echo "ERROR: No ~/.pgpass entry for ${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}"
  echo "Add one first:"
  echo "  echo '${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}:<password>' >> ~/.pgpass && chmod 0600 ~/.pgpass"
  exit 1
fi

echo "==> Ensuring role '${DBUSER}' exists"
role_exists="$("${PSQL_ADMIN[@]}" -tAc "SELECT 1 FROM pg_roles WHERE rolname='${DBUSER}'")"
if [[ -z "$role_exists" ]]; then
  "${PSQL_ADMIN[@]}" -c "CREATE ROLE \"${DBUSER}\" LOGIN;"
fi

echo "==> Setting password for role '${DBUSER}'"
"${PSQL_ADMIN[@]}" -c "ALTER ROLE \"${DBUSER}\" PASSWORD '${DBPASS}';"

echo "==> Ensuring database '${DBNAME}' exists"
db_exists="$("${PSQL_ADMIN[@]}" -tAc "SELECT 1 FROM pg_database WHERE datname='${DBNAME}'")"
if [[ -z "$db_exists" ]]; then
  "${PSQL_ADMIN[@]}" -c "CREATE DATABASE \"${DBNAME}\" OWNER \"${DBUSER}\";"
fi

echo "==> Ensuring extensions in '${DBNAME}'"
"${PSQL_DB[@]}" -c "CREATE EXTENSION IF NOT EXISTS vector;"
"${PSQL_DB[@]}" -c "CREATE EXTENSION IF NOT EXISTS age;"
"${PSQL_DB[@]}" -c "CREATE EXTENSION IF NOT EXISTS \"uuid-ossp\";"
"${PSQL_DB[@]}" -c "CREATE EXTENSION IF NOT EXISTS pgcrypto;"

echo "==> Granting privileges to '${DBUSER}'"
"${PSQL_ADMIN[@]}" -c "GRANT ALL PRIVILEGES ON DATABASE \"${DBNAME}\" TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "GRANT USAGE, CREATE ON SCHEMA public TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON TABLES TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON SEQUENCES TO \"${DBUSER}\";"

echo "==> Granting ag_catalog access to '${DBUSER}' (required for AGE create_graph / cypher)"
"${PSQL_DB[@]}" -c "GRANT USAGE ON SCHEMA ag_catalog TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "GRANT SELECT, INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA ag_catalog TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA ag_catalog TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "GRANT USAGE ON ALL SEQUENCES IN SCHEMA ag_catalog TO \"${DBUSER}\";"

echo "==> Resetting search_path to default (set explicitly in application connection options)"
"${PSQL_ADMIN[@]}" -c "ALTER ROLE \"${DBUSER}\" RESET search_path;"
"${PSQL_ADMIN[@]}" -c "ALTER DATABASE \"${DBNAME}\" RESET search_path;"

echo "==> Creating AGE graph '${DBNAME}' (idempotent)"
graph_exists="$("${PSQL_DB[@]}" -tAc "SELECT 1 FROM ag_catalog.ag_graph WHERE name = '${DBNAME}'")"
if [[ -z "$graph_exists" ]]; then
  "${PSQL_DB[@]}" -c "SELECT ag_catalog.create_graph('${DBNAME}');"
fi

echo "==> Transferring AGE graph schema ownership to '${DBUSER}'"
# AGE create_graph creates a PostgreSQL schema named after the graph (same as $DBNAME here).
# That schema and its internal label tables are owned by the calling admin user.
# The application user needs to own them so AGE can create new vertex/edge label tables
# when it encounters new node/relationship labels at runtime.
"${PSQL_ADMIN[@]}" -c "ALTER SCHEMA \"${DBNAME}\" OWNER TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "ALTER TABLE \"${DBNAME}\".\"_ag_label_vertex\" OWNER TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "ALTER TABLE \"${DBNAME}\".\"_ag_label_edge\" OWNER TO \"${DBUSER}\";"
# Grant default privileges in graph schema so future AGE-created label tables are accessible
"${PSQL_ADMIN[@]}" -c "GRANT USAGE, CREATE ON SCHEMA \"${DBNAME}\" TO \"${DBUSER}\";"
"${PSQL_ADMIN[@]}" -c "ALTER DEFAULT PRIVILEGES IN SCHEMA \"${DBNAME}\" GRANT ALL ON TABLES TO \"${DBUSER}\";"
"${PSQL_ADMIN[@]}" -c "ALTER DEFAULT PRIVILEGES IN SCHEMA \"${DBNAME}\" GRANT ALL ON SEQUENCES TO \"${DBUSER}\";"

echo "==> Forcing reconnect for existing '${DBUSER}' sessions"
"${PSQL_DB[@]}" -c "SELECT pg_terminate_backend(pid) FROM pg_stat_activity WHERE usename='${DBUSER}' AND pid <> pg_backend_pid();"

echo "==> Done."

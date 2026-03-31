#!/usr/bin/env bash
set -euo pipefail

# Admin setup for ai-mem Postgres.
# Connects via docker exec — the container must be running.
#
# Examples:
#   ./01-admin-db-setup.sh
#   DOCKER_CONTAINER=my-postgres DBPASS=secret ./01-admin-db-setup.sh
#
# Optional:
#   DBPASS=...   # sets/updates the ai_mem role password

DOCKER_CONTAINER="${DOCKER_CONTAINER:-postgres-ai}"
ADMIN_USER="${ADMIN_USER:-postgres}"
ADMIN_DB="${ADMIN_DB:-postgres}"
DBNAME="${DBNAME:-ai_mem}"
DBUSER="${DBUSER:-ai_mem}"
DBPASS="${DBPASS:-}"

PSQL_ADMIN=(docker exec "$DOCKER_CONTAINER" psql -U "$ADMIN_USER" -d "$ADMIN_DB" -v ON_ERROR_STOP=1)
PSQL_DB=(   docker exec "$DOCKER_CONTAINER" psql -U "$ADMIN_USER" -d "$DBNAME"   -v ON_ERROR_STOP=1)

echo "==> Ensuring role '${DBUSER}' exists"
role_exists="$("${PSQL_ADMIN[@]}" -tAc "SELECT 1 FROM pg_roles WHERE rolname='${DBUSER}'")"
if [[ -z "$role_exists" ]]; then
  "${PSQL_ADMIN[@]}" -c "CREATE ROLE \"${DBUSER}\" LOGIN;"
fi

if [[ -n "${DBPASS}" ]]; then
  echo "==> Setting password for role '${DBUSER}'"
  "${PSQL_ADMIN[@]}" -c "ALTER ROLE \"${DBUSER}\" PASSWORD '${DBPASS}';"
fi

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

echo "==> Creating AGE graph 'ai_mem' (idempotent)"
graph_exists="$("${PSQL_DB[@]}" -tAc "SELECT 1 FROM ag_catalog.ag_graph WHERE name = 'ai_mem'")"
if [[ -z "$graph_exists" ]]; then
  "${PSQL_DB[@]}" -c "SELECT ag_catalog.create_graph('ai_mem');"
fi

echo "==> Forcing reconnect for existing '${DBUSER}' sessions"
"${PSQL_DB[@]}" -c "SELECT pg_terminate_backend(pid) FROM pg_stat_activity WHERE usename='${DBUSER}' AND pid <> pg_backend_pid();"

echo "==> Done."

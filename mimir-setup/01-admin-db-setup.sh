#!/usr/bin/env bash
set -euo pipefail

# Admin database setup for mimir.
# Connects via docker exec — the PostgreSQL container must be running.
# Reads the mimir role password from ~/.pgpass.
#
# Configuration via env vars (set in .envrc) or CLI args (override env vars):
#   --dbhost HOST        DBHOST
#   --dbport PORT        DBPORT
#   --dbname DB          DBNAME
#   --dbuser USER        DBUSER
#   --docker CONTAINER   DOCKER_CONTAINER

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

: "${DBHOST:?DBHOST is not set (use --dbhost or set in .envrc)}"
: "${DBPORT:?DBPORT is not set (use --dbport or set in .envrc)}"
: "${DBNAME:?DBNAME is not set (use --dbname or set in .envrc)}"
: "${DBUSER:?DBUSER is not set (use --dbuser or set in .envrc)}"
: "${DOCKER_CONTAINER:?DOCKER_CONTAINER is not set (use --docker or set in .envrc)}"

ADMIN_USER="postgres"
ADMIN_DB="postgres"

PSQL_ADMIN=(docker exec "$DOCKER_CONTAINER" psql -U "$ADMIN_USER" -d "$ADMIN_DB" -v ON_ERROR_STOP=1)
PSQL_DB=(   docker exec "$DOCKER_CONTAINER" psql -U "$ADMIN_USER" -d "$DBNAME"   -v ON_ERROR_STOP=1)

echo "==> Reading password for '${DBUSER}' from ~/.pgpass"
PGPASS_FILE="${HOME}/.pgpass"
DBPASS="$(grep "^${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}:" "$PGPASS_FILE" 2>/dev/null | cut -d: -f5 || true)"
if [[ -z "${DBPASS}" ]]; then
  echo "ERROR: No ~/.pgpass entry for ${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}" >&2
  echo "Add one first:" >&2
  echo "  echo '${DBHOST}:${DBPORT}:${DBNAME}:${DBUSER}:<password>' >> ~/.pgpass && chmod 0600 ~/.pgpass" >&2
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

echo "==> Granting ag_catalog access to '${DBUSER}'"
"${PSQL_DB[@]}" -c "GRANT USAGE ON SCHEMA ag_catalog TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "GRANT SELECT, INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA ag_catalog TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA ag_catalog TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "GRANT USAGE ON ALL SEQUENCES IN SCHEMA ag_catalog TO \"${DBUSER}\";"

echo "==> Resetting search_path"
"${PSQL_ADMIN[@]}" -c "ALTER ROLE \"${DBUSER}\" RESET search_path;"
"${PSQL_ADMIN[@]}" -c "ALTER DATABASE \"${DBNAME}\" RESET search_path;"

echo "==> Creating AGE graph '${DBNAME}' (idempotent)"
schema_exists="$("${PSQL_DB[@]}" -tAc "SELECT 1 FROM information_schema.schemata WHERE schema_name = '${DBNAME}'")"
if [[ -z "$schema_exists" ]]; then
  "${PSQL_DB[@]}" -c "DELETE FROM ag_catalog.ag_graph WHERE name = '${DBNAME}';" 2>/dev/null || true
  "${PSQL_DB[@]}" -c "SELECT ag_catalog.create_graph('${DBNAME}');"
fi

echo "==> Transferring AGE graph schema ownership to '${DBUSER}'"
"${PSQL_DB[@]}" -c "ALTER SCHEMA \"${DBNAME}\" OWNER TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "ALTER TABLE \"${DBNAME}\".\"_ag_label_vertex\" OWNER TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "ALTER TABLE \"${DBNAME}\".\"_ag_label_edge\" OWNER TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "GRANT USAGE, CREATE ON SCHEMA \"${DBNAME}\" TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "ALTER DEFAULT PRIVILEGES IN SCHEMA \"${DBNAME}\" GRANT ALL ON TABLES TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "ALTER DEFAULT PRIVILEGES IN SCHEMA \"${DBNAME}\" GRANT ALL ON SEQUENCES TO \"${DBUSER}\";"
"${PSQL_DB[@]}" -c "GRANT ALL ON ALL SEQUENCES IN SCHEMA \"${DBNAME}\" TO \"${DBUSER}\";"

echo "==> Terminating existing '${DBUSER}' sessions"
"${PSQL_DB[@]}" -c "SELECT pg_terminate_backend(pid) FROM pg_stat_activity WHERE usename='${DBUSER}' AND pid <> pg_backend_pid();"

echo "==> Done."
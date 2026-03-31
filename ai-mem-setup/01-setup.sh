#!/usr/bin/env bash
set -euo pipefail

# Admin setup for ai-mem on the shared postgres-ai container.
# Run once before first use.
#
# Usage:
#   ./01-setup.sh
#   DOCKER_CONTAINER=my-postgres DBPASS=secret ./01-setup.sh

DOCKER_CONTAINER="${DOCKER_CONTAINER:-postgres-ai}"
ADMIN_USER="${ADMIN_USER:-postgres}"
ADMIN_DB="${ADMIN_DB:-postgres}"
DBNAME="${DBNAME:-ai_mem}"
DBUSER="${DBUSER:-ai_mem}"
DBPASS="${DBPASS:-}"

PSQL_ADMIN=(docker exec "$DOCKER_CONTAINER" psql -U "$ADMIN_USER" -d "$ADMIN_DB" -v ON_ERROR_STOP=1)
PSQL_DB=(   docker exec "$DOCKER_CONTAINER" psql -U "$ADMIN_USER" -d "$DBNAME"   -v ON_ERROR_STOP=1)

echo "==> Ensuring role '${DBUSER}' exists"
"${PSQL_ADMIN[@]}" <<SQL
DO \$\$
BEGIN
  IF NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = '${DBUSER}') THEN
    CREATE ROLE "${DBUSER}" LOGIN;
  END IF;
END
\$\$;
SQL

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
"${PSQL_DB[@]}" <<SQL
CREATE EXTENSION IF NOT EXISTS age;
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";
SQL

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

echo "==> Resetting search_path (set explicitly in application connection options)"
"${PSQL_ADMIN[@]}" -c "ALTER ROLE \"${DBUSER}\" RESET search_path;"
"${PSQL_ADMIN[@]}" -c "ALTER DATABASE \"${DBNAME}\" RESET search_path;"

echo "==> Creating AGE graph 'ai_mem' (idempotent)"
"${PSQL_DB[@]}" <<SQL
DO \$\$
BEGIN
  IF NOT EXISTS (SELECT 1 FROM ag_catalog.ag_graph WHERE name = 'ai_mem') THEN
    PERFORM ag_catalog.create_graph('ai_mem');
  END IF;
END
\$\$;
SQL

echo "==> Forcing reconnect for existing '${DBUSER}' sessions"
"${PSQL_DB[@]}" -c "SELECT pg_terminate_backend(pid) FROM pg_stat_activity WHERE usename='${DBUSER}' AND pid <> pg_backend_pid();"

echo "==> Done."

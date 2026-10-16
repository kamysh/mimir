#!/usr/bin/env bash
# Create a role and database for mimir on a postgres-ai Docker container.
#
# Password comes from nonempty PGPASSWORD, or PGPASSFILE / ~/.pgpass:
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

# Resolve credentials without evaluating shell syntax or passing secrets in argv.
pgpass_field() {
    local input=$1 index ch
    PGPASS_FIELD= PGPASS_RAW= PGPASS_REST= PGPASS_DELIMITED=false
    for ((index=0; index<${#input}; index++)); do
        ch=${input:index:1}
        if [[ $ch == : ]]; then
            PGPASS_REST=${input:index+1}
            PGPASS_DELIMITED=true
            return 0
        fi
        PGPASS_RAW+=$ch
        if [[ $ch == '\' && $((index+1)) -lt ${#input} ]]; then
            index=$((index+1))
            ch=${input:index:1}
            PGPASS_RAW+=$ch
        fi
        PGPASS_FIELD+=$ch
    done
}

read_password_file() {
    local path=$1 mode line rest expected
    [[ -f $path ]] || return 1
    mode=$(stat -c '%a' "$path" 2>/dev/null) || mode=$(stat -f '%Lp' "$path") || return 1
    [[ $mode =~ ^[0-7]+$ ]] || return 1
    if (( (8#$mode & 077) != 0 )); then
        echo "Error: password file has group or world permissions; use chmod 600" >&2
        return 1
    fi
    while IFS= read -r line || [[ -n $line ]]; do
        while [[ $line == *$'\r' ]]; do line=${line%$'\r'}; done
        [[ -n $line && $line != \#* ]] || continue
        rest=$line
        for expected in "$DBHOST" "$DBPORT" "$DBNAME" "$DBUSER"; do
            pgpass_field "$rest"
            if [[ $PGPASS_DELIMITED != true || ( $PGPASS_RAW != '*' && $PGPASS_FIELD != "$expected" ) ]]; then
                continue 2
            fi
            rest=$PGPASS_REST
        done
        pgpass_field "$rest"
        PASSWORD=$PGPASS_FIELD
        return 0
    done < "$path"
    return 1
}

PASSWORD=${PGPASSWORD-}
if [[ -z $PASSWORD ]]; then
    if ! read_password_file "${PGPASSFILE-${HOME}/.pgpass}"; then
        echo "Error: no usable password-file entry for the requested connection; set PGPASSWORD or PGPASSFILE" >&2
        exit 1
    fi
fi

# SQL values and identifiers have different quoting rules.
PASSWORD_SQL=${PASSWORD//\'/\'\'}
DBUSER_SQL=${DBUSER//\'/\'\'}
DBNAME_SQL=${DBNAME//\'/\'\'}
DBUSER_IDENT=${DBUSER//\"/\"\"}
DBNAME_IDENT=${DBNAME//\"/\"\"}


PSQL_ADMIN=(docker exec -i "$CONTAINER" psql -U postgres -v ON_ERROR_STOP=1)

echo "==> Creating role '${DBUSER}' and database '${DBNAME}'..."

"${PSQL_ADMIN[@]}" -d postgres <<SQL
SET standard_conforming_strings = on;
SELECT format('CREATE ROLE %I WITH LOGIN', '${DBUSER_SQL}')
WHERE NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = '${DBUSER_SQL}')\gexec

ALTER ROLE "${DBUSER_IDENT}" PASSWORD '${PASSWORD_SQL}';

SELECT format('CREATE DATABASE %I OWNER %I', '${DBNAME_SQL}', '${DBUSER_SQL}')
WHERE NOT EXISTS (SELECT 1 FROM pg_database WHERE datname = '${DBNAME_SQL}')\gexec

GRANT ALL PRIVILEGES ON DATABASE "${DBNAME_IDENT}" TO "${DBUSER_IDENT}";
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
GRANT USAGE, CREATE ON SCHEMA public TO "${DBUSER_IDENT}";
ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON TABLES    TO "${DBUSER_IDENT}";
ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON SEQUENCES TO "${DBUSER_IDENT}";
GRANT USAGE                                          ON SCHEMA ag_catalog TO "${DBUSER_IDENT}";
GRANT SELECT, INSERT, UPDATE, DELETE ON ALL TABLES   IN SCHEMA ag_catalog TO "${DBUSER_IDENT}";
GRANT EXECUTE ON ALL FUNCTIONS                       IN SCHEMA ag_catalog TO "${DBUSER_IDENT}";
GRANT USAGE   ON ALL SEQUENCES                       IN SCHEMA ag_catalog TO "${DBUSER_IDENT}";
SQL

echo "==> Done."
echo "    Verify: psql -h ${DBHOST} -p ${DBPORT} -U ${DBUSER} -d ${DBNAME} -c '\\conninfo'"

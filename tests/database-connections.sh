#!/usr/bin/env bash
# Real authentication/TLS checks using only labelled disposable containers.
set -euo pipefail
umask 077
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
[[ $# == 1 ]] || { echo 'usage: database-connections.sh /path/to/connection_probe' >&2; exit 2; }
probe_bin=$(cd "$(dirname "$1")" && printf '%s/%s\n' "$PWD" "$(basename "$1")")
app=muninn; [[ ! -d $repo/mimir-setup ]] || app=mimir
root=$(mktemp -d "/tmp/$app-connection-tests-XXXXXXXX")
root=$(cd "$root" && pwd -P)
printf 'Artifacts: %s\n' "$root"
image=${PG_TEST_IMAGE:-sha256:79fb863620098b1e443338075bb65f6775130cbcb381f115d4272719256e334d}
clean_env=()
while IFS= read -r -d '' entry; do key=${entry%%=*}; [[ $key == PG* ]] || clean_env+=("$entry"); done < <(env -0)
run_env=() run_input=/dev/null containers=()
count=0 passed=0
run() {
    local status stem
    count=$((count+1)); printf -v stem '%s/%04d' "$root" "$count"
    jq -n --args '$ARGS.positional' -- "$@" > "$stem.command.json" || return 1
    if timeout 60 env -i "${clean_env[@]}" "${run_env[@]}" "$@" < "$run_input" > "$stem.stdout" 2> "$stem.stderr"; then status=0; else status=$?; fi
    printf '%s\n' "$status" > "$stem.exit"
    last_out=$stem.stdout; last_err=$stem.stderr
    run_env=(); run_input=/dev/null
    return "$status"
}
must() { run "$@" || { echo "Command $count failed; inspect retained output" >&2; return 1; }; }
sql() {
    local container=$1 statement=$2
    printf '%s\n' "$statement" > "$root/.sql-input"
    run_input=$root/.sql-input
    must docker exec -i "$container" psql -X -U postgres -v ON_ERROR_STOP=1
    rm -f "$root/.sql-input"
}
migration_sql() {
    printf '%s\n' "$1" > "$root/.sql-input"
    run_input=$root/.sql-input
    must docker exec -i "$plain" psql -X -tA -U postgres -d "$migration_db" -v ON_ERROR_STOP=1
    sql_result=$(<"$last_out")
    rm -f "$root/.sql-input"
}
cleanup() {
    local status=$? name owner
    trap - EXIT INT TERM
    for name in "${containers[@]}"; do
        if run docker inspect --format '{{index .Config.Labels "connection-test"}}' "$name"; then
            owner=$(<"$last_out")
            if [[ $owner == "$root" ]]; then
                run docker logs "$name" || true
                run docker rm -f "$name" || status=1
            else
                echo "Cleanup identity mismatch: $name" >&2; status=1
            fi
        else
            echo "Cannot verify cleanup identity: $name" >&2; status=1
        fi
    done
    find "$root" -maxdepth 1 -type f \( -name '*.key' -o -name '*.csr' -o -name '*.srl' -o -name config.toml -o -name '*passwords' -o -name .sql-input \) -delete
    chmod 700 "$root"
    exit "$status"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
certificate() {
    local name=$1 ca=${2-} extensions=${3-}
    must openssl req -new -newkey rsa:2048 -nodes -keyout "$root/$name.key" -out "$root/$name.csr" -subj "/CN=$name"
    local -a args=(openssl x509 -req -in "$root/$name.csr" -out "$root/$name.crt" -days 1)
    if [[ -n $ca ]]; then args+=(-CA "$root/$ca.crt" -CAkey "$root/$ca.key" -CAcreateserial); else args+=(-signkey "$root/$name.key"); fi
    if [[ -n $extensions ]]; then printf '%s\n' "$extensions" > "$root/$name.ext"; args+=(-extfile "$root/$name.ext"); fi
    must "${args[@]}"
    # These are disposable fixture certificates. PostgreSQL runs under a
    # different UID and must be able to read the mounted certificate files.
    chmod 644 "$root/$name.key" "$root/$name.crt"
}
start() {
    local tls=$1 tls_only=${2:-false} name hba script address
    name=$app-connection-$(openssl rand -hex 6)
    hba='local all all trust'
    [[ $tls != true ]] || hba+=$'\nhostssl all certuser all cert clientcert=verify-full'
    [[ $tls_only != true ]] || hba+=$'\nhostnossl all all all reject'
    hba+=$'\nhost all all all scram-sha-256'
    printf '%s\n' "$hba" > "$root/$name.hba"; chmod 644 "$root/$name.hba"
    script=$(cat <<EOF
set -eu
initdb -D /var/lib/postgresql/data --username=postgres --auth-local=trust --auth-host=scram-sha-256
cp /fixture/$name.hba /var/lib/postgresql/data/pg_hba.conf
cp /fixture/server.key /var/lib/postgresql/data/server.key
chmod 600 /var/lib/postgresql/data/server.key
exec postgres -D /var/lib/postgresql/data -c listen_addresses='*' -c shared_preload_libraries=age -c unix_socket_directories=/var/lib/postgresql/data -c search_path=public,ag_catalog -c ssl=$([[ $tls == true ]] && echo on || echo off) -c ssl_cert_file=/fixture/server.crt -c ssl_key_file=/var/lib/postgresql/data/server.key -c ssl_ca_file=/fixture/ca.crt
EOF
)
    must docker create --name "$name" --label "connection-test=$root" --user 999:999 --memory 512m --tmpfs /var/lib/postgresql/data:rw,size=256m,uid=999,gid=999,mode=0700 \
        --publish 127.0.0.1::5432 --mount "type=bind,src=$root,dst=/fixture,readonly" --env PGHOST=/var/lib/postgresql/data --entrypoint /bin/bash "$image" -c "$script"
    containers+=("$name")
    must docker start "$name"
    for ((attempt=0; attempt<60; attempt++)); do if run docker exec "$name" pg_isready -U postgres; then break; fi; sleep 0.5; done
    ((attempt < 60)) || { run docker logs "$name" || true; echo 'Fixture did not start' >&2; return 1; }
    must docker port "$name" 5432/tcp
    address=$(<"$last_out"); [[ ${address%:*} == 127.0.0.1 ]]
    started_port=${address##*:}; started_container=$name
    sql "$name" 'CREATE EXTENSION age; CREATE EXTENSION vector; CREATE EXTENSION pgcrypto;'
}
escaped() { local v=$1; v=${v//\\/\\\\}; v=${v//:/\\:}; printf '%s' "$v"; }
password_file() {
    local name=$1 port=$2 password=$3 user=${4:-tester} db=${5:-postgres}
    printf '# ignored\ninvalid\nwrong:*:*:*:wrong\n%s:%s:%s:%s:%s\r\n*:*:*:*:wrong\n' \
        "$(escaped 127.0.0.1)" "$(escaped "$port")" "$(escaped "$db")" "$(escaped "$user")" "$(escaped "$password")" > "$root/$name"
    chmod 600 "$root/$name"
    password_path=$root/$name
}
probe() {
    local label=$1 port=$2 fields=$3 env_json=$4 ok=${5:-true} ssl=${6:-false} mode=${7:-query} user=${8:-tester} db=${9:-postgres} status=0 config
    config=$(jq -nc --argjson port "$port" --arg user "$user" --arg db "$db" --argjson fields "$fields" '{host:"127.0.0.1",port:$port,dbname:$db,user:$user,ssl_mode:"disable"} + $fields')
    { printf 'config_version = 1\n[logging]\ndirectory = %s\n[database]\n' "$(jq -Rn --arg v "$root/logs" '$v')"; jq -r 'to_entries[] | "\(.key) = \(.value|tojson)"' <<< "$config"; } > "$root/config.toml"
    chmod 600 "$root/config.toml"
    run_env=("PGPASSFILE=$root/absent")
    while IFS= read -r line; do run_env+=("$line"); done < <(jq -r 'to_entries[] | "\(.key)=\(.value)"' <<< "$env_json")
    run "$probe_bin" "$root/config.toml" "$mode" || status=$?
    if [[ $ok == true ]]; then
        ((status == 0)) || { echo "$label: unexpected failure, command $count" >&2; return 1; }
        grep -Fq "ssl=$ssl" "$last_out" || { echo "$label: wrong transport" >&2; return 1; }
    else
        ((status != 0)) || { echo "$label: unexpected success" >&2; return 1; }
    fi
    if grep -Fq -- "$SECRET" "$last_out" "$last_err"; then echo "$label: password exposed" >&2; return 1; fi
    passed=$((passed+1)); printf 'PASS %s\n' "$label"
}

SECRET='  '\''quoted" : slash\ пароль $()  '
certificate ca '' $'basicConstraints=critical,CA:TRUE\nkeyUsage=critical,keyCertSign,cRLSign'
certificate otherca '' $'basicConstraints=critical,CA:TRUE\nkeyUsage=critical,keyCertSign,cRLSign'
certificate server ca $'subjectAltName=DNS:localhost\nextendedKeyUsage=serverAuth'
certificate certuser ca 'extendedKeyUsage=clientAuth'
chmod 755 "$root"
start false; plain=$started_container; port=$started_port
secret_sql=${SECRET//\'/\'\'}
sql "$plain" "CREATE ROLE tester LOGIN PASSWORD '$secret_sql';"
password_file passwords "$port" "$SECRET"; file=$password_path
probe 'literal config password beats environment and file' "$port" "$(jq -nc --arg p "$SECRET" '{password:$p,pgpassfile:"/absent"}')" '{"PGPASSWORD":"wrong"}'
probe 'environment beats file' "$port" '{"pgpassfile":"/absent"}' "$(jq -nc --arg p "$SECRET" '{PGPASSWORD:$p}')"
probe 'configured file beats environment file' "$port" "$(jq -nc --arg f "$file" '{pgpassfile:$f}')" '{"PGPASSFILE":"/absent","PGPASSWORD":""}'
probe 'PGPASSFILE with escapes and CRLF' "$port" '{}' "$(jq -nc --arg f "$file" '{PGPASSFILE:$f}')"
probe 'explicit missing file does not fall back' "$port" '{"pgpassfile":"/absent"}' "$(jq -nc --arg f "$file" '{PGPASSFILE:$f}')" false
probe 'empty configured password overrides environment' "$port" '{"password":""}' "$(jq -nc --arg p "$SECRET" '{PGPASSWORD:$p}')" false
chmod 644 "$file"; probe 'insecure password file ignored' "$port" "$(jq -nc --arg f "$file" '{pgpassfile:$f}')" '{}' false; chmod 600 "$file"
probe 'prefer accepts non-TLS server' "$port" "$(jq -nc --arg p "$SECRET" '{password:$p,ssl_mode:"prefer"}')" '{}'
for mode in require verify-ca verify-full; do probe "$mode refuses non-TLS server" "$port" "$(jq -nc --arg p "$SECRET" --arg m "$mode" '{password:$p,ssl_mode:$m}')" '{}' false; done
role='test'\''"role:slash\'; database='test'\''"db:slash\'
password_file setup-passwords "$port" "$SECRET" "$role" "$database"; setup_file=$password_path
setup=(bash "$repo/$app-setup/create-db-user.sh" --container "$plain" --host 127.0.0.1 --port "$port" --user "$role" --db "$database")
run_env=("PGPASSFILE=$setup_file"); must "${setup[@]}"
probe 'setup file grammar and SQL quoting' "$port" "$(jq -nc --arg p "$SECRET" '{password:$p}')" '{}' true false query "$role" "$database"
run_env=("PGPASSWORD=$SECRET" 'PGPASSFILE=/absent'); must "${setup[@]}"
probe 'setup PGPASSWORD and idempotence' "$port" "$(jq -nc --arg p "$SECRET" '{password:$p}')" '{}' true false query "$role" "$database"

migration_db=mimir_connection_migrations
run_env=("PGPASSWORD=$SECRET"); must bash "$repo/mimir-setup/create-db-user.sh" --container "$plain" --host 127.0.0.1 --port "$port" --user tester --db "$migration_db"
fields=$(jq -nc --arg p "$SECRET" '{password:$p}')
probe 'fresh migration with Kryzhen 2' "$port" "$fields" '{}' true false migrate tester "$migration_db"
migration_sql 'SELECT json_agg(row_to_json(m) ORDER BY name) FROM mallard.applied_migrations m;'; before=$sql_result
migration_sql "CREATE TABLE public.upgrade_sentinel(value text); INSERT INTO public.upgrade_sentinel VALUES ('preserved');"
migration_sql 'DROP TABLE mallard.applied_migration_schemas; DROP TABLE mallard.migrator_version; DROP INDEX mallard.applied_migrations_name_key;'
probe 'upgrade existing Kryzhen history' "$port" "$fields" '{}' true false migrate tester "$migration_db"
migration_sql 'SELECT json_agg(row_to_json(m) ORDER BY name) FROM mallard.applied_migrations m;'; [[ $sql_result == "$before" ]]
migration_sql 'SELECT value FROM public.upgrade_sentinel;'; [[ $sql_result == preserved ]]
migration_sql "SELECT bool_and(schema='public') AND count(*)=(SELECT count(*) FROM mallard.applied_migrations) FROM mallard.applied_migration_schemas;"; [[ $sql_result == t ]]
probe 'migration upgrade is idempotent' "$port" "$fields" '{}' true false migrate tester "$migration_db"
migration_sql 'SELECT json_agg(row_to_json(m) ORDER BY name) FROM mallard.applied_migrations m;'; [[ $sql_result == "$before" ]]
receipt=$repo/crates/core/migrations/.kryzhen-import-receipt.json
names=$(jq -r --arg q "'" '.migrations | map($q + (.kryzhen_name | gsub($q; $q+$q)) + $q) | join(",")' "$receipt")
migration_sql "CREATE TABLE public._sqlx_migrations(version bigint PRIMARY KEY, description text NOT NULL, installed_on timestamptz NOT NULL DEFAULT now(), success boolean NOT NULL, checksum bytea NOT NULL, execution_time bigint NOT NULL); DELETE FROM mallard.applied_migration_schemas WHERE migration_name IN ($names); DELETE FROM mallard.applied_migrations WHERE name IN ($names);"
while IFS= read -r row; do
    version=$(jq -r '.version' <<< "$row"); description=$(jq -r '.sqlx_description' <<< "$row"); checksum=$(jq -r '.sqlx_checksum_hex' <<< "$row")
    migration_sql "INSERT INTO public._sqlx_migrations(version,description,success,checksum,execution_time) VALUES ($version,'$description',true,decode('$checksum','hex'),0);"
done < <(jq -c '.migrations[]' "$receipt")
probe 'import historical sqlx receipt with Kryzhen 2' "$port" "$fields" '{}' true false migrate tester "$migration_db"
migration_sql "SELECT to_regclass('public._sqlx_migrations') IS NULL;"; [[ $sql_result == t ]]
migration_sql "SELECT bool_and(schema='public') AND count(*)=(SELECT count(*) FROM mallard.applied_migrations) FROM mallard.applied_migration_schemas;"; [[ $sql_result == t ]]
migration_sql 'SELECT json_agg(row_to_json(m) ORDER BY name) FROM mallard.applied_migrations m;'; before=$sql_result
probe 'sqlx import is idempotent' "$port" "$fields" '{}' true false migrate tester "$migration_db"
migration_sql 'SELECT json_agg(row_to_json(m) ORDER BY name) FROM mallard.applied_migrations m;'; [[ $sql_result == "$before" ]]
migration_sql "UPDATE mallard.applied_migrations SET checksum=decode(repeat('00',32),'hex') WHERE name=(SELECT name FROM mallard.applied_migrations ORDER BY name LIMIT 1);"
migration_sql 'SELECT json_agg(row_to_json(m) ORDER BY name) FROM mallard.applied_migrations m;'; tampered=$sql_result
probe 'changed migration checksum is rejected' "$port" "$fields" '{}' false false migrate tester "$migration_db"
migration_sql 'SELECT json_agg(row_to_json(m) ORDER BY name) FROM mallard.applied_migrations m;'; [[ $sql_result == "$tampered" ]]
migration_sql 'SELECT value FROM public.upgrade_sentinel;'; [[ $sql_result == preserved ]]

start true true; secure=$started_container; tls_port=$started_port
sql "$secure" "CREATE ROLE tester LOGIN PASSWORD '$secret_sql'; CREATE ROLE certuser LOGIN;"
ca=$root/ca.crt; base=$(jq -nc --arg p "$SECRET" '{password:$p,ssl_mode:"require"}')
probe 'require encrypted' "$tls_port" "$base" '{}' true true
probe 'prefer negotiates TLS' "$tls_port" "$(jq -c '.ssl_mode="prefer"' <<< "$base")" '{}' true true
if [[ $app == muninn ]]; then
    probe 'allow retries TLS after plaintext rejection' "$tls_port" "$(jq -c '.ssl_mode="allow"' <<< "$base")" '{}' true true
    probe 'allow prefers plaintext' "$port" "$(jq -c '.ssl_mode="allow"' <<< "$base")" '{}'
fi
probe 'verify-ca ignores hostname but validates trust' "$tls_port" "$(jq -c --arg ca "$ca" '.ssl_mode="verify-ca" | .ssl_root_cert=$ca' <<< "$base")" '{}' true true
probe 'verify-full rejects wrong hostname' "$tls_port" "$(jq -c --arg ca "$ca" '.ssl_mode="verify-full" | .ssl_root_cert=$ca' <<< "$base")" '{}' false
full=$(jq -c --arg ca "$ca" '.host="localhost" | .ssl_mode="verify-full" | .ssl_root_cert=$ca' <<< "$base")
probe 'verify-full checks trusted hostname' "$tls_port" "$full" '{}' true true
for mode in verify-ca verify-full; do probe "$mode rejects untrusted CA" "$tls_port" "$(jq -c --arg m "$mode" --arg ca "$root/otherca.crt" '.ssl_mode=$m | .ssl_root_cert=$ca' <<< "$full")" '{}' false; done
cat "$root/otherca.crt" "$root/ca.crt" > "$root/bundle.crt"
probe 'multiple root certificates' "$tls_port" "$(jq -c --arg ca "$root/bundle.crt" '.ssl_root_cert=$ca' <<< "$full")" '{}' true true
identity=$(jq -c --arg crt "$root/certuser.crt" --arg key "$root/certuser.key" 'del(.password) | .ssl_client_cert=$crt | .ssl_client_key=$key' <<< "$full")
probe 'mutual TLS client identity' "$tls_port" "$identity" '{}' true true query certuser
probe 'missing client identity rejected by server' "$tls_port" "$full" '{}' false false query certuser
probe 'partial client identity rejected' "$tls_port" "$(jq -c --arg crt "$root/certuser.crt" '.ssl_client_cert=$crt' <<< "$full")" '{}' false
probe 'mismatched client key rejected' "$tls_port" "$(jq -c --arg key "$root/server.key" '.ssl_client_key=$key' <<< "$identity")" '{}' false false query certuser
probe 'disabled TLS with certificate options rejected' "$port" "$(jq -nc --arg p "$SECRET" --arg ca "$ca" '{password:$p,ssl_root_cert:$ca}')" '{}' false
if [[ $app == muninn ]]; then
    for mode in listener lock preparation; do
        probe "$mode including cancellation uses TLS" "$tls_port" "$full" '{}' true true "$mode"
        probe "$mode supports plaintext" "$port" "$fields" '{}' true false "$mode"
    done
fi
printf 'PASS: %s real connection checks\n' "$passed"

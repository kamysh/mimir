#!/usr/bin/env bash
# Release checks in a private environment with one owned, disposable database.
set -euo pipefail
umask 077
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
image=sha256:79fb863620098b1e443338075bb65f6775130cbcb381f115d4272719256e334d
label=mimir.isolated-test
selected=all
usage='usage: test-isolated.sh [--check all|format|lint|workspace|fixtures|formal]'
if [[ $# == 1 && ( $1 == -h || $1 == --help ) ]]; then printf '%s\n' "$usage"; exit 0; fi
if [[ $# == 1 && $1 == --check=* ]]; then selected=${1#--check=}
elif (($#)); then
    [[ $# == 2 && $1 == --check ]] || { echo "$usage" >&2; exit 2; }
    selected=$2
fi
case $selected in all|format|lint|workspace|fixtures|formal) ;; *) echo 'Unknown check' >&2; exit 2 ;; esac
root=$(mktemp -d /tmp/mimir-tests-XXXXXXXX)
root=$(cd "$root" && pwd -P)
printf 'Isolated test artifacts: %s\n' "$root"
token=$(openssl rand -hex 16)
container= active= count=0 run_cwd=$repo
mkdir -m 700 "$root"/{home,config,state,cache,scratch,bin}

# Only explicitly allowed build settings are inherited; credentials, application
# configuration and provider API keys never enter a test subprocess.
source "$repo/scripts/lib/isolated-environment.sh"
isolated_environment "$root"
for name in mimir mimir-mcp; do
    printf '#!/bin/sh\nexec %q "$@"\n' "$root/target/debug/$name" > "$root/bin/$name"
    chmod 700 "$root/bin/$name"
done
for name in codex claude; do
    printf '#!/bin/sh\necho "Live model harness forbidden in release tests" >&2\nexit 78\n' > "$root/bin/$name"
    chmod 700 "$root/bin/$name"
done
for name in python python3; do
    printf '#!/bin/sh\necho "Python is forbidden in these checks" >&2\nexit 78\n' > "$root/bin/$name"
    chmod 700 "$root/bin/$name"
done

run() {
    local name=$1; shift
    local stem status
    count=$((count+1)); printf -v stem '%s/%03d-%s' "$root" "$count" "$name"
    printf 'Check: %s; log: %s.log\n' "$name" "$stem"
    jq -n --args '$ARGS.positional' -- "$@" > "$stem.command.json" || return 1
    : > "$stem.stdout"; : > "$stem.stderr"
    set -m
    (cd "${run_cwd:-$repo}"; exec env -i "${child_env[@]}" "$@") < /dev/null > "$stem.stdout" 2> "$stem.stderr" &
    active=$!
    if wait "$active"; then status=0; else status=$?; fi
    active=
    set +m
    printf '%s\n' "$status" > "$stem.exit"
    { printf '.stdout:\n'; cat "$stem.stdout"; printf '.stderr:\n'; cat "$stem.stderr"; } > "$stem.log"
    last_stdout=$stem.stdout
    return "$status"
}

cleanup() {
    local status=$? info
    trap - EXIT INT TERM
    if [[ -n $active ]]; then
        kill -TERM -- "-$active" 2>/dev/null || true
        for ((i=0; i<100; i++)); do kill -0 "$active" 2>/dev/null || break; sleep 0.05; done
        kill -KILL -- "-$active" 2>/dev/null || true
        wait "$active" 2>/dev/null || true
        active=
    fi
    if [[ -n $container ]]; then
        run database-final-logs docker logs "$container" || true
        if run database-ownership docker inspect "$container"; then
            info=$(<"$last_stdout")
            if owned_container "$container" "$label" "$token" "$info"; then
                if run remove-owned-database docker rm --force "$container"; then container=; else status=1; fi
            else
                echo 'Refusing cleanup of a container this run does not own' >&2; status=1
            fi
        else
            echo 'Could not verify database ownership; container was not removed' >&2; status=1
        fi
    fi
    jq -n --arg check "$selected" --argjson code "$status" --argjson removed "$([[ -z $container ]] && echo true || echo false)" \
        '{check:$check,exit_code:$code,container_removed:$removed}' > "$root/result.json"
    exit "$status"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

fixture() {
    local name script address port db user password binary mcp text
    name=mimir-test-${token:0:16}
    script=$(cat <<'SH'
set -eu
initdb -D /var/lib/postgresql/data --username=postgres --auth-local=trust --auth-host=scram-sha-256
printf 'local all all trust\nhost all postgres all reject\nhost all all all scram-sha-256\n' > /var/lib/postgresql/data/pg_hba.conf
exec postgres -D /var/lib/postgresql/data -c listen_addresses='*' -c shared_preload_libraries=age -c search_path=public,ag_catalog -c unix_socket_directories=/var/lib/postgresql/data
SH
)
    run create-database-container docker create --name "$name" --label "$label=$token" --user 999:999 --memory 1g --cpus 2 \
        --tmpfs /var/lib/postgresql/data:rw,size=512m,uid=999,gid=999,mode=0700 --publish 127.0.0.1::5432 \
        --env PGHOST=/var/lib/postgresql/data --entrypoint /bin/bash "$image" -c "$script"
    container=$(<"$last_stdout")
    [[ $container =~ ^[0-9a-f]{64}$ ]] || { echo 'Docker did not return a container identity' >&2; return 1; }
    run start-database-container docker start "$container"
    for ((attempt=0; attempt<60; attempt++)); do
        if run database-ready docker exec "$container" pg_isready -U postgres; then break; fi
        sleep 0.5
    done
    ((attempt < 60)) || { echo 'Isolated PostgreSQL did not become ready' >&2; return 1; }
    run database-port docker port "$container" 5432/tcp
    address=$(<"$last_stdout"); port=${address##*:}; address=${address%:*}
    [[ $address == 127.0.0.1 && $port =~ ^[0-9]+$ && $port -gt 0 && $port -lt 65536 ]]
    db=mimir_learning_test_${token:0:16}; user=mimir_test_${token:0:16}; password=$(openssl rand -hex 32)
    printf '127.0.0.1:%s:%s:%s:%s\n' "$port" "$db" "$user" "$password" > "$root/test.pgpass"
    child_env+=("MIMIR_HOST=127.0.0.1" "MIMIR_PORT=$port" "MIMIR_DBNAME=$db" "MIMIR_USER=$user" "PGPASSFILE=$root/test.pgpass")
    run database-role-and-extensions bash "$repo/mimir-setup/create-db-user.sh" --container "$container" --host 127.0.0.1 --port "$port" --user "$user" --db "$db"
    binary=$root/target/debug/mimir; mcp=$root/target/debug/mimir-mcp
    jq -n --arg root "$root" --arg token "$token" --arg container "$container" --arg db "$db" --arg user "$user" --argjson port "$port" --arg mimir "$binary" --arg mcp "$mcp" \
        '{root:$root,token:$token,container:$container,database:$db,user:$user,port:$port,mimir:$mimir,mcp:$mcp}' > "$root/fixture.json"
    child_env+=("MIMIR_TEST_ROOT=$root" "MIMIR_TEST_TOKEN=$token" "MIMIR_CONFIG=$root/config.toml" "MIMIR_TEST_CONFIG=$root/config.toml" "MIMIR_TEST_MIMIR=$binary" "MIMIR_TEST_MCP=$mcp")
    {
        printf 'config_version = 1\n[logging]\ndirectory = %s\n[database]\n' "$(jq -Rn --arg v "$root/logs" '$v')"
        printf 'host = "127.0.0.1"\nport = %s\ndbname = %s\nuser = %s\npgpassfile = %s\nssl_mode = "disable"\n' "$port" \
            "$(jq -Rn --arg v "$db" '$v')" "$(jq -Rn --arg v "$user" '$v')" "$(jq -Rn --arg v "$root/test.pgpass" '$v')"
    } > "$root/database.toml"
    { cat "$root/database.toml"; printf '\n[judge]\nbatch_size = 1\nmcp_command = %s\n\n[llm]\nbackend = "command"\nmodel = "fixture"\ncommand = "/bin/true"\n[email]\nenabled = false\n' "$(jq -Rn --arg v "$mcp" '$v')"; } > "$root/config.toml"
    run fixture-contract bash "$repo/tests/support/fixture.sh" check
}

run isolation-regressions bash "$repo/tests/test-isolated-runner.sh"
if [[ $selected == all ]]; then run release-source-regressions bash "$repo/tests/test-release-source.sh"; fi
if [[ $selected == all || $selected == format ]]; then
    run format cargo fmt --all -- --check
    run qa-format cargo fmt --manifest-path "$repo/tools/qa/Cargo.toml" -- --check
fi
if [[ $selected == all || $selected == lint ]]; then
    run lint cargo clippy --workspace --all-targets --locked --offline -- -D warnings
    run qa-lint cargo clippy --manifest-path "$repo/tools/qa/Cargo.toml" --locked --offline -- -D warnings
fi
if [[ $selected == all || $selected == workspace || $selected == fixtures ]]; then
    fixture
    run build-snapshot-binaries cargo build --workspace --locked --offline
    run initialize-test-schema "$root/target/debug/mimir" stats
fi
if [[ $selected == all || $selected == workspace ]]; then
    run workspace-tests cargo test --workspace --all-targets --locked --offline -- --test-threads=1
    mapfile -t binaries < <(find "$root/target/debug/deps" -maxdepth 1 -type f -executable -name 'store_integration-*')
    ((${#binaries[@]} == 1)) || { echo 'Expected one store integration test binary' >&2; exit 1; }
    run refuse-conflicting-database cargo run --quiet --offline --manifest-path "$repo/tools/qa/Cargo.toml" -- decoy-guard "${binaries[0]}"
    jq -n '{rejected_before_connect:true,connection_attempts:0}' > "$root/connection-guard.json"
    run documentation-tests cargo test --workspace --doc --locked --offline
fi
if [[ $selected == all || $selected == fixtures ]]; then
    run judge-adapter-fixtures bash "$repo/tests/judge-adapters.sh"
    run evaluator-tests cargo test --manifest-path "$repo/tests/eval/Cargo.toml" --locked --offline
    run learning-comparator-fixture bash "$repo/tests/eval/learning-compare-fixture.sh"
fi
if [[ $selected == all || $selected == formal ]]; then
    run formal-source-regressions cargo test --manifest-path "$repo/tools/qa/Cargo.toml" --locked --offline
    run formal-inventory bash "$repo/scripts/formal/check-coverage.sh"
    run_cwd=$repo/spec run aggregate-formal-specification agda Mimir.agda
fi

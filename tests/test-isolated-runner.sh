#!/usr/bin/env bash
set -euo pipefail
umask 077
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
fixture=$repo/tests/support/fixture.sh
root=$(mktemp -d "${TMPDIR:-/tmp}/mimir-fixture-test-XXXXXXXX")
root=$(cd "$root" && pwd -P)
cleanup() { status=$?; if ((status == 0)); then rm -rf -- "$root"; else printf 'Fixture failure evidence: %s\n' "$root" >&2; fi; }
trap cleanup EXIT
mkdir -p "$root/target/debug"
export MIMIR_TEST_ROOT=$root MIMIR_TEST_TOKEN=owned-fixture MIMIR_HOST=127.0.0.1 MIMIR_PORT=43217
export MIMIR_DBNAME=mimir_learning_test_owned MIMIR_USER=mimir_test_owned
export MIMIR_CONFIG=$root/config.toml MIMIR_TEST_CONFIG=$root/config.toml PGPASSFILE=$root/test.pgpass
export MIMIR_TEST_MIMIR=$root/target/debug/mimir MIMIR_TEST_MCP=$root/target/debug/mimir-mcp
unset PGPASSWORD PGSERVICE PGSERVICEFILE DATABASE_URL || true
jq -n --arg root "$root" --arg token "$MIMIR_TEST_TOKEN" --arg mimir "$MIMIR_TEST_MIMIR" --arg mcp "$MIMIR_TEST_MCP" \
    '{root:$root,token:$token,port:43217,database:"mimir_learning_test_owned",user:"mimir_test_owned",mimir:$mimir,mcp:$mcp}' > "$root/fixture.json"
cat > "$root/config.toml" <<EOF
config_version = 1
[database]
host = "127.0.0.1"
port = 43217
dbname = "mimir_learning_test_owned"
user = "mimir_test_owned"
pgpassfile = "$root/test.pgpass"
EOF
cp "$root/config.toml" "$root/database.toml"
printf 'fixture-only\n' > "$root/test.pgpass"
cp "$root/config.toml" "$root/original.toml"
cp "$root/fixture.json" "$root/original.json"
counter=0
run() {
    counter=$((counter+1))
    if "$@" > "$root/$counter.stdout" 2> "$root/$counter.stderr"; then return 0; else return $?; fi
}
refused() { if run "$@"; then echo "Expected refusal: $*" >&2; exit 1; fi; }

run bash "$fixture" check
run bash "$fixture" config "$root/generated.toml" --backend codex --model fixture-a
rg -q '^reasoning_effort = "high"$' "$root/generated.toml"
rg -q '^model = "fixture-a"$' "$root/generated.toml"
rg -q '^enabled = false$' "$root/generated.toml"
refused bash "$fixture" config "$root/invalid.toml" --backend codex --command /fixture/custom
refused bash "$fixture" config "$root/generated.toml" --backend codex
refused env -u MIMIR_TEST_ROOT bash "$fixture" check
rg -q 'missing fixture setting MIMIR_TEST_ROOT' "$root/$counter.stderr"
for pair in 'MIMIR_HOST=deployment' 'MIMIR_PORT=5450' 'MIMIR_DBNAME=mimir' 'MIMIR_USER=mimir' 'MIMIR_CONFIG=/deployment/config.toml' 'PGPASSFILE=/deployment/.pgpass' 'MIMIR_TEST_MCP=/deployment/bin/mimir-mcp'; do
    refused env "$pair" bash "$fixture" check
done
for key in PGPASSWORD PGSERVICE PGSERVICEFILE DATABASE_URL; do refused env "$key=deployment" bash "$fixture" check; done
jq '.token="foreign"' "$root/original.json" > "$root/fixture.json"; refused bash "$fixture" check
jq '.database="mimir"' "$root/original.json" > "$root/fixture.json"; refused bash "$fixture" check
cp "$root/original.json" "$root/fixture.json"
sed '/config_version/d' "$root/original.toml" > "$root/config.toml"; refused bash "$fixture" check
sed 's/43217/5450/' "$root/original.toml" > "$root/config.toml"; refused bash "$fixture" check
{ cat "$root/original.toml"; printf 'password = "deployment"\n'; } > "$root/config.toml"; refused bash "$fixture" check
cp "$root/original.toml" "$root/config.toml"
chmod 644 "$root/test.pgpass"; refused bash "$fixture" check
rm "$root/test.pgpass"; ln -s /deployment/.pgpass "$root/test.pgpass"; refused bash "$fixture" check
rm "$root/test.pgpass"; printf 'fixture-only\n' > "$root/test.pgpass"

cat > "$MIMIR_TEST_MIMIR" <<'EOF'
#!/usr/bin/env bash
trap 'exit 0' TERM
sleep 0.3
printf ready > "$MIMIR_JUDGE_FIXTURE_READY_FILE"
sleep 0.1
printf 'fixture waiting\n' >&2
while :; do sleep 0.1; done
EOF
chmod 700 "$MIMIR_TEST_MIMIR"
export MIMIR_JUDGE_FIXTURE_READY_FILE=$root/child.ready
run bash "$fixture" cancel --ready "$root/child.ready" --stderr-ready 'fixture waiting' --report "$root/cancel.json" -- "$MIMIR_TEST_MIMIR"
[[ -f $root/child.ready && ! -s $root/cancel.json && $(<"$root/cancel.exit") == 0 ]]
rg -q 'fixture waiting' "$root/cancel.stderr"
mkdir "$root/dotted.dir"
export MIMIR_JUDGE_FIXTURE_READY_FILE=$root/dotted.dir/child.ready
run bash "$fixture" cancel --ready "$MIMIR_JUDGE_FIXTURE_READY_FILE" --stderr-ready 'fixture waiting' --report "$root/dotted.dir/report" -- "$MIMIR_TEST_MIMIR"
[[ -f $root/dotted.dir/report.stderr && $(<"$root/dotted.dir/report.exit") == 0 ]]
refused bash "$fixture" cancel --ready "$root/child.ready" --report "$root/other.json" -- /deployment/bin/mimir
refused bash "$fixture" config /tmp/mimir-fixture-escape.toml --backend codex

source "$repo/scripts/lib/isolated-environment.sh"
owned=$(jq -n '[{Id:"owned",Config:{Labels:{"mimir.isolated-test":"owned-token"}}}]')
owned_container owned mimir.isolated-test owned-token "$owned"
if owned_container owned mimir.isolated-test foreign-token "$owned"; then echo 'Foreign container accepted' >&2; exit 1; fi
env -i PATH="$PATH" HOME=/deployment MIMIR_CONFIG=/deployment/config PGPASSWORD=secret OPENAI_API_KEY=secret \
    bash -c 'source "$1"; isolated_environment "$2"; printf "%s\n" "${child_env[@]}"' _ "$repo/scripts/lib/isolated-environment.sh" "$root" > "$root/child-env"
if rg -q '^(MIMIR_CONFIG|PGPASSWORD|OPENAI_API_KEY)=' "$root/child-env"; then echo 'Deployment settings leaked' >&2; exit 1; fi
rg -q "^HOME=$root/home$" "$root/child-env"
printf 'Isolated fixture regression checks passed.\n'

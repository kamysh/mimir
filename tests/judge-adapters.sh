#!/usr/bin/env bash
set -euo pipefail

base=/var/tmp/mimir/step6
bin=/var/tmp/mimir/step5/target/debug/mimir
mcp=/var/tmp/mimir/step5/target/debug/mimir-mcp
mkdir -p "$base/bin"
rustc --edition=2021 tests/judge_process_fixture.rs -o "$base/judge-process-fixture"

cat > "$base/bin/fake-harness" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
kind="$(basename "$0")"
has() { local x; for x in "$@"; do [[ "$x" == "$needle" ]] && return 0; done; return 1; }
if [[ " $* " == *" --help "* ]]; then
    if [[ "${MIMIR_JUDGE_FIXTURE_MODE:-}" == incompatible ]]; then
        printf '%s\n' '--print'
        exit 0
    fi
    if [[ "$kind" == codex ]]; then
        printf '%s\n' '--ignore-user-config --ignore-rules --ephemeral --sandbox --output-schema --output-last-message --skip-git-repo-check --model --config'
    else
        printf '%s\n' '--print --restricted --tools --strict-mcp-config --mcp-config --disable-slash-commands --no-session-persistence --output-format --json-schema --permission-mode --permission-prompts --settings --model'
    fi
    exit 0
fi
if [[ "${MIMIR_JUDGE_FIXTURE_MODE:-}" == incompatible ]]; then
    touch /var/tmp/mimir/step6/incompatible-invoked-model
    exit 9
fi
if [[ "$kind" == codex ]]; then
    for needle in exec --ignore-user-config --ignore-rules --ephemeral --sandbox --output-schema --output-last-message --skip-git-repo-check --model; do has "$@"; done
    needle='model_reasoning_effort="high"'; has "$@"
elif [[ "$kind" == claude ]]; then
    for needle in --print --restricted --tools --strict-mcp-config --mcp-config --disable-slash-commands --no-session-persistence --output-format --json-schema --permission-mode --permission-prompts --settings --model; do has "$@"; done
fi
payload="$(cat)"
if jq -e '.history | length > 0' <<< "$payload" >/dev/null; then
    reply='{"calls":[]}'
else
    id="$(jq -er '.experience.experience.id' <<< "$payload")"
    revision="$(jq -er '.experience.revision' <<< "$payload")"
    review_revision="$(jq -er '.experience.review_revision' <<< "$payload")"
    call="$(jq -cn --arg id "$id" --argjson revision "$revision" --argjson review_revision "$review_revision" '{expected_review_revision:$review_revision,review:{experience_id:$id,experience_revision:$revision,reviewer:"untrusted-fixture",rationale:"fixture review of isolated observation"}}')"
    reply="$(jq -cn --arg call "$call" '{calls:[{name:"review_experience",arguments_json:$call}]}')"
fi
if [[ "$kind" == claude ]]; then
    jq -cn --argjson reply "$reply" '{is_error:false,structured_output:$reply}'
elif [[ "$kind" == codex ]]; then
    args=("$@")
    for ((i=0; i<${#args[@]}; i++)); do
        if [[ "${args[$i]}" == --output-last-message ]]; then
            printf '%s\n' "$reply" > "${args[$((i+1))]}"
            exit 0
        fi
    done
    exit 8
else
    printf '%s\n' "$reply"
fi
SH
chmod 700 "$base/bin/fake-harness"
ln -sf fake-harness "$base/bin/claude"
ln -sf fake-harness "$base/bin/codex"
ln -sf fake-harness "$base/bin/custom"

make_config() {
    local kind="$1" project="$2" config="$3" timeout="$4" command="${5:-}"
    cat > "$config" <<EOF
[database]
host = "127.0.0.1"
port = 32885
dbname = "mimir_learning_test_series"
user = "mimir_learning_test"
ssl_mode = "disable"
[judge]
project = "$project"
batch_size = 1
mcp_command = "$mcp"
[llm]
backend = "$kind"
model = "fixture-model"
timeout_seconds = $timeout
max_calls = 6
EOF
    if [[ "$kind" == codex ]]; then
        printf '%s\n' 'reasoning_effort = "high"' >> "$config"
    fi
    if [[ "$kind" == command ]]; then
        printf 'command = "%s"\n' "$command" >> "$config"
    fi
    chmod 600 "$config"
}

call_tool() {
    local config="$1" name="$2" args="$3"
    jq -cn --arg name "$name" --argjson args "$args" '{jsonrpc:"2.0",id:1,method:"tools/call",params:{name:$name,arguments:$args}}' | MIMIR_CONFIG="$config" "$mcp" | jq -er '.result.content[0].text | fromjson'
}

current_config=
current_project=
cleanup_current() {
    if [[ -n "$current_project" ]]; then
        call_tool "$current_config" delete_project "$(jq -nc --arg project "$current_project" '{project:$project}')" >/dev/null || true
    fi
}
trap cleanup_current EXIT

seed() {
    local config="$1" project="$2" id="$3"
    local args
    args="$(jq -cn --arg id "$id" --arg project "$project" '{expected_revision:0,experience:{id:$id,project:$project,context:"adapter fixture",action:"inspect result",outcome:"success",source:"tool_result",evidence:["disposable test observation"]}}')"
    call_tool "$config" record_experience "$args" | jq -e '.revision == 1' >/dev/null
}

for kind in claude-code codex command; do
    project="step6-${kind}-$(uuidgen)"
    id="$(uuidgen)"
    config="$base/${kind}.toml"
    current_config="$config"
    current_project="$project"
    make_config "$kind" "$project" "$config" 10 "$base/bin/custom"
    seed "$config" "$project" "$id"
    PATH="$base/bin:$PATH" "$bin" judge run --config "$config" --state-dir "$base/state-${kind}" | jq -e '.status == "complete" and .confirmed == 1' >/dev/null
    history="$(call_tool "$config" experience_history "$(jq -nc --arg id "$id" '{id:$id}')")"
    jq -e '.reviews[0].payload.reviewer == "mimir-judge"' <<< "$history" >/dev/null
    call_tool "$config" delete_project "$(jq -nc --arg project "$project" '{project:$project}')" >/dev/null
    current_project=
done

for mode in crash malformed oversized slow fork 'done'; do
    project="step6-${mode}-$(uuidgen)"
    id="$(uuidgen)"
    config="$base/${mode}.toml"
    current_config="$config"
    current_project="$project"
    make_config command "$project" "$config" 2 "$base/judge-process-fixture"
    seed "$config" "$project" "$id"
    export MIMIR_JUDGE_FIXTURE_MODE="$mode"
    export MIMIR_JUDGE_FIXTURE_PID_FILE="$base/descendant.pid"
    status=0
    "$bin" judge run --config "$config" --state-dir "$base/state-${mode}" > "$base/${mode}-report.json" || status=$?
    test "$status" -eq 3
    jq -e '.status == "blocked" and .confirmed == 0' "$base/${mode}-report.json" >/dev/null
    if [[ "$mode" == fork ]]; then
        pid="$(cat "$base/descendant.pid")"
        for _ in $(seq 1 30); do
            if [[ ! -e "/proc/$pid/stat" ]] || [[ "$(awk '{print $3}' "/proc/$pid/stat")" == Z ]]; then break; fi
            sleep 0.05
        done
        test ! -e "/proc/$pid/stat" || test "$(awk '{print $3}' "/proc/$pid/stat")" == Z
    fi
    unset MIMIR_JUDGE_FIXTURE_MODE MIMIR_JUDGE_FIXTURE_PID_FILE
    call_tool "$config" delete_project "$(jq -nc --arg project "$project" '{project:$project}')" >/dev/null
    current_project=
done

project="step6-incompatible-$(uuidgen)"
id="$(uuidgen)"
config="$base/incompatible.toml"
current_config="$config"
current_project="$project"
make_config claude-code "$project" "$config" 5
seed "$config" "$project" "$id"
rm -f "$base/incompatible-invoked-model"
status=0
MIMIR_JUDGE_FIXTURE_MODE=incompatible PATH="$base/bin:$PATH" "$bin" judge run --config "$config" --state-dir "$base/state-incompatible" > "$base/incompatible-report.json" || status=$?
test "$status" -eq 3
jq -e '.status == "blocked" and .confirmed == 0' "$base/incompatible-report.json" >/dev/null
test ! -e "$base/incompatible-invoked-model"
call_tool "$config" delete_project "$(jq -nc --arg project "$project" '{project:$project}')" >/dev/null
current_project=

project="step6-watch-$(uuidgen)"
id="$(uuidgen)"
config="$base/watch.toml"
current_config="$config"
current_project="$project"
make_config command "$project" "$config" 2 "$base/judge-process-fixture"
seed "$config" "$project" "$id"
status=0
MIMIR_JUDGE_FIXTURE_MODE=crash timeout 20s "$bin" judge watch --config "$config" \
    --state-dir "$base/state-watch" --interval-seconds 60 \
    --max-consecutive-failures 1 > "$base/watch-stdout" 2> "$base/watch-stderr" || status=$?
test "$status" -eq 124
test ! -s "$base/watch-stdout"
test "$(grep -c 'judge watch: incomplete run' "$base/watch-stderr")" -eq 1
"$bin" judge status --state-dir "$base/state-watch" \
    | jq -e '.report.status == "blocked" and .report.block_reason == "backend_error_or_timeout"' >/dev/null
call_tool "$config" pending_experiences "$(jq -nc --arg project "$project" '{project:$project,limit:1}')" | jq -e 'length == 1' >/dev/null
call_tool "$config" delete_project "$(jq -nc --arg project "$project" '{project:$project}')" >/dev/null
current_project=
printf 'judge adapter fixtures passed: Claude, Codex, custom, crash, malformed, oversized, timeout, descendant cleanup, false completion, incompatible flags, quiet watch retry\n'

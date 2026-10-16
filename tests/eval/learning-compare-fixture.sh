#!/usr/bin/env bash
# Local end-to-end check of the learning comparator. Fake Codex; disposable DB.
set -euo pipefail

base=/var/tmp/mimir/step11-fixture-$(uuidgen)
mkdir -m 700 -p "$base/bin"
result_dir=
cleanup() {
    if [[ -n "$result_dir" && "$result_dir" == /var/tmp/mimir/learning-compare-* ]]; then
        rm -rf -- "$result_dir"
    fi
    rm -rf -- "$base"
}
trap cleanup EXIT

cat > "$base/bin/codex" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [[ " $* " == *" --help "* ]]; then
    printf '%s\n' '--ignore-user-config --ignore-rules --ephemeral --sandbox --output-schema --output-last-message --skip-git-repo-check --model --config'
    exit 0
fi
answer=
model=
args=("$@")
for ((i=0; i<${#args[@]}; i++)); do
    case "${args[$i]}" in
        --output-last-message) answer="${args[$((i+1))]}" ;;
        --model) model="${args[$((i+1))]}" ;;
    esac
done
[[ -n "$answer" && "$model" == fixture-* ]]
printf '%s\n' "${args[@]}" | rg -q '^model_reasoning_effort="high"$'
payload="$(cat)"
if jq -e '.experience.experience.id' <<< "$payload" >/dev/null 2>&1; then
    if jq -e '.history | length > 0' <<< "$payload" >/dev/null; then
        reply='{"calls":[]}'
    else
        call="$(jq -cn --argjson p "$payload" '{experience_id:$p.experience.experience.id,experience_revision:$p.experience.revision,reviewer:"fixture",rationale:"isolated fixture review"}')"
        # The review token lives outside the review object.
        reply="$(jq -cn --argjson p "$payload" --arg call "$call" '{calls:[{name:"review_experience",arguments_json:({expected_review_revision:$p.experience.review_revision,review:($call|fromjson)}|tojson)}]}')"
    fi
else
    reply='{"related_action":"inspect loaded keyboard configuration","unrelated_action":"inspect disk usage and quota","used_belief_ids":[]}'
fi
printf '%s\n' "$reply" > "$answer"
SH
chmod 700 "$base/bin/codex"

mimir=/var/tmp/mimir/step5/target/debug/mimir
mcp=/var/tmp/mimir/step5/target/debug/mimir-mcp
for arm in a b; do
    cat > "$base/$arm.toml" <<EOF
[database]
host = "127.0.0.1"
port = 32885
dbname = "mimir_learning_test_series"
user = "mimir_learning_test"
ssl_mode = "disable"
[judge]
batch_size = 1
mcp_command = "$mcp"
[llm]
backend = "codex"
model = "fixture-$arm"
reasoning_effort = "high"
timeout_seconds = 15
max_calls = 3
[email]
enabled = false
EOF
    chmod 600 "$base/$arm.toml"
done

export PATH="$base/bin:$PATH"
eval_cmd="$(cd "$(dirname "$0")" && pwd)/eval"
preflight="$("$eval_cmd" learning-compare --arm-a "$base/a.toml" --arm-b "$base/b.toml" --mimir "$mimir" --mcp "$mcp")"
jq -e '.status == "preflight" and .selectors.arm_a.model == "fixture-a" and .selectors.arm_b.model == "fixture-b"' <<< "$preflight" >/dev/null

summary="$("$eval_cmd" learning-compare --arm-a "$base/a.toml" --arm-b "$base/b.toml" --mimir "$mimir" --mcp "$mcp" --live)"
result="$(jq -er '.results' <<< "$summary")"
result_dir="$(dirname "$result")"
jq -e '.status == "complete" and (.cases | length == 12) and all(.cases[]; (.result.safety | all(.[]; . == true)))' "$result" >/dev/null
printf '%s\n' 'learning comparator fixture passed: 12 isolated cases, selected models, receipts, actor decisions, cleanup'

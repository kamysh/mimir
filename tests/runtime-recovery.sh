#!/usr/bin/env bash
# Exercise correction and resubmission on one real MCP connection.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
bash "$repo/tests/support/fixture.sh" check
root=$(mktemp -d "$MIMIR_TEST_ROOT/recovery.XXXXXXXX")
{
    printf '\377\n'
    printf '%s\n' \
        '{"jsonrpc":"2.0","id":"missing","method":"tools/call","params":{"name":"get_belief","arguments":{}}}' \
        '{"jsonrpc":"2.0","id":"wrong","method":"tools/call","params":{"name":"list_beliefs","arguments":{"limti":1}}}' \
        '{"jsonrpc":"2.0","id":"zero","method":"tools/call","params":{"name":"pending_experiences","arguments":{"limit":0}}}' \
        '{"jsonrpc":"2.0","id":"corrected","method":"tools/call","params":{"name":"list_beliefs","arguments":{}}}'
} > "$root/requests.jsonl"
"$MIMIR_TEST_MCP" < "$root/requests.jsonl" > "$root/replies.jsonl" 2> "$root/stderr"
jq -se 'length == 5 and .[0].error.code == -32700' "$root/replies.jsonl" >/dev/null
for id in missing wrong zero; do
    jq -se --arg id "$id" 'map(select(.id == $id))[0].result.content[0].text | fromjson | .status == "needs_correction" and (.next_action | length > 0)' "$root/replies.jsonl" >/dev/null
done
jq -se 'map(select(.id == "corrected"))[0] | has("result") and (.result.content[0].text | fromjson | type == "array")' "$root/replies.jsonl" >/dev/null
printf 'Real MCP connection survived invalid input and accepted the corrected request.\n'
for binary in "$MIMIR_TEST_MIMIR" "$MIMIR_TEST_MCP"; do
    name=${binary##*/}
    printf '%s\n' '{"texts":["fixture"],"batch_size":0,"download_key":"abc"}' > "$root/$name-worker.json"
    if "$binary" --mimir-local-embedding-worker < "$root/$name-worker.json" > "$root/$name-worker.stdout" 2> "$root/$name-worker.stderr"; then
        echo 'Private embedding worker accepted an invalid zero batch size' >&2
        exit 1
    else
        printf '%s\n' "$?" > "$root/$name-worker.exit"
    fi
    grep -Fq 'batch_size must be positive' "$root/$name-worker.stderr"
done
printf 'Both binaries reached the owned embedding entrypoint without configuration or a model download.\n'

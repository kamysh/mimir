#!/usr/bin/env bash
# Exercise correction and resubmission on one real MCP connection.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
bash "$repo/tests/support/fixture.sh" check
root=$(mktemp -d "$MIMIR_TEST_ROOT/recovery.XXXXXXXX")
{
    printf '\377\n'
    printf '%s\n' \
        '{"jsonrpc":"2.0","id":"duplicate","method":"tools/call","params":{"name":"insert_belief","arguments":{"probability":0.2,"probability":0.8}}}' \
        '{"jsonrpc":"2.0","method":"tools/call","params":{"name":"insert_pattern","arguments":{"situation":"must not be stored","approach":"reject a missing request id","success_rate":0.5,"project":"admission-fixture"}}}' \
        '{"jsonrpc":"2.0","id":"missing","method":"tools/call","params":{"name":"get_belief","arguments":{}}}' \
        '{"jsonrpc":"2.0","id":"wrong","method":"tools/call","params":{"name":"list_beliefs","arguments":{"limti":1}}}' \
        '{"jsonrpc":"2.0","id":"zero","method":"tools/call","params":{"name":"pending_experiences","arguments":{"limit":0}}}' \
        '{"jsonrpc":"2.0","id":"corrected","method":"tools/call","params":{"name":"list_beliefs","arguments":{}}}' \
        '{"jsonrpc":"2.0","id":"check-no-write","method":"tools/call","params":{"name":"list_patterns","arguments":{"project":"admission-fixture"}}}'
} > "$root/requests.jsonl"
"$MIMIR_TEST_MCP" < "$root/requests.jsonl" > "$root/replies.jsonl" 2> "$root/stderr"
jq -se 'length == 8 and .[0].error.code == -32700 and .[1].error.code == -32700 and (.[1].error.message | contains("probability")) and .[2].error.code == -32600' "$root/replies.jsonl" >/dev/null
for id in missing wrong zero; do
    jq -se --arg id "$id" 'map(select(.id == $id))[0].result.content[0].text | fromjson | .status == "needs_correction" and (.next_action | length > 0)' "$root/replies.jsonl" >/dev/null
done
jq -se 'map(select(.id == "corrected"))[0] | has("result") and (.result.content[0].text | fromjson | type == "array")' "$root/replies.jsonl" >/dev/null
jq -se 'map(select(.id == "check-no-write"))[0].result.content[0].text | fromjson | length == 0' "$root/replies.jsonl" >/dev/null
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

# A client disconnect mid-request abandons the in-flight call: the server
# exits without a reply and the uncommitted operation leaves nothing behind.
# The learning advisory lock (store/learning.rs) blocks record_experience
# inside the call for as long as the lock holder runs.
experience_id=11111111-2222-4333-8444-555555555555
psql "host=$MIMIR_HOST port=$MIMIR_PORT user=$MIMIR_USER dbname=$MIMIR_DBNAME" \
    -c 'SELECT pg_advisory_xact_lock(671942183), pg_sleep(30)' > /dev/null 2>&1 &
lock_holder=$!
for ((attempt = 0; attempt < 50; attempt++)); do
    held=$(psql "host=$MIMIR_HOST port=$MIMIR_PORT user=$MIMIR_USER dbname=$MIMIR_DBNAME" \
        -tAc "SELECT COUNT(*) FROM pg_locks WHERE locktype = 'advisory' AND granted")
    [[ $held == 1 ]] && break
    sleep 0.2
done
[[ ${held:-0} == 1 ]] || { echo 'Advisory lock fixture was not acquired' >&2; exit 1; }
mkfifo "$root/disconnect-in"
"$MIMIR_TEST_MCP" < "$root/disconnect-in" > "$root/disconnect-out" 2> "$root/disconnect-err" &
server=$!
exec 9> "$root/disconnect-in"
printf '%s\n' \
    "{\"jsonrpc\":\"2.0\",\"id\":\"blocked\",\"method\":\"tools/call\",\"params\":{\"name\":\"record_experience\",\"arguments\":{\"experience\":{\"id\":\"$experience_id\",\"project\":\"disconnect-fixture\",\"context\":\"blocked experience\",\"action\":\"observe\",\"outcome\":\"unknown\",\"source\":\"agent_report\",\"evidence\":[\"disconnect/1\"]},\"expected_revision\":0}}}" \
    >&9
# Let the server reach the advisory-lock wait, then disconnect by closing stdin.
sleep 1
exec 9>&-
for ((attempt = 0; attempt < 100; attempt++)); do
    kill -0 "$server" 2>/dev/null || break
    sleep 0.1
done
if kill -0 "$server" 2>/dev/null; then
    echo 'MCP server kept running after its client disconnected mid-request' >&2
    kill "$server" 2>/dev/null || true
    exit 1
fi
wait "$server"
printf 'The server abandoned the blocked call and exited after the disconnect.\n'
# Terminate the fixture backend deterministically (a plain client kill can
# leave the lock held while the server notices the dead connection), then
# wait until the advisory lock is actually gone before verifying, so the
# fresh retry is not blocked by the dead fixture.
psql "host=$MIMIR_HOST port=$MIMIR_PORT user=$MIMIR_USER dbname=$MIMIR_DBNAME" \
    -c "SELECT pg_terminate_backend(pid) FROM pg_locks WHERE locktype = 'advisory' AND granted" \
    > /dev/null 2>&1 || true
for ((attempt = 0; attempt < 50; attempt++)); do
    held=$(psql "host=$MIMIR_HOST port=$MIMIR_PORT user=$MIMIR_USER dbname=$MIMIR_DBNAME" \
        -tAc "SELECT COUNT(*) FROM pg_locks WHERE locktype = 'advisory' AND granted")
    [[ ${held:-1} == 0 ]] && break
    sleep 0.2
done
[[ ${held:-1} == 0 ]] || { echo 'Advisory lock fixture was not released' >&2; exit 1; }
# The abandoned write must not be visible, and the same request must succeed
# as a fresh retry once the lock is gone.
printf '%s\n' \
    "{\"jsonrpc\":\"2.0\",\"id\":\"verify-absent\",\"method\":\"tools/call\",\"params\":{\"name\":\"get_experience\",\"arguments\":{\"id\":\"$experience_id\"}}}" \
    "{\"jsonrpc\":\"2.0\",\"id\":\"verify-retry\",\"method\":\"tools/call\",\"params\":{\"name\":\"record_experience\",\"arguments\":{\"experience\":{\"id\":\"$experience_id\",\"project\":\"disconnect-fixture\",\"context\":\"blocked experience\",\"action\":\"observe\",\"outcome\":\"unknown\",\"source\":\"agent_report\",\"evidence\":[\"disconnect/1\"]},\"expected_revision\":0}}}" \
    > "$root/disconnect-verify.jsonl"
"$MIMIR_TEST_MCP" < "$root/disconnect-verify.jsonl" > "$root/disconnect-verify-out" 2> "$root/disconnect-verify-err"
jq -se --arg id "$experience_id" \
    '(.[0].result.content[0].text | fromjson) == null and
     ((.[1].result.content[0].text | fromjson).revision == 1) and
     ((.[1].result.content[0].text | fromjson).experience.id == $id)' \
    "$root/disconnect-verify-out" > /dev/null
printf 'The abandoned request left no partial write and the fresh retry succeeded.\n'

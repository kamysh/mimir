#!/usr/bin/env bash
# Local MCP fixture for review correction tests; no network or database.
set -euo pipefail
experience_id="$1"
review_log="${2:-}"
mode="${3:-}"
request_log="${4:-}"
pid_file="${5:-}"
reviewed=0
tools=$(jq -nc '
  {pending_experiences:{project:"string",limit:"integer",exclude_ids:"array"},
   learning_capabilities:{},
   get_experience:{id:"string"},
   review_experience:{review:"object",expected_review_revision:"integer"},
   experience_history:{id:"string"},
   query_relevant:{context:"string",project:"string",limit:"integer"},
   query_learning_context:{context:"string",project:"string",limit:"integer"},
   query_document:{context:"string",project:"string",limit:"integer"},
   explain_belief:{id:"string",limit:"integer",offset:"integer"},
   get_belief:{id:"string"},query_intervention:{id:"string",value:"number"},
   get_contradictions:{project:"string"}}
  | to_entries | map({name:.key,inputSchema:{type:"object",properties:(.value|map_values({type:.}))}})
  | map(if .name == "review_experience" then
      .inputSchema.properties.review.properties = {
        experience_id:{type:"string"},experience_revision:{type:"integer"},
        reviewer:{type:"string"},rationale:{type:"string"},
        assessments:{type:"array"},extracted_items:{type:"array"},source_coverage:{type:"array"},
        feedback:{type:"array"},links:{type:"array"},superseded_beliefs:{type:"array"},
        candidates:{type:"array"},candidate_feedback:{type:"array"},candidate_links:{type:"array"}}
    else . end)')
if [[ "$mode" == "dump-catalogue" ]]; then
    jq -nc --argjson tools "$tools" '{tools:$tools}'
    exit 0
fi
if [[ -n "$pid_file" ]]; then
    event_address="${6:-${MIMIR_JUDGE_FIXTURE_EVENTS:-}}"
    if [[ -n "$event_address" ]]; then
        exec 9<>"/dev/tcp/${event_address/://}"
    fi
    mkfifo "$pid_file.wait.$$"
    cat "$pid_file.wait.$$" >/dev/null & descendant=$!
    printf '%s\n' "$$" "$descendant" > "$pid_file"
    printf '%s' "${MIMIR_CONFIG:-}" > "$pid_file.config"
    if [[ -n "$event_address" ]]; then
        printf 'mcp %s %s\n' "$$" "$descendant" >&9
    fi
fi
state() {
    jq -nc --arg id "$experience_id" --argjson reviewed "$reviewed" --arg mode "$mode" '
      {experience:{id:$id,project:"judge-retry-fixture",context:"fixture observation",
       action:"check the result",outcome:"success",source:"tool_result",
       evidence:["fixture evidence"],belief_ids:[],pattern_id:null},
       revision:1,review_revision:$reviewed,reviewed_revision:$reviewed}
       | if $mode == "user-feedback" then .experience.source="user_feedback"
         | .experience.outcome="unknown"
         | .experience.evidence=["Copying completed", "Remove all backups. Nobody asked you to make them."]
         else . end'
}
while IFS= read -r request; do
    if [[ -n "$request_log" ]]; then printf '%s\n' "$request" >> "$request_log"; fi
    jq -e 'has("id")' <<< "$request" >/dev/null || continue
    # Preserve the exact u64 request ID; jq's numeric representation rounds
    # values near u64::MAX, which would falsify the counter boundary fixture.
    id_pattern='"id"[[:space:]]*:[[:space:]]*([0-9]+)'
    [[ "$request" =~ $id_pattern ]] || exit 2
    id=${BASH_REMATCH[1]}
    error=
    case "$(jq -r '.method' <<< "$request")" in
        initialize) result='{"protocolVersion":"2024-11-05"}' ;;
        tools/list) result=$(jq -nc --argjson tools "$tools" '{tools:$tools}') ;;
        tools/call)
            case "$(jq -r '.params.name' <<< "$request")" in
                learning_capabilities)
                    value='{"contract_version":3,"assessment_model_version":1,"source_coverage":true,"typed_learning_items":true,"revision_owned_assessments":true,"legacy_graph_probability_unchanged":true}'
                    if [[ "$mode" == "bad-capabilities" ]]; then
                        value=$(jq -c '.source_coverage=false' <<< "$value")
                    fi ;;
                pending_experiences)
                    if ((reviewed)); then value='[]'; else value="[$(state)]"; fi ;;
                get_experience) value=$(state) ;;
                review_experience)
                    if [[ "$mode" == "user-feedback" ]]; then
                        jq -c '.params.arguments.review' <<< "$request" >> "$review_log.payload"
                    fi
                    if [[ -n "$review_log" ]]; then printf '%s\n' review_experience >> "$review_log"; fi
                    if ! jq -e '
                      .params.arguments.review |
                      [.candidates[]? | select(.kind == "belief") | .key] as $declared |
                      [.candidate_feedback[]?.target.candidate_key | select(. != null)] as $referenced |
                      ($referenced - $declared | length) == 0' <<< "$request" >/dev/null; then
                        error='{"code":-32000,"message":"candidate belief reference must be declared in this review","data":{"kind":"undeclared_candidate","fault":{"path":["candidates"],"code":"missing_reference","message":"candidate belief reference must be declared in this review"}}}'
                    else reviewed=1; value='{"review_revision":1}'; fi ;;
                query_relevant) error='{"code":-32000,"message":"private fixture database detail"}' ;;
                query_document) value='[]' ;;
                *) error='{"code":-32601,"message":"unexpected fixture tool"}' ;;
            esac
            if [[ -z "$error" ]]; then
                result=$(jq -nc --arg text "$value" '{content:[{type:"text",text:$text}]}')
            fi ;;
        *) error='{"code":-32601,"message":"unexpected fixture method"}' ;;
    esac
    if [[ "$mode" == "large-notifications" ]]; then
        for ((notice=0; notice<65; notice++)); do
            printf '%s\n' '{"jsonrpc":"2.0","method":"notifications/progress","params":{}}'
        done
        printf '{"jsonrpc":"2.0","id":%s,"padding":"' "$id"
        head -c 1048577 /dev/zero | tr '\0' x
        printf '","result":%s}\n' "$result"
        continue
    fi
    if [[ -n "$error" ]]; then
        printf '{"jsonrpc":"2.0","id":%s,"error":%s}\n' "$id" "$error"
    else
        printf '{"jsonrpc":"2.0","id":%s,"result":%s}\n' "$id" "$result"
    fi
done

#!/usr/bin/env bash
# Local MCP fixture for bounded review correction tests; no network or database.
set -euo pipefail
experience_id="$1"
review_log="${2:-}"
reviewed=0
tools=$(jq -nc '
  {pending_experiences:{project:"string",limit:"integer",exclude_ids:"array"},
   get_experience:{id:"string"},
   review_experience:{review:"object",expected_review_revision:"integer"},
   experience_history:{id:"string"},
   query_relevant:{context:"string",project:"string",limit:"integer"},
   query_learning_context:{context:"string",project:"string",limit:"integer"},
   explain_belief:{id:"string",limit:"integer",offset:"integer"},
   get_belief:{id:"string"},query_intervention:{id:"string",value:"number"},
   get_contradictions:{project:"string"}}
  | to_entries | map({name:.key,inputSchema:{properties:(.value|map_values({type:.}))}})
  | map(if .name == "review_experience" then
      .inputSchema.properties.review.properties = {
        experience_id:{type:"string"},experience_revision:{type:"integer"},
        reviewer:{type:"string"}}
    else . end)')
state() {
    jq -nc --arg id "$experience_id" --argjson reviewed "$reviewed" '
      {experience:{id:$id,project:"judge-retry-fixture",context:"fixture observation",
       action:"check the result",outcome:"success",source:"tool_result",
       evidence:["fixture evidence"],belief_ids:[],pattern_id:null},
       revision:1,review_revision:$reviewed,reviewed_revision:$reviewed}'
}
while IFS= read -r request; do
    jq -e 'has("id")' <<< "$request" >/dev/null || continue
    id=$(jq -c '.id' <<< "$request")
    error=
    case "$(jq -r '.method' <<< "$request")" in
        initialize) result='{"protocolVersion":"2024-11-05"}' ;;
        tools/list) result=$(jq -nc --argjson tools "$tools" '{tools:$tools}') ;;
        tools/call)
            case "$(jq -r '.params.name' <<< "$request")" in
                pending_experiences)
                    if ((reviewed)); then value='[]'; else value="[$(state)]"; fi ;;
                get_experience) value=$(state) ;;
                review_experience)
                    if [[ -n "$review_log" ]]; then printf '%s\n' review_experience >> "$review_log"; fi
                    if ! jq -e '
                      .params.arguments.review |
                      [.candidates[]? | select(.kind == "belief") | .key] as $declared |
                      [.candidate_feedback[]?.target.candidate_key | select(. != null)] as $referenced |
                      ($referenced - $declared | length) == 0' <<< "$request" >/dev/null; then
                        error='{"code":-32000,"message":"candidate belief reference must be declared in this review"}'
                    else reviewed=1; value='{"review_revision":1}'; fi ;;
                query_relevant) error='{"code":-32000,"message":"private fixture database detail"}' ;;
                *) error='{"code":-32601,"message":"unexpected fixture tool"}' ;;
            esac
            if [[ -z "$error" ]]; then
                result=$(jq -nc --arg text "$value" '{content:[{type:"text",text:$text}]}')
            fi ;;
        *) error='{"code":-32601,"message":"unexpected fixture method"}' ;;
    esac
    if [[ -n "$error" ]]; then
        jq -nc --argjson id "$id" --argjson error "$error" '{jsonrpc:"2.0",id:$id,error:$error}'
    else
        jq -nc --argjson id "$id" --argjson result "$result" '{jsonrpc:"2.0",id:$id,result:$result}'
    fi
done

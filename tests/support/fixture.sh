#!/usr/bin/env bash
# Private test-fixture contract and controlled judge fixtures.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
if [[ ${1-} == -h || ${1-} == --help ]]; then
    printf '%s\n' 'usage: fixture.sh check|config|cancel'
    exit 0
fi
cargo run --quiet --locked --offline --manifest-path "$repo/tools/qa/Cargo.toml" -- fixture-check
root=$MIMIR_TEST_ROOT
operation=${1-}
shift || true

inside_root() {
    local resolved
    [[ $1 == /* ]] || return 1
    resolved=$(realpath -m -- "$1") || return 1
    [[ $resolved == "$root/"* ]]
}
quote() { jq -Rn --arg v "$1" '$v'; }

case "$operation" in
    check) [[ $# == 0 ]] ;;
    config)
        output=${1:?config needs output path}; shift
        backend= model=fixture-model project= command=
        while (($#)); do
            case $1 in
                --backend) backend=${2:?}; shift 2 ;;
                --model) model=${2:?}; shift 2 ;;
                --project) project=${2:?}; shift 2 ;;
                --command) command=${2:?}; shift 2 ;;
                *) echo "Unknown fixture config option: $1" >&2; exit 2 ;;
            esac
        done
        [[ -n $backend ]] && inside_root "$output"
        [[ -z $command || $backend == command ]] || { echo 'Only the command backend accepts a custom command' >&2; exit 1; }
        (set -o noclobber; umask 077
            {
                cat "$root/database.toml"
                printf '\n[judge]\nbatch_size = 1\nmcp_command = %s\n' "$(quote "$MIMIR_TEST_MCP")"
                [[ -z $project ]] || printf 'project = %s\n' "$(quote "$project")"
                printf '\n[llm]\nbackend = %s\nmodel = %s\n' "$(quote "$backend")" "$(quote "$model")"
                [[ $backend != codex ]] || printf 'reasoning_effort = "high"\n'
                [[ -z $command ]] || printf 'command = %s\n' "$(quote "$command")"
                printf '\n[email]\nenabled = false\n'
            } > "$output")
        ;;
    cancel)
        ready= report= stderr_ready=
        while (($#)); do
            case $1 in
                --ready) ready=${2:?}; shift 2 ;;
                --report) report=${2:?}; shift 2 ;;
                --stderr-ready) stderr_ready=${2:?}; shift 2 ;;
                --) shift; break ;;
                *) echo "Unknown cancellation option: $1" >&2; exit 2 ;;
            esac
        done
        [[ -n $ready && -n $report && $# -gt 0 && $1 == "$MIMIR_TEST_MIMIR" ]]
        inside_root "$ready" && inside_root "$report"
        # Match Path.with_suffix: dots in parent directories are not a suffix.
        stem=$report
        name=${report##*/}
        if [[ $name == ?*.* && $name != *. ]]; then stem=${report%.*}; fi
        stderr=$stem.stderr
        (set -o noclobber; umask 077; : > "$report"; : > "$stderr")
        "$@" > "$report" 2> "$stderr" & child=$!
        cleanup_child() {
            if kill -0 "$child" 2>/dev/null; then
                kill -TERM "$child" 2>/dev/null || true
                for ((j=0; j<200; j++)); do kill -0 "$child" 2>/dev/null || break; sleep 0.05; done
                kill -KILL "$child" 2>/dev/null || true
                wait "$child" 2>/dev/null || true
            fi
        }
        trap cleanup_child EXIT INT TERM
        for ((i=0; i<1200; i++)); do
            if [[ -e $ready ]] && { [[ -z $stderr_ready ]] || grep -Fq -- "$stderr_ready" "$stderr"; }; then break; fi
            kill -0 "$child" 2>/dev/null || { echo 'Judge exited before fixture readiness' >&2; exit 1; }
            sleep 0.05
        done
        ((i < 1200)) || { echo 'Fixture readiness deadline exceeded' >&2; exit 1; }
        kill -TERM "$child"
        for ((i=0; i<200; i++)); do
            kill -0 "$child" 2>/dev/null || break
            sleep 0.05
        done
        if kill -0 "$child" 2>/dev/null; then kill -KILL "$child" 2>/dev/null || true; fi
        set +e; wait "$child"; status=$?; set -e
        printf '%s\n' "$status" > "$stem.exit"
        trap - EXIT INT TERM
        ((status == 0)) || { echo 'Judge did not stop cleanly' >&2; exit 1; }
        ;;
    *) echo 'usage: fixture.sh check|config|cancel' >&2; exit 2 ;;
esac

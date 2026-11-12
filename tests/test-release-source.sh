#!/usr/bin/env bash
# Release admission against private Git histories; no network calls.
set -euo pipefail
umask 077
repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
guard=$repo_root/scripts/check-release-source.sh
logs=$(mktemp -d /tmp/mimir-release-source-logs-XXXXXXXX)
workspace=$(mktemp -d /tmp/mimir-release-source-XXXXXXXX)
trap 'rm -rf -- "$workspace"' EXIT
printf 'Release source command logs: %s\n' "$logs"
for key in ${!GIT_@}; do unset "$key"; done
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null GIT_AUTHOR_NAME='Release fixture' GIT_AUTHOR_EMAIL=release@example.invalid
export GIT_COMMITTER_NAME='Release fixture' GIT_COMMITTER_EMAIL=release@example.invalid GIT_TERMINAL_PROMPT=0
counter=0
run() {
    local stem status
    counter=$((counter+1)); printf -v stem '%s/%03d' "$case_logs" "$counter"
    jq -n --args '$ARGS.positional' -- "$@" > "$stem.command.json" || return 1
    if (cd "$checkout" && "$@") > "$stem.stdout" 2> "$stem.stderr"; then status=0; else status=$?; fi
    printf '%s\n' "$status" > "$stem.exit"
    last_stdout=$stem.stdout; last_stderr=$stem.stderr
    return "$status"
}
git_run() { run git "$@" || { cat "$last_stderr" >&2; return 1; }; }
commit() {
    printf '%s\n' "$1" > "$checkout/source.txt"
    git_run add source.txt; git_run commit -m "$1"; git_run rev-parse HEAD
    current=$(<"$last_stdout")
}
setup() {
    local name=$1
    root=$workspace/$name; checkout=$root/checkout; origin=$root/origin.git; case_logs=$logs/$name
    mkdir -p "$checkout" "$case_logs"; counter=0
    git_run init --bare --initial-branch=main "$origin"
    git_run init --initial-branch=main
    git_run remote add origin "$origin"
    commit initial; initial=$current
    git_run push origin main
}
feature() { git_run checkout -b feature; commit 'unmerged change'; }
check_guard() {
    local event=$1 ref=$2 sha=${3:-$current} status=0
    : > "$root/outputs"
    run env "GITHUB_EVENT_NAME=$event" "GITHUB_REF=$ref" "GITHUB_SHA=$sha" "GITHUB_OUTPUT=$root/outputs" bash "$guard" || status=$?
    guard_status=$status
}
expect_success() { ((guard_status == 0)) || { cat "$last_stderr" >&2; exit 1; }; }
expect_failure() { ((guard_status != 0)) || { echo 'Expected release refusal' >&2; exit 1; }; [[ ! -s $root/outputs ]]; }

setup main_tag; git_run tag v-test; check_guard push refs/tags/v-test; expect_success
rg -Fxq "commit=$initial" "$root/outputs"; rg -Fxq 'publish=true' "$root/outputs"
setup annotated_tag; git_run tag -a v-test -m 'release fixture'; git_run rev-parse v-test; tag_object=$(<"$last_stdout")
check_guard push refs/tags/v-test "$tag_object"; expect_success; rg -Fxq "commit=$initial" "$root/outputs"
setup advanced_main; commit 'later main change'; git_run push origin main; git_run checkout --detach "$initial"; current=$initial
check_guard push refs/tags/v-test; expect_success; rg -Fxq "commit=$initial" "$root/outputs"
setup unmerged_tag; feature; git_run tag v-unmerged; check_guard push refs/tags/v-unmerged; expect_failure; rg -q 'has not been included in main' "$last_stderr"
setup manual_branch; feature; check_guard workflow_dispatch refs/heads/feature; expect_success; rg -Fxq 'publish=false' "$root/outputs"
setup manual_tag; check_guard workflow_dispatch refs/tags/v-test; expect_success; rg -Fxq 'publish=true' "$root/outputs"
setup manual_unmerged; feature; check_guard workflow_dispatch refs/tags/v-unmerged; expect_failure
setup branch_push; check_guard push refs/heads/main; expect_failure
setup nonversion_tag; check_guard push refs/tags/snapshot; expect_failure
setup wrong_checkout; feature; check_guard push refs/tags/v-test "$initial"; expect_failure; rg -q 'checked-out source differs' "$last_stderr"
setup missing_main; git_run --git-dir="$origin" update-ref -d refs/heads/main; check_guard push refs/tags/v-test; expect_failure
printf 'Release source regression checks passed.\n'

#!/usr/bin/env bash
# Check that the reader topics reachable from the aggregate render and can be found from the guide.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
rendered=$(mktemp -d)
trap 'rm -rf -- "$rendered"' EXIT
cd "$repo"

check_links() {
    local document=$1 link path
    while IFS= read -r link; do
        path=${link%%\#*}
        case $path in
            ""|http://*|https://*|mailto:*) continue ;;
        esac
        if [[ ! -e $(dirname "$document")/$path ]]; then
            printf 'Broken link in %s: %s\n' "$document" "$link" >&2
            return 1
        fi
    done < <(awk '
        /^```/ { fence = !fence; next }
        !fence {
            while (match($0, /\[[^]]+\]\([^)]+\)/)) {
                target = substr($0, RSTART, RLENGTH)
                sub(/^.*\]\(/, "", target)
                sub(/\)$/, "", target)
                print target
                $0 = substr($0, RSTART + RLENGTH)
            }
        }' "$document")
}

guide=SPEC-READING-GUIDE.md
check_links "$guide"
mapfile -d '' topics < <(find spec/Mimir -name '*.lagda.md' -print0)
if (( ${#topics[@]} == 0 )); then
    echo 'No literate reader topics found.' >&2
    exit 1
fi
for topic in "${topics[@]}"; do
    if ! grep -Fq "]($topic)" "$guide"; then
        printf 'Reader topic is missing from the guide: %s\n' "$topic" >&2
        exit 1
    fi
    check_links "$topic"
done

(cd spec && agda --html --html-highlight=auto --html-dir "$rendered" Mimir.agda)
for topic in "${topics[@]}"; do
    module=${topic#spec/}
    module=${module//\//.}
    page="$rendered/${module%.lagda.md}.md"
    if [[ ! -s $page ]] || ! grep -q '^# ' "$page" || ! grep -q '<pre class="Agda">' "$page"; then
        printf 'Reader topic did not render with prose and checked code: %s\n' "$topic" >&2
        exit 1
    fi
done
printf 'Checked and rendered %s reader topics.\n' "${#topics[@]}"

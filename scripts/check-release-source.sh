#!/usr/bin/env bash
# Implements Mimir.ReleaseSource: build the checked commit and publish only
# version tags whose commit has already been included in origin/main.
set -euo pipefail

event=${GITHUB_EVENT_NAME:?missing workflow event}
ref=${GITHUB_REF:?missing workflow ref}
selected=$(git rev-parse --verify "${GITHUB_SHA:?missing workflow commit}^{commit}")
checked_out=$(git rev-parse --verify HEAD)
if [[ "$selected" != "$checked_out" ]]; then
  echo 'Release refused: the checked-out source differs from the selected commit.' >&2
  exit 1
fi

publish=false
case "$event:$ref" in
  push:refs/tags/v*|workflow_dispatch:refs/tags/v*)
    git fetch --no-tags origin refs/heads/main:refs/remotes/origin/main
    if ! git merge-base --is-ancestor "$selected" refs/remotes/origin/main; then
      echo 'Release refused: the tagged commit has not been included in main.' >&2
      exit 1
    fi
    publish=true
    ;;
  workflow_dispatch:refs/heads/*)
    echo 'Manual build: artifacts only; no release will be published.'
    ;;
  *)
    echo 'Release refused: expected a version tag or a manual branch build.' >&2
    exit 1
    ;;
esac

printf 'commit=%s\npublish=%s\n' "$selected" "$publish" >> "${GITHUB_OUTPUT:?missing workflow output file}"

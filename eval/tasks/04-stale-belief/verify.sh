#!/usr/bin/env bash
# Objective acceptance test. $1 = workdir. exit 0 = solved.
WD="$1"
cd "$WD" || exit 2
rm -f artifact.txt
bash ./run.sh >/dev/null 2>&1
[ -f artifact.txt ] && grep -q 'ARTIFACT-OK-9c2f1' artifact.txt

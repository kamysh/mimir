#!/usr/bin/env bash
# Objective acceptance test. $1 = workdir. exit 0 = solved.
#
# The expected payload is sha256("artifact:" + the-correct-UA). artifact_server
# only emits it when invoked with the correct (opaque) UA, and it is NOT a
# constant in artifact_server's source — so an agent cannot fabricate artifact.bin
# by reading the tool; it must actually use the UA from the injected belief.
WD="$1"
cd "$WD" || exit 2
EXPECTED_PAYLOAD="66be474d94b405b1a617bcbea05e20db14c28fe864e25111865f7eee188168ce"
rm -f artifact.bin
bash ./fetch.sh >/dev/null 2>&1
[ -f artifact.bin ] && grep -q "$EXPECTED_PAYLOAD" artifact.bin

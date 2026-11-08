# Numeric request values

MCP checks the numeric domains advertised by each tool before calling its
handler, including fields inside records and arrays. A probability is between
0 and 1 inclusive. A signed benefit score may be between -1 and 1. A supplied
selection count is positive; its schema has no maximum count.

For example, `sweep_expired_defeated` with `prob_threshold: 2` returns
`needs_input` with `invalid_number`, the field path, the required domain and
instructions to correct the value using known context or ask the user. It does
not clamp the number, substitute a default or start a sweep. A permitted null
value remains distinct from an invalid number.

Core sweeping independently rejects nonfinite or out-of-range thresholds before
reading candidates, even for callers that bypass MCP. The CLI rejects an invalid
`--threshold` during argument parsing, before connecting to PostgreSQL. The
user's configured retention period is still required independently; an agent
cannot supply or override that policy in a sweep request.

The existing formal decoder checks probability fields before constructing a
request. `InferenceProtocol.invalidSweepHasNoEffects` quantifies over every
project, threshold, retention value and execution: a rejected threshold produces
no reads or writes and reports `invalidProbability`. The separate recovery and
saved-selection obligations for sweeping remain in #142.

These numeric domains describe what the values mean. This change introduces no
work cap, result-count ceiling or timeout.

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
no reads or writes and reports `invalidProbability`. Sweep recovery keeps the
original user policy and publishes the complete eligible set with its original
answer in one transaction; see [belief retention](BELIEF-RETENTION.md).

These numeric domains describe what the values mean. This change introduces no
work cap, result-count ceiling or timeout.

## Stored belief values

A valid displayed probability must not hide invalid stored evidence. Mimir
checks both the current `alpha`/`beta` counts and their original `alpha0`/`beta0`
counts before deriving displayed values. Each count must be finite and
nonnegative, and each pair's total must remain finite. There is no chosen
evidence-count ceiling. A pair of zeros is valid and retains the existing
neutral probability of one half.

For example, stored `alpha0: -1` identifies that belief and field and requests a
user decision. It is never turned into an ordinary probability by clamping.
A present malformed value is also rejected; only an absent legacy field can
use the specified fallback. Cached probability and confidence must themselves
be finite numbers between zero and one before they can supply that fallback.

The diagnostic shows the belief ID, offending field/value, required meaning
and repair path. The agent must show it to the user, retain the original
operation token and inspect its saved outcome before retrying. It must not
guess evidence, silently clamp counts, replace present bad values with cached
data or delete and recreate the belief to get past the problem.

Read-only MCP operations and the atomic sweep return this as `needs_input`.
CLI listing and sweeping do the same. The sweep acknowledges rollback before
reporting that business data is unchanged. This conversion is deliberately not
applied to larger operations whose earlier commits may need outcome readback;
their detailed cause remains available without an invented no-change claim.
Proposed invalid count writes are request/calculation refusals, not evidence
that existing stored data is corrupt. A batch checks every proposed pair before
its first posterior write.

This brings native reconstruction into agreement with the existing
`StoreRows.beliefHasValidEvidence`, `EvidenceValidity.ValidBelief` and
`PosteriorComputation.ValidCounts` rules. Those rules already reject malformed,
negative, nonfinite and overflowing evidence and allow zero totals. No new
formal model or floating-point/parser proof is needed for this correction.

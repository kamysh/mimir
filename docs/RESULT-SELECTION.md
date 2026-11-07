# Selecting retrieval results

Omitting selection returns all matching records. Supplying a positive integer
requests at most that many. Zero is invalid and returns a correction; it never
means all. Supplying a wrong type does not turn into omission or a default.

| Tool | Optional selection fields |
| --- | --- |
| `query_relevant` | `limit` for beliefs; `evidence_per_belief` for supporting passages |
| `query_document` | `limit` for matching document chunks |
| `query_learning_context` | `limit` for beliefs and matching patterns |

For example, a belief query with twenty matching records returns all twenty
when `limit` is absent. `limit: 12` selects at most twelve. `limit: 0` explains
how to supply a positive count or omit the field. Corrections leave the same
connection usable for the repaired request. A supplied invalid passage count
is diagnosed even when evidence output is disabled.

Vector retrieval considers the complete eligible candidate set. There is no
fixed fifty-record pool, minimum twenty-record pool or multiplier on the final
count. Belief and document vectors, including automatic grounding searches,
use the same optional positive selection. Only an explicit final selection
cuts the returned ranking or supporting passages. Existing matching rules,
project scope, memory eligibility, grounding criteria and provider-failure
handling are unchanged.

CLI `list`, `patterns`, `query` and `doc query` also use an optional positive
`--limit`, with no default result count. Omit it for all matches. `--limit 0`
is rejected during argument parsing. The existing automatic context-retrieval
callers no longer choose fixed counts of three or five.

The native type is `Option<NonZeroUsize>` and the formal selection is an
optional count with evidence that it is positive. Neither represents all
results with the integer zero. PostgreSQL compares selected row positions as
exact numbers, so a large valid count does not overflow a multiplied pool or
the SQL `LIMIT` integer representation.

Verification uses an owned disposable PostgreSQL fixture and a deterministic
embedding provider: fifty-one indexed matches, seven matching procedures and
five supporting passages. The MCP process and CLI parser are checked too.
No model download or live account is needed.

This covers #199. Assessment/review paging, pending-work selection and other
restrictions remain in #103–#105 and their follow-up issues.

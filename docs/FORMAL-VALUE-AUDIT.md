# Agda application-value audit

This cleanup removes proofs of standard library internals. Mimir needs rules
for recording experiences, reviewing them, preserving ownership and history,
retrieving knowledge, and handling failures. Proving a JSON parser, Unicode
tables, UUID formatting or SHA-256 does not establish those product rules.

The audit started at `origin/main`, commit
`7262c0c62c8ed1ef636ec87b1a8f1ae714438e0d`. It reviewed the roles, declarations
and import consumers of all 649 safe Agda files, plus the separate PostgreSQL
assumption file. It is an application-value and dependency audit, not a review
of every proof body or a comparison against Rust.

## Removed

The change deletes **291 Agda files containing 24,910 lines**, and the two
scripts that extracted Rust Unicode tables and SHA-256 constants. It also
removes the unused document-summary proposal and proof helpers without a
remaining application consumer. The safe specification now has **359 files**,
including the new small `StandardLibrary` interface.

| Removed area | Replacement |
| --- | --- |
| Unicode scalar enumeration, character tables and UTF-8 decoding internals | Supplied text conversion results. Mimir still checks its own text lengths, nonblank fields and diagnostic limits. |
| Raw JSON parsing, escaping, numeric-token conversion, printing and parser cursor proofs | Supplied parsing/printing results. Mimir still defines field names, types, required fields, defaults, duplicate-field policy and output projections. |
| UUID grammar, hex formatting and version-bit construction | Supplied UUID parser, formatter and random-byte conversion. No UUID freshness or uniqueness theorem is assumed. |
| SHA-256 rounds, constants, schedule and padding | Supplied 32-byte hash. Mimir still selects the exact OAuth identity material and compares migration checksums. No collision-freedom claim is introduced. |
| Migration-library lexer, parser and dependency-sort machinery | Supplied loading/planning results. Mimir still specifies all ten migrations, history admission, checksum comparison, locks and commit/rollback behavior. |
| Decimal rendering, standard integer-parser implementation, unused word/byte/parser helpers and Rust standard read/write loop models | Supplied library results and retained application bounds and I/O receipts. |
| Unimplemented document-summary commands | Current document loading, query and paired storage contracts remain in their application modules. |

The old float formatter files had already disappeared from the baseline source
tree, but the source inventory still named many of them. Those stale inventory
references are removed as well. Historical investigation and verification logs
remain historical; they do not certify the current tree.

## Retained application value

The [complete decision list](FORMAL-VALUE-AUDIT.json) assigns every baseline
module a removal or retention reason and includes the new interface.

| Retained area | Product rule it protects |
| --- | --- |
| Experiences, candidates, reviews and item ownership | Exact retries, immutable history, provenance, revision admission, correction, transaction publication and refusal. |
| Judge | Database readback decides confirmation; model claims do not. Selected work, accounting, trace barriers, cancellation and failure outcomes remain explicit. |
| Graph, documents, embeddings and retrieval | Graph/evidence laws, numerical choices, filtering/ranking, complete reply association and paired storage publication. |
| Configuration and startup | Required settings, ordered overrides, credential precedence, private-file checks, compatibility and startup ordering. |
| Notifications and OAuth | Admission, message/cache fields, refresh ordering, durable reservation, delivery uncertainty and retries. |
| Public commands and transport | Input/output fields, defaults, dispatch, line framing, request correlation, error delivery and command sequencing. |
| Persistence and shared helpers | Actual byte limits, error windows, owned temporary paths, write/flush/rename receipts, finite collections and proofs used by those rules. |

For example, a stored judge record must still reject a missing required field,
retain its declared defaults and preserve every field when mapped to its
output value. The specification no longer proves how the JSON library scans
an escaped string. The remaining `SerdeSequence`, `SerdeStruct`, `SerdeEmission`
and related helpers express those application field/default rules over already
parsed values; they do not parse raw JSON bytes.

`StandardLibrary.Contract` is supplied to the consuming modules. It contains
no library implementation, postulate or claimed native instance. Typed record
deserialization is a separate supplied operation: it is not replaced with a
generic JSON-value parse that could change handling of ignored unknown fields.
A successful typed read retains the equation for Mimir's field decoder.

The three previously approved PostgreSQL assumptions remain outside the safe
root. They state external database guarantees; they neither implement
PostgreSQL nor prove Mimir's SQL or lock participation.

## Verification boundary

The final publication check type-checks `spec/Mimir.agda`, whose import closure
includes every remaining safe module. The inventory checker retains the same
34 MCP operations, 30 CLI commands, seven lifecycle groups and ten exact SQL
body bindings. The repository's isolated full check also verifies the unchanged
application; its disposable configuration and database are separate from the
real deployment. Compiler naming/deprecation warnings are reported separately
from errors. Publication evidence belongs to the exact checked commit.

This change does not alter the Rust application, SQL migrations, installed
binaries, version, tags, system configuration or production data. The remaining
specification-gap issues are separate work.

# Registered public operations

`crates/mcp/src/operation_catalogue.rs` defines the existing public tool set.
Each declaration supplies its wire name, typed handler identity and current
committed business-write sites. Graph and learning handlers match closed Rust
enums, without a catch-all branch. Adding a declared operation without adding
its handler is therefore a compile error.

The catalogue associates each handler with its actual advertised input schema.
Its constructor rejects duplicate names, unknown descriptions, missing schemas
and registered operations without descriptions. Tool discovery is generated
from the resulting registered entries, preserving the existing descriptions
and order. It does not use a hardcoded tool count.

The MCP request loop selects an entry by name and calls that entry. A caller
cannot supply an arbitrary function where a `RegisteredOperation` is required;
the fields and construction of those entries are private. The test dispatcher
uses the same catalogue. Unknown names receive an actionable correction with
the advertised names, without executing an alternate tool.

The present Rust input is still `serde_json::Value`, paired with the advertised
schema. Each registered entry checks required fields, input shapes and unknown
fields before calling its handler. Semantic admission and operation-journal
ownership remain separate work; the recovery binding remains #85–#86. An input
schema by itself is not evidence that all business conditions were checked.

Committed boundaries describe actual publication sites, rather than every SQL
query inside a transaction. Propagation and document replacement each publish
through one transaction. Project deletion currently has six independently
committed steps; #125 must replace that sequence with one atomic deletion.
Its declaration is deliberately about the current code, not a claim that the
design is already recoverable.

A boundary can be skipped when execution stops earlier or its branch is not
taken. Grounding and sweeping can revisit the same site for multiple selected
records. `may_repeat` records that control flow; it does not restrict the number
of records, statements, retries or workers. Read-only operations declare no
business-write sites.

The declarations do not yet prove that a handler emits exactly those events.
Instrumentation and the native/specification comparison in #88 and #91 must
check actual occurrences, including repeated ones. The existing Agda
`ToolCatalog.Tool` remains the closed public operation universe, and the
coverage check ties its names to the advertised tools.

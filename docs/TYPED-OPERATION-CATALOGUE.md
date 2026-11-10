# Registered public operations

`crates/core/src/operation_catalogue.rs` defines the existing public tool set
and commit boundaries once, for both core storage and MCP.
Each declaration supplies its wire name, typed handler identity and current
committed write sites, including preparation ownership. Graph and learning handlers match closed Rust
enums, without a catch-all branch. Adding a declared operation without adding
its handler is therefore a compile error.

`crates/mcp/src/operation_catalogue.rs` imports those closed types and associates
each handler with its actual advertised input schema.
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
query inside a transaction. Propagation publishes through one transaction.
Document loading first saves its original complete file preparation and
PostgreSQL-issued chunk identities with an embedding owner. After embedding,
one transaction replaces the complete index, removes old evidence, recomputes
affected beliefs, consumes the owner and saves the original loaded count.
Those are two registered boundaries. A retry uses that saved file even if the
file on disk has since changed. Project deletion has one boundary: its graph
roots, dependent vectors, chunks and learning records publish together. Its
registered token path saves the original result in that same transaction.
This declaration describes the native publication boundary; the independent
intended-outcome and recovery proofs remain separate obligations.

Belief insertion first reserves a PostgreSQL-issued preparation owner. It then
prepares the complete embedding and indexed supporting passages without
publishing a belief. One publication transaction writes the belief, provenance,
vector and grounding links and consumes that owner. These are two registered
boundaries; vector and grounding writes are not separate publication steps.

A review may reserve an owner for each new belief candidate during preparation.
Its one review-publication boundary commits all candidates, their embeddings
and indexed support, the review and its acknowledgement together. The repeated
reservation site describes actual metadata writes without limiting their count.

A boundary can be skipped when execution stops earlier or its branch is not
taken. Grounding can revisit the same site for multiple selected records.
Sweeping now has one deletion publication for its complete eligible set,
dependent vectors, affected survivor updates and saved original count/IDs.
Exact historical repeated sweep plans remain readable, but cannot execute.
`may_repeat` records actual control flow; it does not restrict the number
of records, statements, retries or workers. Read-only operations declare no
business-write sites.

The declarations do not yet prove that a handler emits exactly those events.
Instrumentation and the native/specification comparison in #88 and #91 must
check actual occurrences, including repeated ones. The existing Agda
`ToolCatalog.Tool` remains the closed public operation universe, and the
coverage check ties its names to the advertised tools.

Core and MCP share the declarations rather than maintaining separate lists.
The shared module contains metadata; executable dispatch stays inside the MCP
catalogue. Moving the declarations does not itself enforce stored step order or
prove completion. Those guards remain #123, and public recovery binding remains
#85–#86.

## Stopping a test at an actual commit

The explicit `test-boundaries` Cargo feature instruments the shared saved-step
writer immediately before and after its transaction commits. It is available
to the CLI and MCP test binaries. Ordinary builds contain no controller code
and do not inspect its environment variables.

The controller selects a PostgreSQL-issued operation token, a declared
publication site and `before_commit` or `after_commit`. The process reports its
actual operation, site and saved-step name through a private Unix socket, then
waits for the controller. Sending the byte `c` continues execution. The test
can instead terminate that process while the socket remains open. There is no
sleep, deadline, synthetic database reply or replacement business callback.
The controller settings are `MIMIR_TEST_BOUNDARY_SOCKET`,
`MIMIR_TEST_BOUNDARY_TOKEN`, `MIMIR_TEST_BOUNDARY_SITE` and
`MIMIR_TEST_BOUNDARY_PHASE`. Keep the socket in a private directory with a path
accepted by the operating system.

The project-deletion session test exercises both sides of its declared commit.
Before commit, terminating the process preserves the project and its vectors.
After commit, the project and vectors are gone even though the caller received
no answer. A later real MCP process retries the original token and arguments:
both cases finish with no project-owned rows or vectors, preserve another
project, and return the original deleted count on subsequent retries.

Run this selected test through the disposable-database test environment with
`cargo test -p mimir-mcp --features test-boundaries --test operation_protocol_session
project_deletion_retries_after_real_process_exit_at_each_commit_side`.
This checks the real commit boundary and retry behavior for deletion. Extending
the operation matrix and comparing observations with the Agda-owned intended
functions remain the separate planned harness work.

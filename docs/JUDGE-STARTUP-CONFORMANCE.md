# Judge startup and MCP client conformance

Status: completed and verified on 2026-10-31. This closes the scoped Rust
startup/handshake gap recorded in FORMAL-REBUILD.md. Other Rust conformance work
remains open. No binary was installed.

Approved scope: Rust judge startup, MCP handshake, shared request ID/deadline,
and owned-child cleanup. Version changes, installation, live models, production
data, system configuration and harness changes are excluded.

## Contract mapping before implementation

The governing source is the checked specification recorded in
`FORMAL-BEHAVIOR-VERIFICATION.json`. No specification change is needed.

| Obligation | Governing definition/law | Rust path and required action |
| --- | --- | --- |
| Successful startup performs initialize, initialized notification, tools/list, learning_capabilities, in that order | `JudgeHandshake.Contract.successfulStartupOrder`; `completedUsesAtMostFourEvents` | `mcp::Client::start`: add the missing final capability tool call and admission; every error returns before `run_inner` selects work. |
| Required host tools exist but are not exposed to the model | `JudgeToolCatalogue.demands`, `Covered.host` | `validate_tools`: require learning_capabilities with object input schema; omit it and pending_experiences from allowed_tools. |
| Exact required nested review property types | `JudgeToolCatalogue.review`; `McpToolAdvertisement.Matches` | Add rationale and all nine typed array fields to the existing identity-field checks. |
| First matching advertisement wins; exposed definitions remain original | `McpToolAdvertisement.First`, `firstUnique`; `everyPublishedDefinitionChecked` | Preserve first-match lookup and cloning of advertised model definitions, including optional tools. Extract the pure admission function for direct verification. |
| Contract version 2, assessment model 1, and all four support flags true | `LearningCapabilities.fields`, `validate`, `Compatible`; `incompatibleCapabilitiesStop` | Add a pure decoder/admission check using exact JSON integer/boolean types. Ignore unrelated object keys as the specification does. A binary version string supplies no compatibility evidence. |
| Every request consumes one ID before transport; overflow sends nothing and retains the counter | `JudgeMcpLifecycle.Calls.Call.full/exchanged`; `Chain.full/next` | Existing checked_add path conforms; retain it and verify success, overflow and rejected transport boundaries. Notifications consume no ID. |
| One deadline shared across handshake and all later calls | `JudgeHandshakeBinding.Receipt`; `Calls.deadlineUnchanged` | Existing Client.deadline and remaining() conform; the added capability call uses the ordinary tool/request path and cannot reset the deadline. |
| Failed handshake drops its owned child before return; final drop targets that child's process group and child | `JudgeClientStartup.Started.handshakeFailed`; `JudgeMcpLifecycle.dropClient`; `ownerPreserved` | Existing local Client and Drop cover all ? returns after construction. Preserve them; verify rejected capability, ordinary drop and timeout with owned disposable children/descendants. |
| No judge capability requirement in ordinary standalone MCP/core startup | `McpServiceProcess`, `ServiceConnection` | Restrict production changes to crates/cli/src/judge/mcp.rs. |

## Correctness argument to preserve

The successful start branch must pass each earlier fallible call before it can
reach the next one. Catalogue admission iterates the same ordered demands as
the formal relation. Each present tool is the first matching advertisement;
every checked property must match its exact JSON string type. Only model
demands are copied to the output. Capability admission checks both integer
versions and every boolean support flag before returning success. Thus the new
return point is reachable only after the existing handshake's formal admission
conditions. The capability request uses the existing request and transport
functions, preserving ID allocation, bounds, deadline and error propagation.

Rust ownership drops the partially initialized Client on a failed handshake.
The Drop implementation obtains the ID from its owned Child, which was put in
its own process group before exec; it does not select unrelated processes by
name or session ancestry. OS signal delivery remains the dependency boundary
described in the formal model.

This is an explicit source-to-contract argument. It is not a machine-checked
Rust refinement theorem. Finite subprocess tests supplement that argument.

## Planned verification

- Catalogue admission: each newly required field, absent/malformed host tool,
  invalid first duplicate, optional tools, and unchanged exposed definitions.
- Capability admission: exact versions, all support flags, missing/wrong JSON
  types, and accepted unrelated fields.
- Actual subprocess startup: full ordered transcript, IDs, configured path,
  shared deadline, overflow without sending, and no selection after rejection.
- Child cleanup: ordinary drop, rejected handshake and existing timeout paths,
  restricted to children created by these fixtures.
- Existing judge fixture tests that pass through Client::start.

All fixtures use disposable local files and processes, without a database,
network access or a live model. Verification results will be appended after
implementation. The existing Agda verification receipt remains valid because
the governing formal sources are unchanged.

## Implementation and verification receipt

The production change is confined to `crates/cli/src/judge/mcp.rs`: the host
requires the capability advertisement, validates the complete typed review
schema, calls learning_capabilities after tools/list, decodes all fields, and
admits contract version 2 / assessment model 1 with all four flags true.
Capability and pending-selection tools remain host-only. Original advertised
model definitions, first-match behavior and optional-tool behavior are retained.

Source comparison confirms the request, transport, deadline, tool-envelope
decoder and Client Drop blocks are byte-for-byte unchanged from the stage input.
The stage input hashes are `/tmp/mimir-judge-stage-input-hashes.json`; the full
production diff is `/tmp/mimir-judge-production-diff-hluqe7d4.log`.

Test-only changes update the existing retry fixture to the typed handshake,
preserve exact u64 IDs without jq rounding, add request/PID capture for owned
subprocesses, and move the timeout fixture's PID file into a unique temporary
path. New checks are in `crates/cli/src/judge/mcp_startup_tests.rs`.

All selected tests passed on their first run after implementation:

| Check | Result | Complete log |
| --- | --- | --- |
| MCP startup/admission/lifecycle | 7 passed, 0 failed | `/tmp/mimir-judge-mcp-sJQJuSxd.log` |
| Existing runner fixtures | 4 passed, 0 failed | `/tmp/mimir-judge-runner-sEDJcnDy.log` |
| Existing evidence/correction fixtures | 3 passed, 0 failed | `/tmp/mimir-judge-evidence-6PIrvO8y.log` |
| Rust formatting check | exit 0 | `/tmp/mimir-judge-format-check-s5NCyPo0.log` |
| Scoped whitespace check | exit 0 | `/tmp/mimir-judge-diff-check-JKEkN6bW.log` |

Each log has a retained `.exit` file. Tests used the existing Nix development
environment, `cargo test --locked --offline -p mimir --bin mimir`, and the
specific `judge::mcp::`, `judge::runner::tests::` and `judge::evidence::tests::`
filters. The runner invocation explicitly skipped `isolated_mcp_review_cycle`,
which can connect to a configured database. No database/model trial ran.

The subprocess checks observed the ordered four-event handshake, IDs 1/2/3,
notifications without IDs, unchanged deadline after later calls, the final
legal u64 ID, overflow/expired requests without transmitted frames, and stopped
owned child/descendant processes after ordinary drop or rejected capability.
The existing malformed-startup and timeout cleanup checks also passed.

The source hash audit found only two changed pre-existing crate files:
`mcp.rs` and `retry_fixture.sh`; the sole new crate file is the startup test
module. All 638 formal-source hashes still match the successful aggregate
receipt. All four crate version declarations remain 2.1.0; dependencies,
Cargo.lock, core/MCP-server/notification sources and system configuration were
not changed in this stage.

Limits: this is contract-derived implementation, reviewed source correspondence
and focused executable verification. It does not claim a machine-checked Rust
refinement theorem, a live-model trial, or verification of installed binaries.

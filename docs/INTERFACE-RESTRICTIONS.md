# MCP and CLI restrictions to remove

Inventory for [#58](https://github.com/kamysh/mimir/issues/58), inspected at
`origin/main` commit `a402f463441c677db82863fe4805e30fbfbe7c55`.
These are observations of current code, not approved exceptions. No restriction
listed here is approved for retention. Omission must have an explicit meaning;
zero is invalid selection input and must receive an actionable correction.

Scope: `crates/mcp/src/main.rs`, `crates/mcp/src/learning.rs`, and the public CLI
paths in `crates/cli/src/main.rs` and `configuration.rs`. Core restrictions are
tracked by [#57](https://github.com/kamysh/mimir/issues/57); the judge's private
MCP client, watcher, diagnostics, and email are covered by
[#59](https://github.com/kamysh/mimir/issues/59). Script/configuration and formal
restrictions are covered by [#60](https://github.com/kamysh/mimir/issues/60).
Source line numbers below belong to the inspected baseline.

## Public MCP selection

| Source | Current behavior and consequence | Follow-up |
|---|---|---|
| [main.rs:239](../crates/mcp/src/main.rs#L239), [main.rs:594](../crates/mcp/src/main.rs#L594), `list_beliefs` | Both schema and handler impose a maximum page size of 10. A positive request for 11 is rejected. Omitting limit instead returns the legacy full array; specifying it changes the result to a page object. Offset without limit is rejected. | Remove the ceiling and define explicit selection in [#103](https://github.com/kamysh/mimir/issues/103); keep result/continuation meaning clear in [#102](https://github.com/kamysh/mimir/issues/102). |
| [main.rs:294](../crates/mcp/src/main.rs#L294), [main.rs:651](../crates/mcp/src/main.rs#L651), `query_relevant` | Omitted limit selects 10 beliefs. Schema admits zero, which bypasses the final core cut. A string, negative number, or fractional value silently becomes 10 because `as_u64().unwrap_or(10)` conflates invalid and missing fields. | [#103](https://github.com/kamysh/mimir/issues/103), with wrong-type corrections in [#81](https://github.com/kamysh/mimir/issues/81). |
| [main.rs:296](../crates/mcp/src/main.rs#L296), [main.rs:664](../crates/mcp/src/main.rs#L664), `query_relevant` evidence | Omitted evidence selection keeps at most three passages per belief. Invalid numeric types silently become three; zero bypasses the core cut. A fourth supporting passage disappears from the result. | [#103](https://github.com/kamysh/mimir/issues/103) and [#104](https://github.com/kamysh/mimir/issues/104). |
| [main.rs:370](../crates/mcp/src/main.rs#L370), [main.rs:779](../crates/mcp/src/main.rs#L779), `query_document` | Defaults to five passages; zero means all; malformed numeric values silently become five. | [#103](https://github.com/kamysh/mimir/issues/103) and [#81](https://github.com/kamysh/mimir/issues/81). |
| [learning.rs:118](../crates/mcp/src/learning.rs#L118), `lesson_assessment_history` | Handler defaults to 20 entries although the schema has no advertised default. | [#103](https://github.com/kamysh/mimir/issues/103) and schema agreement [#102](https://github.com/kamysh/mimir/issues/102). |
| [learning.rs:43](../crates/mcp/src/learning.rs#L43), [learning.rs:133](../crates/mcp/src/learning.rs#L133), `explain_belief` | Schema and handler default to 10 reviews. | [#103](https://github.com/kamysh/mimir/issues/103). |
| [learning.rs:52](../crates/mcp/src/learning.rs#L52), [learning.rs:161](../crates/mcp/src/learning.rs#L161), `pending_experiences` | Defaults to 10 pending experiences. This tool-level default is distinct from the judge's batch-size quota. | [#103](https://github.com/kamysh/mimir/issues/103); judge quota removal is [#162](https://github.com/kamysh/mimir/issues/162). |
| [learning.rs:65](../crates/mcp/src/learning.rs#L65), [learning.rs:174](../crates/mcp/src/learning.rs#L174), `query_learning_context` | Defaults to five selected beliefs and five patterns through the shared core call. | [#103](https://github.com/kamysh/mimir/issues/103) and [#104](https://github.com/kamysh/mimir/issues/104). |
| [learning.rs:81](../crates/mcp/src/learning.rs#L81), `limit` | Parses nonnegative values, including zero, although these learning schemas require a positive value and the core rejects zero. Unlike the general query handlers, a wrong type here produces an error instead of a default. | Unify selection and corrections in [#103](https://github.com/kamysh/mimir/issues/103), [#81](https://github.com/kamysh/mimir/issues/81), and [#102](https://github.com/kamysh/mimir/issues/102). |
| [main.rs:716](../crates/mcp/src/main.rs#L716), `list_evidence` | The public tool has no selection field and requests all evidence by passing the internal zero sentinel. No extra evidence count is imposed here. | Replace the sentinel with an explicit all-results value alongside the core contract in [#104](https://github.com/kamysh/mimir/issues/104). |

For example, `{"context":"deployment","limit":"20"}` must elicit an
explanation that `limit` must be a positive integer and a proposed corrected
request. It must not silently run with ten results. A request with `limit: 0`
must also be corrected, not interpreted as all results.

## CLI selection and content shortening

| Source | Current behavior | Follow-up |
|---|---|---|
| [main.rs:55](../crates/cli/src/main.rs#L55), [main.rs:66](../crates/cli/src/main.rs#L66), [main.rs:475](../crates/cli/src/main.rs#L475), [main.rs:527](../crates/cli/src/main.rs#L527) | `list` and `patterns` default to zero; zero skips truncation, and a positive caller value selects that many records. | Explicit omission/all selection and invalid-zero correction in [#105](https://github.com/kamysh/mimir/issues/105). |
| [main.rs:76](../crates/cli/src/main.rs#L76), [main.rs:303](../crates/cli/src/main.rs#L303) | `query` defaults to 10 results and `doc query` to five; both document zero as all. | [#105](https://github.com/kamysh/mimir/issues/105). |
| [main.rs:563](../crates/cli/src/main.rs#L563), `cmd_query` | `--evidence` always requests at most three supporting passages per belief, regardless of the caller's result selection. | Hidden evidence selection removal in [#104](https://github.com/kamysh/mimir/issues/104). |
| [main.rs:648](../crates/cli/src/main.rs#L648), `cmd_evidence` | Requests all evidence via the core zero sentinel. Display separately shortens each passage. | [#104](https://github.com/kamysh/mimir/issues/104) removes the sentinel; [#167](https://github.com/kamysh/mimir/issues/167) restores full output. |
| [main.rs:401](../crates/cli/src/main.rs#L401), `trunc` | Trims surrounding whitespace and replaces content beyond a supplied character width with an ellipsis. This affects presentation and, in hooks, the query sent to retrieval. It does not shorten database rows. | [#167](https://github.com/kamysh/mimir/issues/167) for ordinary CLI output; [#168](https://github.com/kamysh/mimir/issues/168) for hooks. |
| [main.rs:502](../crates/cli/src/main.rs#L502), [main.rs:580](../crates/cli/src/main.rs#L580), [main.rs:615](../crates/cli/src/main.rs#L615), [main.rs:692](../crates/cli/src/main.rs#L692) | Belief text in listing, query, and intervention output is shortened to 70 characters. | [#167](https://github.com/kamysh/mimir/issues/167). |
| [main.rs:541](../crates/cli/src/main.rs#L541), [main.rs:542](../crates/cli/src/main.rs#L542) | Pattern situation and approach are each shortened to 40 characters. | [#167](https://github.com/kamysh/mimir/issues/167). |
| [main.rs:590](../crates/cli/src/main.rs#L590), [main.rs:663](../crates/cli/src/main.rs#L663), [main.rs:810](../crates/cli/src/main.rs#L810) | Query/evidence passages are shortened to 100 characters; document query passages to 120. An agent can miss the clause that explains a returned passage. | [#167](https://github.com/kamysh/mimir/issues/167). |
| [main.rs:860](../crates/cli/src/main.rs#L860), [main.rs:864](../crates/cli/src/main.rs#L864), [main.rs:909](../crates/cli/src/main.rs#L909) | Contradiction descriptions are shortened to 50 characters and re-embedding progress descriptions to 60. | [#167](https://github.com/kamysh/mimir/issues/167). |
| [main.rs:1105](../crates/cli/src/main.rs#L1105), `cmd_hook_prompt` | Shortens the retrieval query to 500 characters and requests five beliefs. The ending of a long prompt cannot influence matching. | [#168](https://github.com/kamysh/mimir/issues/168). |
| [main.rs:1153](../crates/cli/src/main.rs#L1153), [main.rs:1171](../crates/cli/src/main.rs#L1171), `cmd_hook_pretooluse` | Shortens the path/command query to 200 characters, requests three beliefs, and shortens each returned belief to 200 characters. | [#168](https://github.com/kamysh/mimir/issues/168). |
| [main.rs:977](../crates/cli/src/main.rs#L977), [main.rs:1085](../crates/cli/src/main.rs#L1085) | Existing set-project/Stop-hook messages shorten working-belief text to 160 characters. | [#168](https://github.com/kamysh/mimir/issues/168); this inventory does not approve enabling those legacy hooks or their blocking policy. |

The CLI retention argument at [main.rs:135](../crates/cli/src/main.rs#L135) and
MCP `grace_hours` at [main.rs:282](../crates/mcp/src/main.rs#L282) both default to
24 hours and allow per-call choice. [#142](https://github.com/kamysh/mimir/issues/142)
must replace that with the user's explicitly configured retention policy and
refuse sweeping when unset. Removing a wait must not cause immediate deletion
by accident or allow an agent to choose a destructive policy.

## Transport, dependency checks, and correction behavior

- The `insert_belief` provenance schema at
  [main.rs:116](../crates/mcp/src/main.rs#L116) declares `maxLength: 2048` for
  `provenance.reference`. A client enforcing that schema can refuse a longer
  valid source reference. The core `IndependentProvenance::validate` checks
  nonempty trimmed text, without that length ceiling, so schema and runtime
  disagree. Remove the ceiling in [#106](https://github.com/kamysh/mimir/issues/106)
  and enforce agreement in [#102](https://github.com/kamysh/mimir/issues/102).
- The public server's [read loop](../crates/mcp/src/main.rs#L855) reads complete
  newline-delimited requests into a growing string. It has no explicit byte
  count or wall-clock deadline. Result serialization and `write_all` have no
  application response-size ceiling in this path. This does not describe an
  external client's limits or the judge's separate transport.
- `Cargo.lock` pins serde_json `1.0.154`. Its `src/de.rs` initializes
  `remaining_depth` to 128. The server uses plain `serde_json::from_str` at
  [main.rs:866](../crates/mcp/src/main.rs#L866), so deeply nested JSON can be
  refused by that dependency even without an application byte cap.
  [#106](https://github.com/kamysh/mimir/issues/106) must address that inherited
  content restriction and safe handling of nesting. Any proposed retained
  dependency constraint requires evidence and user approval through
  [#112](https://github.com/kamysh/mimir/issues/112); none is granted here.
- The [parse-error branch](../crates/mcp/src/main.rs#L866) sends a parse error
  and continues reading. The [tool-error branch](../crates/mcp/src/main.rs#L910)
  returns a generic JSON-RPC error, with structured `Refusal` data only for that
  particular core error type. Neither establishes the required uniform
  explanation, proposed correction, and continued agent dialogue.
  [#75](https://github.com/kamysh/mimir/issues/75),
  [#80](https://github.com/kamysh/mimir/issues/80),
  [#81](https://github.com/kamysh/mimir/issues/81), and
  [#82](https://github.com/kamysh/mimir/issues/82) own that behavior. Do not report
  every malformed request as a process crash: these branches continue serving.
- Numeric domain validation (probability/weight in `[0,1]`, nonnegative
  revisions and offsets), UUID syntax, required fields, and known enum values
  define what a field means. They are not work quotas. Invalid values still
  need actionable corrections, not guessed replacements. Existing
  `additionalProperties: false` declarations do not prove the runtime rejects
  unknown fields consistently; schema/runtime agreement remains
  [#102](https://github.com/kamysh/mimir/issues/102).
- Apart from the provenance reference ceiling above, no schema `maxLength`,
  `maxItems`, or explicit request/response byte cap was found in these public
  handler files. CLI output precision formats numeric
  values, while the fixed-width text helper loses actual content as listed
  above. The CLI configuration report prints the core logging bounds; their
  removal is tracked by [#109](https://github.com/kamysh/mimir/issues/109).

## Verification boundary

Source searches covered selection/defaults, size checks, timeouts, truncation
(including the separate `trunc` helper), request parsing, and output writes.
Relevant branches and the pinned parser were read. Focused verification checks
the linked source locations, stated constants and branches, follow-up issue
references, and whitespace. This documentation change does not claim runtime
removal, successful recovery, or a tested live deployment.

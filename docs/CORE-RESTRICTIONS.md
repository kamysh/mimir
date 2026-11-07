# Core restrictions to remove or resolve

Inventory for [#57](https://github.com/kamysh/mimir/issues/57), inspected at
`origin/main` commit `a402f463441c677db82863fe4805e30fbfbe7c55`.
This records current behavior, not approval to retain it. No restriction in this
inventory has an approved exception. Follow-up changes must remove arbitrary
restrictions; any proposed exception needs the user's explicit approval and a
concrete explanation of the consequence of removing it.

The scope is `crates/core/src`: storage, inference, embedding, and the shared
configuration/logging code they use. MCP/CLI, watcher/mail, scripts, migrations,
and formal-model inventories are tracked separately in
[#58](https://github.com/kamysh/mimir/issues/58),
[#59](https://github.com/kamysh/mimir/issues/59), and
[#60](https://github.com/kamysh/mimir/issues/60). Locations below refer to this
baseline; later edits can move lines.

## Work stopped or information dropped

| Source | Current behavior and a concrete consequence | Required follow-up |
|---|---|---|
| [embed.rs:226](../crates/core/src/embed.rs#L226), `download_blocking` | Download stops after 600 seconds, even if still progressing. A slow first model download fails for elapsed time alone. | Remove the deadline in [#107](https://github.com/kamysh/mimir/issues/107). |
| [embed.rs:227](../crates/core/src/embed.rs#L227), `download_blocking` | Only 10 HTTP redirects are followed. An otherwise valid longer redirect chain fails. | Remove the arbitrary hop count in [#107](https://github.com/kamysh/mimir/issues/107); any different restriction requires user approval. |
| [embed.rs:112](../crates/core/src/embed.rs#L112) and [embed.rs:343](../crates/core/src/embed.rs#L343), `embed_with_state` | Token sequence length is reduced to 512; only that prefix is copied into the model input. A long passage's ending is silently omitted from its embedding. | [#113](https://github.com/kamysh/mimir/issues/113) removes silent truncation. [#112](https://github.com/kamysh/mimir/issues/112) must establish any actual model constraint and obtain approval for its handling; the constant alone proves nothing about the model's requirements. |
| [embed.rs:129](../crates/core/src/embed.rs#L129) and [embed.rs:334](../crates/core/src/embed.rs#L334), `LocalBackend` | Positive configured `batch_size` divides an embedding request into chunks; all chunks are processed. Zero secretly means process the whole input together. This is a scheduling size, not a cap on the number of returned embeddings. | Resolve the configuration and dependency behavior in [#117](https://github.com/kamysh/mimir/issues/117), [#112](https://github.com/kamysh/mimir/issues/112), and the owned local worker in [#70](https://github.com/kamysh/mimir/issues/70). Do not carry forward the zero convention or claim that every later chunk was dropped. |
| [inference.rs:178](../crates/core/src/inference.rs#L178), [inference.rs:245](../crates/core/src/inference.rs#L245), `propagate_core` | Stops after 50 passes. If unfinished, warns and returns the current values through the successful result path. A larger graph can therefore publish an unfinished inference result. | Define completion in [#114](https://github.com/kamysh/mimir/issues/114), then remove the cutoff in [#115](https://github.com/kamysh/mimir/issues/115). |
| [inference.rs:179](../crates/core/src/inference.rs#L179) and [inference.rs:274](../crates/core/src/inference.rs#L274), `propagate_core` | Calls the calculation converged when the largest change in mean is below `1e-9`. This is an approximation criterion, not an elapsed-time limit, and does not itself establish that the complete persisted evidence state is final. | [#114](https://github.com/kamysh/mimir/issues/114) must give an explicit completion meaning. The tolerance is not an approved exception. |
| [lib.rs:631](../crates/core/src/lib.rs#L631), `query_relevant` | Vector candidates are restricted to `max(limit * 4, 20)`, or 50 when limit is zero, before graph expansion and ranking. A relevant vector match outside that window cannot become a seed. | Remove the hidden search window in [#104](https://github.com/kamysh/mimir/issues/104); positive caller selection must not create a second unexplained cutoff. |
| [lib.rs:227](../crates/core/src/lib.rs#L227), `auto_ground_belief` | Searches only the nearest 20 chunks before checking project compatibility. Twenty chunks from other projects can hide a valid supporting passage in the right project. | Remove the search ceiling in [#104](https://github.com/kamysh/mimir/issues/104); enforce complete pre-publication grounding in [#96](https://github.com/kamysh/mimir/issues/96) and [#97](https://github.com/kamysh/mimir/issues/97). |
| [lib.rs:262](../crates/core/src/lib.rs#L262), `auto_ground_chunks` | Searches only the nearest 20 beliefs before project filtering. Loading a document can miss another compatible belief beyond that window. | [#104](https://github.com/kamysh/mimir/issues/104), with the document-load outcome in [#143](https://github.com/kamysh/mimir/issues/143). |
| [store.rs:2122](../crates/core/src/store.rs#L2122), `list_beliefs_page` | Rejects page sizes above 10, regardless of the caller's positive request. | Remove the imposed ceiling in [#103](https://github.com/kamysh/mimir/issues/103) and [#104](https://github.com/kamysh/mimir/issues/104). |
| [operations.rs:23](../crates/core/src/operations.rs#L23) and [operations.rs:65](../crates/core/src/operations.rs#L65), `Logging` | Defaults to 1,048,576 bytes per file and four retained files; only 4,096–16,777,216 bytes and 1–16 files are accepted. Logs outside the retained set disappear. | Remove the file/count restrictions in [#109](https://github.com/kamysh/mimir/issues/109), with configuration compatibility in [#117](https://github.com/kamysh/mimir/issues/117). |
| [operations.rs:202](../crates/core/src/operations.rs#L202) and [operations.rs:219](../crates/core/src/operations.rs#L219), `Logging::write` | Cuts an oversized write to the byte ceiling, shortens oversized existing files, and rotates away older data. The lost error details cannot be recovered from these files. | Preserve complete diagnostics in [#108](https://github.com/kamysh/mimir/issues/108) and remove retention/truncation in [#109](https://github.com/kamysh/mimir/issues/109). |
| [operations.rs:257](../crates/core/src/operations.rs#L257), `Logging::event` | Keeps only the first 8,192 non-control characters of a message. | [#108](https://github.com/kamysh/mimir/issues/108) and [#109](https://github.com/kamysh/mimir/issues/109). |
| [operations.rs:286](../crates/core/src/operations.rs#L286), `LogWriter::write` | Keeps at most `min(max_file_bytes, 32768)` bytes in an event buffer but reports the entire write as accepted. A long tracing event loses its ending silently. | [#108](https://github.com/kamysh/mimir/issues/108) and [#109](https://github.com/kamysh/mimir/issues/109). |

## Caller selection and inconsistent zero handling

These paths also need the explicit selection contract. A caller asking for a
positive number of results is different from the application imposing its own
maximum. An omitted selection must have an explicit meaning; zero is invalid,
not a substitute for “all.” Existing zero behavior below describes a bug to
remove, not the proposed API.

| Source | Current behavior | Required follow-up |
|---|---|---|
| [lib.rs:805](../crates/core/src/lib.rs#L805), `query_relevant`; [lib.rs:883](../crates/core/src/lib.rs#L883), `query_document` | Positive limits select results; zero avoids the final cut. The hidden vector seed window still applies to relevant-belief search. | [#104](https://github.com/kamysh/mimir/issues/104), with request correction in [#75](https://github.com/kamysh/mimir/issues/75). |
| [lib.rs:949](../crates/core/src/lib.rs#L949), `evidence_for_belief`; [lib.rs:1014](../crates/core/src/lib.rs#L1014), `query_relevant_grounded` | Evidence is truncated to the caller's positive value; zero bypasses that truncation. | [#104](https://github.com/kamysh/mimir/issues/104). |
| [store.rs:1651](../crates/core/src/store.rs#L1651), [store.rs:1723](../crates/core/src/store.rs#L1723), [store.rs:1754](../crates/core/src/store.rs#L1754), [store.rs:1781](../crates/core/src/store.rs#L1781), [store.rs:1824](../crates/core/src/store.rs#L1824) | All five vector search variants generate SQL `LIMIT` for positive values and omit it for zero. | [#104](https://github.com/kamysh/mimir/issues/104) must change the core/store contract together, without a zero sentinel. |
| [learning.rs:482](../crates/core/src/learning.rs#L482) and [learning.rs:520](../crates/core/src/learning.rs#L520), `query_learning_context` | Requires a positive limit; limits both selected beliefs and ranked patterns. No additional fixed pattern ceiling was found here. | [#104](https://github.com/kamysh/mimir/issues/104) and [#135](https://github.com/kamysh/mimir/issues/135) for the explicit result contract. |
| [store/learning.rs:153](../crates/core/src/store/learning.rs#L153), `lesson_assessment_history` | Requires positive limit; requests one extra SQL row to determine whether another page exists. The extra row is not returned. | [#104](https://github.com/kamysh/mimir/issues/104); preserve accurate continuation when defining selection. |
| [store/learning.rs:190](../crates/core/src/store/learning.rs#L190), `list_experiences_excluding` | Requires positive limit and applies it in SQL, including to judge backlog selection. | [#104](https://github.com/kamysh/mimir/issues/104) and judge quota removal [#162](https://github.com/kamysh/mimir/issues/162). |
| [store/learning.rs:905](../crates/core/src/store/learning.rs#L905), `reviews_for_belief` | Requires positive limit; fetches and sorts matching reviews, then selects a page and reports continuation. | [#104](https://github.com/kamysh/mimir/issues/104). |

## Decisions and dependency constraints still to resolve

- `lib.rs:45`, `auto_ground_belief`, and `auto_ground_chunks` use a fixed cosine
  score threshold of `0.80` to admit supporting passages. It is a content
  acceptance threshold, not a result count. Its suitability for actual support
  must be resolved in [#95](https://github.com/kamysh/mimir/issues/95) and
  [#96](https://github.com/kamysh/mimir/issues/96); it is not approved merely
  because the current implementation uses it.
- `lib.rs:531` rounds a caller-supplied retirement period to minutes before
  deleting eligible beliefs. Do not turn removal of a wait into immediate
  destructive deletion. [#142](https://github.com/kamysh/mimir/issues/142) must
  use the user's explicitly configured `[retirement].grace_hours`, refuse an
  unset policy, and remove per-call discretion. The existing caller argument
  does not implement that agreement.
- `Cargo.lock` pins reqwest `0.12.28`. `VoyageBackend::new` and
  `OpenAiBackend::new` use its default asynchronous HTTP client. Inspection of
  the pinned dependency's `src/async_impl/client.rs` confirms no default total,
  read, or connect timeout, but a default redirect policy; `src/redirect.rs`
  sets that policy to 10 hops. Thus omitting `.timeout(...)` alone does not
  remove the redirect ceiling. [#107](https://github.com/kamysh/mimir/issues/107)
  owns the application policy for all embedding HTTP clients. No provider
  quota or model size exception has been established or approved by this audit;
  [#112](https://github.com/kamysh/mimir/issues/112) owns external evidence and
  approval requests.
- `store.rs:2123` and `store/learning.rs:153–162,192` check or convert page
  values against PostgreSQL's signed integer representation; history's extra
  row can also overflow that representation. These are representation edges,
  not a reason to impose another smaller arbitrary maximum. Resolve them in
  [#112](https://github.com/kamysh/mimir/issues/112) and
  [#104](https://github.com/kamysh/mimir/issues/104), with an actionable
  correction rather than truncation or guessed replacement values.

## Checked candidates that are not work cutoffs

- `graph.rs:13,23,56,66` validates or clamps probabilities/confidence to their
  `[0,1]` domain. `KAPPA_MIN`, `KAPPA_MAX`, and `EVIDENCE_UNIT` define the existing
  belief-strength mapping; accumulated posterior strength is not cut to
  `KAPPA_MAX`. Ranking weights in `lib.rs` order results. These change the
  calculation, not how many operations are allowed to run. Their numerical
  correctness is outside this inventory; they do not authorize a runtime cap.
- `embed.rs:258` copies downloads through a 64 KiB buffer in a loop until EOF;
  it does not limit download size. `Vec::with_capacity` reserves space without
  restricting growth. `max(1)` makes the batch chunk size valid for empty input;
  it does not discard a nonempty request.
- `documents.rs` splits Markdown at headings and retains section contents;
  there is no fixed section-size truncation in that parser.
- `store.rs:2027–2109` discovers distinct reachable graph nodes without a depth
  cutoff. `assessments_for_beliefs` returns its complete aggregation and an
  always-false `assessments_truncated` flag; that name alone is not evidence of
  a live assessment cap.
- `db.rs::connect` does not set an application connection or statement timeout.
  It does not establish what a deployed PostgreSQL server or operating system
  is configured to enforce. No live configuration was inspected or changed.
- `operations.rs::upgrade` removes retired LLM timeout/call/token/budget keys;
  their appearance in upgrade tests is not a live core limit. Test sample sizes
  and simulated belief ages are fixtures, not runtime waits.

## Verification boundary

The inventory was built from source searches for timeouts, sleeps, intervals,
limits, loops, truncation, numeric checks, and dependency settings, followed by
reading each relevant implementation. It records code behavior, not a live
incident reproduction or a claim that the listed problems are fixed. Verify
source links, stated constants/branches, issue references, and whitespace for
this documentation-only change. Runtime and formal proofs belong to the
linked implementation issues.

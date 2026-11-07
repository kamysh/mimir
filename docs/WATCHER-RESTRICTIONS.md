# Watcher, notification, and diagnostic restrictions

Inventory for [#59](https://github.com/kamysh/mimir/issues/59), inspected at
`origin/main` commit `a402f463441c677db82863fe4805e30fbfbe7c55`.
This describes existing behavior. None of these restrictions is an approved
exception. Follow-up issues must remove arbitrary limits; an exception needs
the user's explicit approval based on a concrete scenario.

Scope: `crates/cli/src/judge`, `crates/notifications/src`, and the shared core
logger. Other core restrictions belong to [#57](https://github.com/kamysh/mimir/issues/57),
public interfaces to [#58](https://github.com/kamysh/mimir/issues/58), and
configuration/scripts/formal inventories to [#60](https://github.com/kamysh/mimir/issues/60).
Line numbers refer to this baseline, not later unmerged fixes.

## Scheduling and delivery

| Source | Existing behavior and consequence | Removal work |
|---|---|---|
| [judge/mod.rs:61](../crates/cli/src/judge/mod.rs#L61), [judge/mod.rs:174](../crates/cli/src/judge/mod.rs#L174), [judge/mod.rs:188](../crates/cli/src/judge/mod.rs#L188) | Watcher defaults to a 300-second sleep after every run, including a successful batch with more work available. New work and configuration changes wait for that sleep. | Immediate successful continuation [#63](https://github.com/kamysh/mimir/issues/63); database notification [#61](https://github.com/kamysh/mimir/issues/61), subscription race [#62](https://github.com/kamysh/mimir/issues/62), idle wait [#64](https://github.com/kamysh/mimir/issues/64), reconnect [#65](https://github.com/kamysh/mimir/issues/65), and configuration file events [#66](https://github.com/kamysh/mimir/issues/66). |
| [judge/mod.rs:65](../crates/cli/src/judge/mod.rs#L65), [judge/mod.rs:337](../crates/cli/src/judge/mod.rs#L337) | After three consecutive failures by default, next delay becomes at least 3,600 seconds. This delays recovery; it does not stop after three attempts. | Remove the failure-count/backoff policy in [#67](https://github.com/kamysh/mimir/issues/67). |
| [judge/config.rs:88](../crates/cli/src/judge/config.rs#L88), [judge/runner.rs:467](../crates/cli/src/judge/runner.rs#L467), [judge/runner.rs:485](../crates/cli/src/judge/runner.rs#L485) | Default batch size is five. Queue selection passes that limit and rejects more returned records. Combined with the post-batch sleep, a large backlog drains slowly even when each review succeeds. | Remove the work quota in [#162](https://github.com/kamysh/mimir/issues/162); do not replace it with zero-as-all. |
| [judge/mod.rs:158](../crates/cli/src/judge/mod.rs#L158), [judge/notification.rs:164](../crates/cli/src/judge/notification.rs#L164) | The review path awaits notification submission, and the watcher awaits daily digest work before continuing. A stalled delivery prevents progress until it returns or its separate mail timeout fires. | Owned background delivery with cancellation cleanup in [#68](https://github.com/kamysh/mimir/issues/68), independently of timeout removal. |
| [notifications/config.rs:61](../crates/notifications/src/config.rs#L61), [notifications/smtp.rs:99](../crates/notifications/src/smtp.rs#L99), [notifications/smtp.rs:129](../crates/notifications/src/smtp.rs#L129), [notifications/oauth.rs:87](../crates/notifications/src/oauth.rs#L87) | Mail timeout defaults to 15 seconds, is restricted to 1–300 seconds, and is applied in the SMTP transport, an outer SMTP timeout, and OAuth HTTP. A slow valid delivery/refresh is cut off. | Remove mail deadlines in [#110](https://github.com/kamysh/mimir/issues/110), with compatibility in [#117](https://github.com/kamysh/mimir/issues/117). |
| [notifications/config.rs:64](../crates/notifications/src/config.rs#L64), [notifications/lib.rs:490](../crates/notifications/src/lib.rs#L490) | Alert retries wait 300 seconds by default; configuration accepts only 1–86,400 seconds. | Remove arbitrary delivery delay in [#110](https://github.com/kamysh/mimir/issues/110). |
| [notifications/config.rs:67](../crates/notifications/src/config.rs#L67), [notifications/lib.rs:481](../crates/notifications/src/lib.rs#L481), [notifications/lib.rs:507](../crates/notifications/src/lib.rs#L507) | Default maximum is five attempts; accepted configuration range is 1–100. Exhausted alerts stop retrying. A crash after reserving an attempt can consume one without delivering mail. | Remove the attempt quota in [#110](https://github.com/kamysh/mimir/issues/110). Keep durable delivery outcome handling explicit. |
| [notifications/lib.rs:344](../crates/notifications/src/lib.rs#L344), [judge/digest.rs:169](../crates/cli/src/judge/digest.rs#L169) | Digest delivery reserves an hourly retry before sending. A failed or interrupted send delays its next attempt by 3,600 seconds. | [#110](https://github.com/kamysh/mimir/issues/110). Daily calendar grouping remains the requested reporting behavior; this retry delay is a separate policy. |
| [notifications/lib.rs:362](../crates/notifications/src/lib.rs#L362), [notifications/lib.rs:385](../crates/notifications/src/lib.rs#L385) | `retry_due` accepts only 1–20 notifications and takes that many pending entries. This is a library restriction, even if a particular host does not call it. | Remove the ceiling and hidden work quota in [#110](https://github.com/kamysh/mimir/issues/110). |
| [judge/mcp.rs:170](../crates/cli/src/judge/mcp.rs#L170) | On MCP stream failure, sleeps 20 milliseconds before sampling captured stderr. That timer does not prove the stderr reader has finished. | [#108](https://github.com/kamysh/mimir/issues/108) must collect complete diagnostics through actual reader completion rather than an arbitrary delay. |

## Diagnostic and log loss

| Source | Existing restriction | Removal work |
|---|---|---|
| [judge/state.rs:10](../crates/cli/src/judge/state.rs#L10), [judge/state.rs:440](../crates/cli/src/judge/state.rs#L440), [judge/state.rs:633](../crates/cli/src/judge/state.rs#L633) | Diagnostic JSON is restricted to 3 MiB on read and write. Oversized metadata is refused. Ordinary batch/status state uses the separate uncapped path; the diagnostic cap is not a batch-input cap. | [#108](https://github.com/kamysh/mimir/issues/108). |
| [judge/state.rs:11](../crates/cli/src/judge/state.rs#L11), [judge/state.rs:453](../crates/cli/src/judge/state.rs#L453), [judge/state.rs:479](../crates/cli/src/judge/state.rs#L479) | Traces retain at most 48 events and 256 KiB. New events can be omitted, and finalization can pop events to fit. Selected IDs in a trace are also cut to 48. | [#108](https://github.com/kamysh/mimir/issues/108). |
| [judge/state.rs:13](../crates/cli/src/judge/state.rs#L13), [judge/state.rs:430](../crates/cli/src/judge/state.rs#L430) | At most eight diagnostic attempts are retained. Older unpinned attempts are deleted. A completed trace is removed separately; that success-retention policy is not the eight-attempt limit. | [#108](https://github.com/kamysh/mimir/issues/108). |
| [judge/state.rs:14](../crates/cli/src/judge/state.rs#L14), [judge/state.rs:107](../crates/cli/src/judge/state.rs#L107), [judge/state.rs:221](../crates/cli/src/judge/state.rs#L221) | Event detail is shortened to 3,072 characters; tool names to 64, kind to 48, and rejection detail to 512. Error report details are also shortened to 512 in `mod.rs` and `runner.rs`. | [#108](https://github.com/kamysh/mimir/issues/108). |
| [judge/state.rs:15](../crates/cli/src/judge/state.rs#L15), [judge/state.rs:41](../crates/cli/src/judge/state.rs#L41), [judge/state.rs:65](../crates/cli/src/judge/state.rs#L65) | Only a 32 KiB excerpt of malformed input is retained, either its prefix or a window near the JSON error. | [#108](https://github.com/kamysh/mimir/issues/108). Preserve complete private evidence without exposing it in public summaries. |
| [judge/mcp.rs:12](../crates/cli/src/judge/mcp.rs#L12), [judge/mcp.rs:112](../crates/cli/src/judge/mcp.rs#L112) | MCP stderr capture retains only the last 4,096 bytes; the reported error is further shortened to 512 characters. | [#108](https://github.com/kamysh/mimir/issues/108). |
| [judge/process.rs:8](../crates/cli/src/judge/process.rs#L8), [judge/process.rs:53](../crates/cli/src/judge/process.rs#L53), [judge/process.rs:113](../crates/cli/src/judge/process.rs#L113) | Model subprocess stderr is drained but only its first 64 KiB are retained; failure text is then shortened to 512 characters. This does not truncate model stdout in that reader. | [#108](https://github.com/kamysh/mimir/issues/108). |
| [judge/notification.rs:30](../crates/cli/src/judge/notification.rs#L30), [judge/notification.rs:41](../crates/cli/src/judge/notification.rs#L41), [judge/notification.rs:56](../crates/cli/src/judge/notification.rs#L56), [judge/notification.rs:109](../crates/cli/src/judge/notification.rs#L109), [judge/diagnose.rs:90](../crates/cli/src/judge/diagnose.rs#L90) | Public reason codes are shortened to 64 characters, project names to 80, and affected/recovered ID lists to five entries. `diagnose` also prints only five selected IDs. | Complete diagnostic output [#108](https://github.com/kamysh/mimir/issues/108) and delivery content [#110](https://github.com/kamysh/mimir/issues/110). |
| [core/operations.rs:23](../crates/core/src/operations.rs#L23), [core/operations.rs:65](../crates/core/src/operations.rs#L65), [core/operations.rs:202](../crates/core/src/operations.rs#L202), [core/operations.rs:257](../crates/core/src/operations.rs#L257), [core/operations.rs:286](../crates/core/src/operations.rs#L286) | Logger defaults to four files of 1 MiB, accepts only 1–16 files and 4 KiB–16 MiB per file, cuts writes at the file ceiling, cuts plain events to 8,192 characters, and cuts tracing event buffers to at most 32 KiB. Rotation discards older files. | [#109](https://github.com/kamysh/mimir/issues/109), with complete evidence in [#108](https://github.com/kamysh/mimir/issues/108). |

## Notification input and state ceilings

| Source | Existing restriction | Removal work |
|---|---|---|
| [notifications/lib.rs:196](../crates/notifications/src/lib.rs#L196), [notifications/lib.rs:207](../crates/notifications/src/lib.rs#L207), [notifications/lib.rs:215](../crates/notifications/src/lib.rs#L215), [notifications/lib.rs:223](../crates/notifications/src/lib.rs#L223) | Source/code: 64 bytes; incident key: 128; summary: 160; details: 2,048. Longer otherwise valid events are rejected. Nonempty/control-character validation is a separate question from length. | [#110](https://github.com/kamysh/mimir/issues/110). |
| [notifications/lib.rs:334](../crates/notifications/src/lib.rs#L334) | Digest body above 256 KiB is refused, even when it consists of valid accumulated reporting rows. | [#110](https://github.com/kamysh/mimir/issues/110). |
| [notifications/state.rs:13](../crates/notifications/src/state.rs#L13), [notifications/state.rs:119](../crates/notifications/src/state.rs#L119), [notifications/state.rs:148](../crates/notifications/src/state.rs#L148) | Notification state/outbox read and write is restricted to 1 MiB. More pending incidents can make persistence fail. | [#110](https://github.com/kamysh/mimir/issues/110), not deletion of pending work to fit. |
| [notifications/config.rs:163](../crates/notifications/src/config.rs#L163), [notifications/config.rs:169](../crates/notifications/src/config.rs#L169), [notifications/oauth.rs:12](../crates/notifications/src/oauth.rs#L12) | OAuth client ID: 1,024 bytes; configured secret/refresh token and returned token: 8,192 bytes. | [#110](https://github.com/kamysh/mimir/issues/110). Any claimed provider requirement needs independent evidence in [#112](https://github.com/kamysh/mimir/issues/112). |
| [notifications/oauth.rs:11](../crates/notifications/src/oauth.rs#L11), [notifications/oauth.rs:121](../crates/notifications/src/oauth.rs#L121), [notifications/oauth.rs:127](../crates/notifications/src/oauth.rs#L127) | OAuth refresh response is restricted to 16 KiB, checked against both content length and received bytes. A larger valid response is classified as needing attention. | [#110](https://github.com/kamysh/mimir/issues/110). |

## External constraints and distinct semantics

- [judge/api.rs:214](../crates/cli/src/judge/api.rs#L214) sends Anthropic
  `max_tokens` from the selected model's metadata, read at
  [judge/api.rs:237](../crates/cli/src/judge/api.rs#L237). This is not a fixed
  Mimir allowance, but it is still a constraint to present with evidence for the
  user's decision in [#112](https://github.com/kamysh/mimir/issues/112). OpenAI
  requests set truncation disabled; do not reintroduce a local output budget.
- [notifications/oauth.rs:88](../crates/notifications/src/oauth.rs#L88) refuses
  redirects during credential refresh. [#112](https://github.com/kamysh/mimir/issues/112)
  must resolve that policy explicitly: forwarding a refresh token/client secret
  to an unconfigured redirect destination is a concrete consequence to consider.
  This inventory grants no exception. The configured Microsoft tenant length
  ceiling of 253 bytes at
  [notifications/config.rs:194](../crates/notifications/src/config.rs#L194) also
  needs evidence rather than an assumed provider limit.
- [judge/harness.rs:268](../crates/cli/src/judge/harness.rs#L268) supplies
  `project_doc_max_bytes=0` to Codex to disable that harness's document cap.
  This is an external configuration convention, not permission to use zero for
  Mimir API selection. [#112](https://github.com/kamysh/mimir/issues/112) must
  account for dependency settings and their actual meaning.
- The private runner still supplies history selection 20 and requires positive
  query/explain selection (`runner.rs:124,176,198`). Coordinate it with public
  selection removal in [#103](https://github.com/kamysh/mimir/issues/103) and
  the judge correction dialogue in [#100](https://github.com/kamysh/mimir/issues/100).
- Retired LLM deadline/call/token/budget keys are rejected by configuration,
  not active execution quotas. Legacy reason strings mentioning those limits
  do not prove such a quota still executes. Conversely, removing those old
  fields did not remove the active waits and limits listed above.
- `Option::take` transfers ownership; it is not a work cap. Fixed read buffers
  used in loops do not limit total input unless their retention logic does so.
  Test-only timeouts/sleeps and fixtures belong to
  [#60](https://github.com/kamysh/mimir/issues/60), not the runtime table.
- Digest calendar-day boundaries, duplicate-notification suppression, and the
  persisted distinction between accepted and unaccepted delivery describe
  intended reporting behavior. They must not be confused with arbitrary retry
  delays or quotas. No live mail was sent and no live state was changed here.

## Verification boundary

Source searches covered timers, retry/count settings, bounds, truncation,
message construction, private state, subprocess capture, and notification
delivery. The relevant implementations were read. Verify linked locations,
stated constants and branches, issue references, and whitespace for this
documentation-only change. It does not claim the restrictions have been removed
or that a review/delivery was verified in a live deployment.

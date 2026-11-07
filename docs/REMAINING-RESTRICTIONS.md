# Restrictions outside application handlers

Inventory for [#60](https://github.com/kamysh/mimir/issues/60), inspected at
`origin/main` commit `a402f463441c677db82863fe4805e30fbfbe7c55`.
Source templates, test infrastructure, and formal rules are included. They are
not exempt from the user's requirement to remove arbitrary limits. This
inventory approves no retained limit and makes no installed or live change.

The companion inventories are [#57](https://github.com/kamysh/mimir/issues/57)
(core), [#58](https://github.com/kamysh/mimir/issues/58) (public interfaces), and
[#59](https://github.com/kamysh/mimir/issues/59) (judge, mail, and diagnostics).
Line numbers below refer to the inspected baseline.

## Examples and installation guidance

| Source | Existing rule and effect | Follow-up |
|---|---|---|
| [runtime/config.example.toml:6](../runtime/config.example.toml#L6) and [runtime/README.md:33](../runtime/README.md#L33) | Examples reproduce the logger's 1 MiB/four-file defaults and five-experience judge batch quota. Copying an example recreates those restrictions. | Remove along with their runtime fields in [#109](https://github.com/kamysh/mimir/issues/109), [#162](https://github.com/kamysh/mimir/issues/162), and compatibility [#117](https://github.com/kamysh/mimir/issues/117). |
| [runtime/config.example.toml:47](../runtime/config.example.toml#L47) | Mail example specifies a 15-second timeout, 300-second retry wait, and five attempts. | Mail removal [#110](https://github.com/kamysh/mimir/issues/110) and compatibility [#117](https://github.com/kamysh/mimir/issues/117). |
| [codex-hooks.json:9](claude-code-setup/codex-hooks.json#L9), [settings.json:9](claude-code-setup/settings.json#L9) | Both startup-reminder templates impose a five-second command timeout. No evidence in these files establishes why five seconds is correct. | Source-template removal in [#172](https://github.com/kamysh/mimir/issues/172); inherited client constraints require the user's decision under [#112](https://github.com/kamysh/mimir/issues/112). Do not edit installed client settings incidentally. |
| [AGENTS.md:167](../AGENTS.md#L167) | New-container setup waits three seconds before verifying PostgreSQL. Elapsed time is not proof of readiness. | Actual readiness in [#172](https://github.com/kamysh/mimir/issues/172). |
| [working-maintenance prompt](claude-code-setup/mimir-judge-working/prompt.md#L80) | Historical optional prompt protects working beliefs only until eight hours old, then permits promotion/deletion. Time alone does not establish that their owning session is finished. | [#173](https://github.com/kamysh/mimir/issues/173) requires a user-provided eligibility policy and leaves beliefs untouched when it is absent. Do not replace this default with immediate destructive cleanup or reuse the unrelated defeated-belief policy. |

## Test infrastructure and timing assumptions

These limits do not stop a production review, but they can make verification
fail for reasons unrelated to the behavior being checked. None is approved as
an exception merely because it is in a test.

| Source | Existing restriction | Follow-up |
|---|---|---|
| [test-isolated.py:104](../scripts/test-isolated.py#L104) | Disposable PostgreSQL gets `--memory 1g`, `--cpus 2`, and a 512 MiB tmpfs. Valid larger test data can exhaust the fixture's allowance. | Remove resource quotas in [#171](https://github.com/kamysh/mimir/issues/171), preserving disposable database identity, loopback port, ownership, and real-deployment connection guards. |
| [test-isolated.py:79](../scripts/test-isolated.py#L79) | Cancellation gives an owned test process five seconds after SIGTERM before SIGKILL. This is cleanup policy, not a review deadline. | [#116](https://github.com/kamysh/mimir/issues/116) must remove arbitrary timing and give cleanup an explicit completion contract. Do not silently retain a five-second exception. |
| [test-isolated.py:112](../scripts/test-isolated.py#L112) | PostgreSQL readiness polls at most 60 times with 0.5-second sleeps. A slower start is rejected despite remaining able to finish. | Event/observable-state synchronization in [#116](https://github.com/kamysh/mimir/issues/116). |
| [test-isolated.py:180](../scripts/test-isolated.py#L180), [test-isolated.py:197](../scripts/test-isolated.py#L197) | Connection-guard fixture polls a socket with a 0.1-second timeout and gives its thread two seconds to join. | [#116](https://github.com/kamysh/mimir/issues/116), preserving the assertion that conflicting settings are refused before any network connection. |
| [MCP startup test:32](../crates/mcp/tests/startup.rs#L32) | Kills a startup child after five seconds and polls it every 10 milliseconds. | [#116](https://github.com/kamysh/mimir/issues/116). |
| [conformance test:191](../crates/core/tests/conformance_integration.rs#L191) | Gives lock contention five seconds to appear, with 10-millisecond polling. It observes contention, but still has an arbitrary deadline. | [#116](https://github.com/kamysh/mimir/issues/116). |
| [cancellation test:47](../crates/cli/tests/judge_cancellation.rs#L47) | Uses a ten-second deadline and repeated 10-millisecond waits to observe descendant lifecycle. | [#116](https://github.com/kamysh/mimir/issues/116). |
| [MCP startup fixture:243](../crates/cli/src/judge/mcp_startup_tests.rs#L243), [MCP unit test:523](../crates/cli/src/judge/mcp.rs#L523), [API fixture:590](../crates/cli/src/judge/api.rs#L590) | Fixtures assume 25/50-millisecond scheduling delays, one-second cancellation timing, and a 30-second HTTP accept deadline. A synthetic child also waits using `sleep 30`. | Replace clock assumptions with explicit signals/process state in [#116](https://github.com/kamysh/mimir/issues/116). |
| [notification test:146](../crates/notifications/src/tests.rs#L146), [notification test:309](../crates/notifications/src/tests.rs#L309) | SMTP fixture refuses a line at 65,536 bytes; mail test configurations repeat short timeouts and attempt/retry quotas. These are fixture rules, not evidence for production exceptions. | Fixture synchronization [#116](https://github.com/kamysh/mimir/issues/116) and mail contract removal [#110](https://github.com/kamysh/mimir/issues/110). |

Changing these sources does not authorize a live database, provider account,
installed hook, system service, or external harness change. The isolated-test
guard must remain effective; tests must never fall back to the real deployment.

## Database constraints and evaluation tools

The supplemental search includes all of `tests/` and the migration SQL, not
only Rust test files. These restrictions also require removal work.

| Source | Existing restriction and effect | Follow-up |
|---|---|---|
| [007_review_candidates.sql:8](../crates/core/migrations/007_review_candidates.sql#L8), and `MigrationSchema.reviewCandidates` | PostgreSQL still rejects a candidate key longer than 128 characters through a table check, independently of the current Rust input validator. | [#106](https://github.com/kamysh/mimir/issues/106) must remove the ceiling through a new migration and update its formal contract. Do not rewrite a historical applied migration. |
| [fixture.py:62](../tests/support/fixture.py#L62), [fixture.py:70](../tests/support/fixture.py#L70), [database-connections.py:33](../tests/database-connections.py#L33), [database-connections.py:88](../tests/database-connections.py#L88) | Shared cancellation helper waits at most 60 seconds for readiness, polls every 0.05 seconds, and waits ten seconds for exit/cleanup. Database-connection checks impose a 60-second subprocess timeout and at most 60 startup checks with 0.5-second sleeps. | Deterministic lifecycle synchronization in [#116](https://github.com/kamysh/mimir/issues/116). |
| [database-connections.py:82](../tests/database-connections.py#L82) | A second disposable database fixture limits memory to 512 MiB and its data filesystem to 256 MiB. It needs the same audit as the main runner's fixture. | Remove these quotas alongside the first fixture in [#171](https://github.com/kamysh/mimir/issues/171). |
| [judge-adapters.sh:150](../tests/judge-adapters.sh#L150), [judge-adapters.sh:187](../tests/judge-adapters.sh#L187), [judge_process_fixture.rs:24](../tests/judge_process_fixture.rs#L24), [test_isolated_runner.py:84](../tests/test_isolated_runner.py#L84) | Adapter fixtures poll at most 30 times with 0.05-second sleeps and use a 60-second watch interval; process fixtures use 30-second sleeping children, and the isolation-runner fixture assumes 0.3/0.1-second ordering. | [#116](https://github.com/kamysh/mimir/issues/116), with obsolete watcher options removed by [#64](https://github.com/kamysh/mimir/issues/64) and [#67](https://github.com/kamysh/mimir/issues/67). |
| [eval/main.rs:676](../tests/eval/main.rs#L676), [eval/main.rs:1439](../tests/eval/main.rs#L1439), [eval/main.rs:1711](../tests/eval/main.rs#L1711), [eval/main.rs:1854](../tests/eval/main.rs#L1854), [eval/config.json:11](../tests/eval/config.json#L11) | Evaluator defaults execution to 600 seconds and 40 turns, kills timed-out scripts/actors, and polls at 30/40 milliseconds. Valid slow work can become an evaluation failure. | Remove evaluation execution budgets in [#175](https://github.com/kamysh/mimir/issues/175). |
| [learning_compare.rs:255](../tests/eval/learning_compare.rs#L255) | Later-action actor is killed after 300 seconds, with 100-millisecond polling. | [#175](https://github.com/kamysh/mimir/issues/175). |
| [eval/main.rs:1013](../tests/eval/main.rs#L1013), [eval/main.rs:1399](../tests/eval/main.rs#L1399), [eval/main.rs:1473](../tests/eval/main.rs#L1473), [eval/main.rs:1500](../tests/eval/main.rs#L1500), [eval/main.rs:1511](../tests/eval/main.rs#L1511), [eval/main.rs:1520](../tests/eval/main.rs#L1520), [eval/main.rs:1636](../tests/eval/main.rs#L1636) | Reporting cuts lines to 200/400 characters; grading sees only 60 calls, 160 characters per input, and 500 characters of final result. Some evidence comparisons use only a 60-character prefix. | Restore complete evaluation evidence and matching in [#176](https://github.com/kamysh/mimir/issues/176). |
| [eval/main.rs:49](../tests/eval/main.rs#L49), [eval/main.rs:1047](../tests/eval/main.rs#L1047), [eval/main.rs:1645](../tests/eval/main.rs#L1645) | Grading sample defaults to zero meaning all. Evaluation callers still send `list --limit 0` and request fixed retrieval/evidence selections of 25/two. These callers must move with the public request contract instead of preserving the old zero convention or hiding an evaluator default. | Explicit evaluator selection [#177](https://github.com/kamysh/mimir/issues/177), coordinated with [#103](https://github.com/kamysh/mimir/issues/103), [#104](https://github.com/kamysh/mimir/issues/104), and [#105](https://github.com/kamysh/mimir/issues/105). |

An explicitly chosen experiment sample or fixed set of scenarios defines the
experiment being requested; it does not justify shortening a selected run's
evidence or terminating its agent. Likewise, fixture requests intentionally
selecting one known row to assert a particular result are not evidence of a
production quota. No live evaluation model was called during this inventory.

## Agda rules that currently encode the restrictions

The removal issues must change these existing contracts before changing the
behavior they govern. A theorem about preserving a cap does not justify keeping
the cap. No new proof of text formatting, tokenization, or dependency algorithms
is needed to remove an application policy.

| Source | Rule currently encoded | Follow-up |
|---|---|---|
| [CLI.agda:80](../spec/Mimir/CLI.agda#L80), [JudgeHost.agda:100](../spec/Mimir/JudgeHost.agda#L100), [JudgeDigestComposition.agda](../spec/Mimir/JudgeDigestComposition.agda) | Default watch interval 300, failure threshold three, and backoff at least 3,600 seconds; host enters a wait after digest handling. | [#63](https://github.com/kamysh/mimir/issues/63), [#64](https://github.com/kamysh/mimir/issues/64), [#66](https://github.com/kamysh/mimir/issues/66), [#67](https://github.com/kamysh/mimir/issues/67), and independent mail [#68](https://github.com/kamysh/mimir/issues/68). |
| [JudgeSelection.agda:45](../spec/Mimir/JudgeSelection.agda#L45), [PendingSelection.agda](../spec/Mimir/PendingSelection.agda) | Judge selection/admission is parameterized by a batch limit and rejects a batch beyond it. | [#162](https://github.com/kamysh/mimir/issues/162). |
| [PublicRequest.agda:145](../spec/Mimir/PublicRequest.agda#L145), [CLI.agda:80](../spec/Mimir/CLI.agda#L80), [GraphRecords.agda:55](../spec/Mimir/GraphRecords.agda#L55) | Reproduces default selections 5/10/20, zero-as-all, and belief page maximum 10. | [#103](https://github.com/kamysh/mimir/issues/103), [#105](https://github.com/kamysh/mimir/issues/105), and schema agreement [#102](https://github.com/kamysh/mimir/issues/102). |
| [RetrievalRanking.agda:133](../spec/Mimir/RetrievalRanking.agda#L133) | `cap 0` returns all; vector candidate pool is 50 for zero or `max(limit * 4, 20)` otherwise. | [#104](https://github.com/kamysh/mimir/issues/104). |
| [CLI.agda:113](../spec/Mimir/CLI.agda#L113), [HookProtocol.agda:117](../spec/Mimir/HookProtocol.agda#L117) | CLI shortening and hook input widths 500/200 with five/three selected beliefs are part of the formal behavior too. | [#167](https://github.com/kamysh/mimir/issues/167) and [#168](https://github.com/kamysh/mimir/issues/168). |
| [EmbeddingBackend.agda:63](../spec/Mimir/EmbeddingBackend.agda#L63), [EmbeddingBackend.agda:133](../spec/Mimir/EmbeddingBackend.agda#L133) | Local model input is cut to 512 tokens; downloads use 600 seconds and ten redirects. | [#113](https://github.com/kamysh/mimir/issues/113), [#107](https://github.com/kamysh/mimir/issues/107), and any evidenced external constraint under [#112](https://github.com/kamysh/mimir/issues/112). |
| [PosteriorComputation.agda:288](../spec/Mimir/PosteriorComputation.agda#L288), [PosteriorComputation.agda:299](../spec/Mimir/PosteriorComputation.agda#L299), [InferenceProtocol.agda:125](../spec/Mimir/InferenceProtocol.agda#L125) | Calculation runs `iterate 50` and exposes `iterationLimitReached` in a completed result. The model encodes the unfinished-result behavior rather than ruling it out. | Completion meaning [#114](https://github.com/kamysh/mimir/issues/114), then cutoff removal [#115](https://github.com/kamysh/mimir/issues/115). |
| [OperationalConfiguration.agda:44](../spec/Mimir/OperationalConfiguration.agda#L44), [OperationalLogRetention.agda:23](../spec/Mimir/OperationalLogRetention.agda#L23), [OperationalLogSteps.agda](../spec/Mimir/OperationalLogSteps.agda) | Logger configuration bounds, byte clipping, and finite retained-file rotation are proved as current behavior. | [#109](https://github.com/kamysh/mimir/issues/109) and configuration migration [#117](https://github.com/kamysh/mimir/issues/117). |
| [JudgePersistence.agda:36](../spec/Mimir/JudgePersistence.agda#L36), [JudgeTraceStart.agda:79](../spec/Mimir/JudgeTraceStart.agda#L79), [JudgeStateOperations.agda:61](../spec/Mimir/JudgeStateOperations.agda#L61), [JudgeTraceRetention.agda](../spec/Mimir/JudgeTraceRetention.agda), [JudgeTraceTrim.agda](../spec/Mimir/JudgeTraceTrim.agda) | Diagnostic 3 MiB admission; 48 selected IDs/events; 256 KiB traces; retention and trimming that drop history to fit. | [#108](https://github.com/kamysh/mimir/issues/108). |
| [JudgeProcess.agda:25](../spec/Mimir/JudgeProcess.agda#L25), [SourceWindow.agda](../spec/Mimir/SourceWindow.agda), [McpClientLineDiagnostic.agda:49](../spec/Mimir/McpClientLineDiagnostic.agda#L49), [JudgeStateRecords.agda:32](../spec/Mimir/JudgeStateRecords.agda#L32) | Encodes subprocess stderr retention, source windows, 512-character diagnostic text, 64-character tool names, and 3,072-character event details. | [#108](https://github.com/kamysh/mimir/issues/108). |
| [NotificationConfig.agda:56](../spec/Mimir/NotificationConfig.agda#L56), [NotificationConfig.agda:191](../spec/Mimir/NotificationConfig.agda#L191), [NotificationDelivery.agda:81](../spec/Mimir/NotificationDelivery.agda#L81), [NotificationRuntime.agda:197](../spec/Mimir/NotificationRuntime.agda#L197) | Default 15/300/five mail limits, accepted numeric ranges, retry exhaustion, and at most 20 retry entries. | [#110](https://github.com/kamysh/mimir/issues/110). |
| [DigestDelivery.agda:54](../spec/Mimir/DigestDelivery.agda#L54), [DigestDelivery.agda:81](../spec/Mimir/DigestDelivery.agda#L81), [NotificationSchema.agda:37](../spec/Mimir/NotificationSchema.agda#L37), [NotificationStorage.agda:92](../spec/Mimir/NotificationStorage.agda#L92), [JudgeNotification.agda:79](../spec/Mimir/JudgeNotification.agda#L79) | Digest 256 KiB body, hourly retry, event field lengths, 1 MiB notification state, and five-ID summaries. | [#110](https://github.com/kamysh/mimir/issues/110), with full diagnostic output [#108](https://github.com/kamysh/mimir/issues/108). |
| [OAuthComposition.agda:77](../spec/Mimir/OAuthComposition.agda#L77), [OAuthCache.agda:28](../spec/Mimir/OAuthCache.agda#L28), [OAuthCache.agda:123](../spec/Mimir/OAuthCache.agda#L123), [SMTPProtocol.agda:78](../spec/Mimir/SMTPProtocol.agda#L78) | OAuth response/token bounds, configured network deadline, and a fixed 60-second early-refresh margin. The latter also appears as `EXPIRY_MARGIN` in `crates/notifications/src/oauth.rs:13,169`; it shortens cache reuse rather than limiting total attempts. | Mail restriction removal [#110](https://github.com/kamysh/mimir/issues/110); any proposed provider-required margin or redirect policy requires evidence and approval in [#112](https://github.com/kamysh/mimir/issues/112). |

## Bounds that need interpretation rather than search-and-delete

- A structural recursion argument tied to the input's length ensures the
  function processes the finite input; it is not a quota. For example,
  `EmbeddingBackend.batchesFuel` partitions all supplied texts. This differs
  from the independent constant 50 in inference. Likewise, counting the four
  required handshake exchanges does not impose an extra cap on later requests.
- Integer/byte/Float representations and timestamp saturation describe
  dependency representations, not proof that a smaller application allowance
  is necessary. [#112](https://github.com/kamysh/mimir/issues/112) must account
  for genuine external constraints. A name containing `bounded` is not evidence
  of an arbitrary limit by itself. `0600` and `0700` are permission modes.
- External I/O can report an interruption or provider rejection without Mimir
  imposing a deadline. Removing application timers must not erase those
  observable events or invent successful completion.
- Fixture sample counts, simulated ages, and tolerance assertions are not
  runtime work budgets. Tests explicitly asserting that data is shortened or
  work is refused at an old cap must change with its removal; tests of valid
  numeric domains and isolation remain meaningful.
- Source migrations and workflow/scripts were searched for statement timeouts,
  hard result ceilings, and process deadlines. No explicit migration statement
  timeout or GitHub workflow `timeout-minutes` setting was found. That does not
  establish the absence of server, platform, or runner limits. This audit did
  not inspect or alter the installed deployment or external service settings.

## Verification boundary

Searches covered scripts, runtime samples, setup templates, migrations, CI
workflows, Rust test timing, and `spec/Mimir`. Matches were checked against their
definitions; ordinary finite-list/domain bounds were distinguished from rules
that stop or shorten work. Focused verification checks source links, concrete
constants/branches, follow-up issue references, and whitespace. It does not run
the full Rust/Agda suites for a documentation-only inventory or claim any of
these restrictions is already removed.

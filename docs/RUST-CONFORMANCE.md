# Rust implementation alignment

The user authorized completion without further stage approval on 2026-10-31.
Version 2.1.0, installed binaries, production data and system configuration
remain unchanged. Existing checked contracts govern each implementation change.

## Governing contracts and implementation derivation

- `EmbeddingBatch.Aligned`, `everyInputPositionExactlyOnce`,
  `noSilentTruncation` and `EmbeddingBackend.Remote.remoteResult`: remote rows
  must cover exactly the requested indices and share a dimension. Decode into
  indexed slots, reject duplicates/out-of-range/missing rows and inconsistent
  shapes, then return input order. Preserve existing scalar conversion.
- `GraphPaths.Returned`: complete, distinct mixed SUPPORTS/CAUSES/DEFEATS or
  causal-only reachability, without a depth cap. Traverse direct edges with a
  visited frontier; include a seed only if a nonempty cycle reaches it. The
  inference engine independently excludes the clamped seed from its writes.
- `DocumentLoading`, `DocumentPublication` and `DocumentStore`: prepare all
  chunks/vectors before mutation; validate count, shape and retained identity
  collisions; hold the shared lock and one transaction through old-row reads,
  chunk/vector deletion, insertion and commit. Automatic grounding follows
  successful replacement. A lost commit acknowledgement remains an error,
  never evidence that rollback occurred.
- `LearningTransaction`, `CandidateRegistry.reserve` and writer findings:
  candidate creation must check occupied graph/registry IDs under the shared
  transaction lock. Independent graph writers must participate in that lock.
  Propagation and decay must acquire it before their reads and retain the same
  transaction through publication. `GraphMutationProtocol.write/afterEdge`
  requires separate publication of a DEFEATS edge before propagation: a later
  propagation failure must preserve the committed edge. Both phases participate
  in the lock, but do not share an atomic commit. Existing numerical policy is
  preserved. This specific checked composition supersedes the historical
  source-audit suggestion to combine edge insertion and propagation.

Verification uses unit tests, existing local protocol fixtures, and a newly
created disposable PostgreSQL containers using the existing local AGE/pgvector
image. No production connection is used. Source hashes, focused diffs,
full command logs and exit statuses are retained. These checks supplement
source-to-contract arguments; they are not a compiled Rust refinement proof.

## Explicit isolation selection

The approved READ COMMITTED assumption excludes choosing the isolation level
from its scope: that is an application obligation. A lock-acquisition SELECT
can establish a stale snapshot under a caller-configured REPEATABLE READ
default before the lock wait finishes. Therefore store transactions explicitly
select READ COMMITTED before beginning, using one private constructor. This
ensures each successful ordinary read after acquiring the shared lock observes
the then-committed state under the approved contract. No server configuration
or additional postulate is required. Verification includes an intentionally
different default on the disposable test account.

## Completed implementation

| Area | Final behavior | Implementation |
| --- | --- | --- |
| Judge startup | Real capability admission precedes readiness; required catalog/schema fields checked; shared request IDs/deadline and owned-child cleanup retained | `crates/cli/src/judge/mcp.rs`; `JUDGE-STARTUP-CONFORMANCE.md` |
| Judge and notification state | Only successful exclusive creation grants temporary cleanup; successful rename ends it; post-publication directory errors do not claim rollback | Both `state.rs` writers; their persistence receipts |
| Embeddings | Exact count and input-index association, no duplicate/out-of-range indices or mixed dimensions | `crates/core/src/embed.rs` |
| Graph traversal | Complete distinct mixed-relation and causal-only closures without a depth-ten cap; inference independently clamps the seed | `store/conformance.rs::downstream_on` |
| Documents | Preparation before mutation; identity/shape/count admission; paired chunks/vectors/obsolete associations publish atomically; grounding follows publication | `lib.rs`, `store.rs`, `store/conformance.rs` |
| Learning concurrency | Candidate collision admission under the shared lock; independent writers participate; propagation/decay reads and publication use one locked READ COMMITTED transaction | `store.rs`, `store/learning.rs`, `store/conformance.rs` |
| Failure-prefix compatibility | A DEFEATS edge remains committed when later propagation fails; bulk project deletion retains separate publication steps; empty vector deletion remains a no-op | `GraphMutationProtocol` and `GraphWrites` mapping |

## Verification results

**254 distinct selected tests have a passing final result**:

- 100 core unit tests and one explicit disposable-database candidate/isolation test.
- Four new database regressions, 48 existing store tests and 19 learning tests.
- 21 notification tests, including the six new persistence cases.
- 56 judge tests; the live-model-capable `isolated_mcp_review_cycle` stayed excluded.
- Three real MCP dispatcher tests, including the learning cycle, and two real
  process-startup tests using disposable configuration.

The 72 database checks were repeated after explicit isolation selection with
the fixture role defaulting to REPEATABLE READ; all passed. The constructor
assertion checks READ COMMITTED inside Mimir's transaction, and the contention
regression observes a waiting advisory lock before committing a changed seed.
The final MCP dispatcher also passed against that configuration. Every workspace
test target compiled from the final source. Formatting, source-scope hashes,
whitespace and public-operation/Agda coverage checks passed.

Both disposable PostgreSQL containers and their temporary credentials were
removed, with exact container-identity and absence checks. No installed binary,
production application data, migration, version, dependency, application config,
system service or host configuration was changed. Mimir remains standalone;
none of these changes requires the harness.

## Corrections and verification limits

Three failed test invocations are retained in the receipt. The first pager
failure came from three global beliefs created by new fixtures; the second
came from the failed pager's own abandoned global marker. New fixtures now use
unique projects and cleanup; residue was removed only from the disposable
database, and zero remaining global beliefs was observed before retry.
The edge-failure fixture initially changed optional `alpha0`, which correctly
uses the legacy fallback. It now changes mandatory `probability` to induce the
specified decoding error. No application behavior was changed to satisfy these
fixture assertions.

Source review also corrected an initial combined edge/propagation transaction
to preserve the checked failure-prefix contract. The older audit suggestion to
combine those commits was not authoritative. Final review preserved the
existing empty-vector-deletion no-op before acquiring a connection/transaction.

The first disposable database setup observed the image's temporary initialization
server. Setup was completed only after the final Nix-wrapped PostgreSQL process
became PID 1. The second setup waited for that condition from the outset.

All 638 Agda sources match the checked aggregate receipt exactly; no new
postulate or weakened law was introduced. Historical `GraphPaths.native` and
comments describing old native defects remain baseline observations; the
required contracts, not those historical SQL choices, govern this implementation.
This work supplies source-to-contract reasoning and executable verification,
not a machine-checked compiled-Rust refinement theorem. Filesystem write/fsync
and directory-fsync error branches were reviewed, not fault-injected. No live
model, external mailbox, static-release build, installation or load trial ran.
Shared-lock serialization can affect throughput; this verification establishes
the tested ordering and failure behavior, not production latency.

Machine-readable commands, exit statuses, hashes, corrected failures and cleanup
receipts: [RUST-CONFORMANCE-VERIFICATION.json](RUST-CONFORMANCE-VERIFICATION.json).

Focused implementation diff: `/tmp/mimir-final-implementation-fopvorcx.patch`.

# Sources and checks for the publication drafts

Prepared on 2026-10-20. This report separates text checked against source from
software builds, live installations and publications that have not been done.

Later publication results, including checked public files, successful Glama
checks and both submitted software-list requests, are recorded in
[publication results](publication-results.md).

## Source versions

| Project | Inspected commit | Existing changes preserved |
| --- | --- | --- |
| Kryzhen | `d8a0c6cbbb5a6ed040945a82373d9c433c88df34` | Modified `flake.lock` and untracked `z`; neither was changed or used as a claim source |
| Muninn | `12efb25acd6bc8f3218f453f763afe3841c7b18c` | Clean before preparation; no edits made |
| Mimir | `d5cf1704f90f82db867ba7837e8a0a90a6a72bbc` | Clean before preparation; only this package was added |

## Technical claims

### Kryzhen

| Claim used in public copy | Source |
| --- | --- |
| Rust library and CLI, version 2.0.3 | Root and member `Cargo.toml` files; [source README](https://github.com/kamysh/kryzhen/blob/d8a0c6cbbb5a6ed040945a82373d9c433c88df34/README.md) |
| Mallard migration syntax and tracking table | README and `kryzhen/src/postgres.rs` |
| Named dependencies, missing-dependency and cycle rejection, deterministic ready-node ordering | `kryzhen/src/graph.rs`, `topo_sort` |
| Duplicate names are rejected before migration | `kryzhen/src/lib.rs`, `migrate`; `validation.rs` |
| Later blocks in the same file depend on their predecessor | `kryzhen/src/file.rs`, `apply_implicit_deps` |
| Target schemas have independent applied sets; omitted schema uses `current_schema()` | `kryzhen/src/lib.rs`, `migrate` |
| Each migration and its tracking entries commit together | `kryzhen/src/postgres.rs`, `apply_one` |
| Dry runs do not bootstrap tracking tables or apply SQL | `kryzhen/src/lib.rs`, `migrate`; existing `kryzhen/tests/applier.rs` dry-run cases |
| Checksum covers the trimmed SQL body | `kryzhen/src/types.rs`, `checksum`; parser body extraction |
| Linux x86_64, Linux ARM64 and Apple Silicon release targets | `.github/workflows/release.yml`; source README |

The article's SQL and commands are illustrative examples checked against the
parser and CLI definitions. They were not executed against a database. No
recording, live demo, benchmark or successful installation is claimed.

### Muninn

| Claim used in public copy | Source |
| --- | --- |
| Semantic, full-text, hybrid and structural search | `crates/mcp/src/tools.rs`; [source README](https://github.com/kamysh/muninn/blob/12efb25acd6bc8f3218f453f763afe3841c7b18c/README.md) |
| Search takes `repo` or `cwd` and returns source ranges | `crates/mcp/src/tools.rs`, `SearchParams`, `SearchResultItem`, search resolution |
| Worktrees share file content and embeddings but select separate views | `crates/core/src/worktrees/mod.rs`; `docs/development.md`, Worktree indexing and search |
| Primary checkout updates preserve other published views | `docs/development.md`; current worktree storage implementation |
| Merge/rebase/conflicts retain the last completed index | Current development guide; search resolution and reconciliation implementation |
| Initial indexing requires an explicit start | README and `docs/development.md`, Configuration and daemon coordination |
| Structural matches are name-based candidates | README and current development guide |
| Curated notes use exact repository-path keys | `docs/development.md`, Storage ownership; `crates/mcp/src/tools.rs`, knowledge tools |
| Database extensions, watcher and MCP connection are needed | `docs/get-started.md`; README |
| Hosted embeddings send source chunks and queries to the provider | README, Data and privacy |

Some search results referenced older proposals that described family-wide notes.
That proposal wording was not used: the current implementation guide documents
exact-path note storage. No claims of compiler-verified relationships or measured
performance improvements are made.

### Mimir

| Claim used in public copy | Source |
| --- | --- |
| Typed belief relationships and persistent reasoning | [source README](https://github.com/kamysh/mimir/blob/d5cf1704f90f82db867ba7837e8a0a90a6a72bbc/README.md); MCP tool definitions |
| Direct belief insertion requires independent provenance | `crates/mcp/src/main.rs`, tool schema and `insert_belief` dispatch |
| Incident creation/correction preserves versions and rejects stale revisions | `crates/core/src/store/learning.rs`, `record_experience`, `experience_history` |
| Corrections invalidate prior active review contributions | `record_experience`, `replace_review_edges`, `recompute_learning` |
| Accepted review retries do not add evidence again | `review_experience` accepted-request comparison |
| Candidate identity belongs to the incident | `reserve_candidates`, `materialize_review`; current README |
| Provenance and active reviews can be inspected | `independent_provenance`, `candidate_provenance`, `reviews_for_belief`; MCP interfaces |
| Optional judge runs only when launched | `runtime/README.md`; source README |
| Stored causal hypotheses do not establish causal truth | README and runner guidance |

The article's cache example and query are illustrative. No fake conversation,
successful behavioral trial or promise that a model will obey memory is included.

## Submission rules checked

| Destination | Finding | Effect on the package |
| --- | --- | --- |
| Awesome MCP Servers | Public installable repositories are eligible for consideration; specified entry format and categories exist | Two exact entries and PR bodies prepared; acceptance remains the list maintainers' decision |
| Official MCP Registry | Supports discovery metadata plus supported installation packages | Two metadata drafts; final install information awaits a real package |
| crates.io | Package metadata and publishable dependencies are needed; upload checks are separate from public documentation builds | Kryzhen preparation steps and proposed fields are written; no upload or dry run claimed |
| This Week in Rust | Rejects LLM-written articles and project/tooling-update PR submissions | Excluded |
| Awesome Postgres | Requires adoption/recognition and production-use maturity | Conditional only |
| Awesome Rust | Requires popularity evidence | Excluded from immediate submission |
| DEV | AI-written content has disclosure and purpose restrictions | Complete article drafts retained; site suitability and account access remain to be checked |

The rules and their first-party links are recorded in
[directory submissions](directory-submissions.md) and
[the publication queue](publication-queue.md).

## Checks completed on the files

The file checks passed: 20 internal links and 9 links into the Git source trees
were checked. Both JSON description files parse, use the inspected software
versions, and stay within the registry description limit. Code blocks are
closed, GitHub descriptions and topic names fit their limits, and all three
articles identify the AI writer. The final receipt is
`/tmp/visibility-final-checks.t5H9jJ.log`.

These checks establish that the prepared text and files are internally
consistent. They are not software-build, installation or publication checks.

## Later checks completed and checks remaining

- The later software-list stage checked for duplicate entries and requests,
  verified GitHub access, and read back both submitted requests. Exact titles,
  bodies, entry lines, labels and lack of assignees or requested reviewers passed.
- Both official publication checks passed for the exact software-list commits.
  The clean contribution worktrees were removed; their branches were retained.
- Glama's local and remote tests passed with the pinned Muninn and Mimir release
  downloads. Their pages and inclusion in public search were verified. This does
  not verify every release target or Kryzhen's release downloads.
- Profile-repository contents, crates.io ownership and article-site account
  access remain unchecked for those separate future steps.
- Confirm registry name and crate-name availability. The public API URLs could
  not be retrieved, so absence or availability is not inferred.
- Run package preparation, build and installation checks in a separately
  approved technical stage. No source package or MCPB bundle was built here.
- Read back all later public changes and retain their addresses. The preparation
  stage excluded publishing; receipts from the subsequent publication stage are
  linked in [publication results](publication-results.md).

## Local inspection receipts

Complete command output was retained in temporary logs, including:

- `/tmp/visibility-source-inventory.43i1zH.log`
- `/tmp/visibility-current-sources.6O9eMd.log`
- `/tmp/visibility-symbols.kYoUgH.log`

These logs are local review aids and are not part of the public article material.

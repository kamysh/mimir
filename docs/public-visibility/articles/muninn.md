# Muninn code search across Git worktrees

A repository can have several correct versions of the same function at once.
The primary checkout contains the current implementation, a feature worktree
contains a rewrite, and another worktree contains a release fix. An AI coding
agent asking where a behavior lives needs the version in its selected checkout.

[Muninn](https://github.com/kamysh/muninn) provides persistent code search over
MCP, the Model Context Protocol. It combines semantic and full-text retrieval,
offers structural queries, and stores repository notes. Its Git worktree support
keeps separate searchable views while sharing unchanged content and embeddings.

## Selecting the source being searched

Consider two worktrees of an application. In the primary checkout, invoice
validation happens in one function. In a feature worktree, that function has
been split across several files. A question about validation should find the
source belonging to the checkout where the agent is working.

Muninn's `search_hybrid` tool accepts an explicit repository or worktree path:

```json
{
  "query": "where invoice validation rejects an unsupported currency",
  "repo": "/work/application-feature",
  "limit": 5
}
```

The same question with `repo` set to `/work/application-main` selects the primary
checkout. A caller can instead supply `cwd` inside a checkout. When both are
present, `repo` takes precedence. These paths illustrate tool arguments; they
are not required directory names.

Results include file paths, line ranges, source excerpts and ranking scores.
The agent can open those ranges and establish what the code actually does.
Search scores rank candidates; they are not estimates that an answer is correct.

## Sharing content while preserving separate views

Creating a worktree usually leaves most files unchanged. Indexing every copy
independently would repeat storage and embedding work for identical content.
Searching only a shared primary index would lose changes made in other
checkouts.

Muninn groups linked worktrees into a repository family. File versions hold the
indexed content, chunks and embeddings. The primary checkout supplies a base
mapping, and each other checkout records the paths that differ from that base.
Search combines the selected checkout's visible content before returning
results.

When the primary checkout advances, another worktree may still need an older
file version. Muninn preserves that reference while updating the internal base
and differences. The branch continues to have its own published view. Matching
content can reuse existing embeddings.

An enabled family discovers linked worktrees automatically. A first search can
also register and index a new linked checkout in that family. Initial family
indexing still requires an explicit start; merely saving configuration does not
start it.

The
[implementation guide](https://github.com/kamysh/muninn/blob/12efb25acd6bc8f3218f453f763afe3841c7b18c/docs/development.md#worktree-indexing-and-search)
describes the storage and reconciliation behavior.

## Choosing a retrieval method

Hybrid search combines semantic and full-text results. It is useful for questions
that describe behavior using words that may differ from the identifiers in the
code. Full-text search offers a direct route for known terms. Semantic search
can be requested on its own.

Structural search follows recorded relationships such as callers and callees.
Those relationships are name-based candidates. They do not provide the binding
guarantees of a compiler or language server, so a result remains a starting point
for inspecting source.

Repository knowledge is a separate facility. An agent can record a durable note
about an interface or an implementation decision, then retrieve it later.
Currently those notes use an exact repository-path key; code worktree resolution
does not automatically turn notes into family-wide storage. Shared notes should
use the established repository key.

## Keeping incomplete changes out of published indexes

A merge or rebase can temporarily leave files in a state that should not become
the checkout's searchable implementation. Muninn retains the last completed
index while those Git operations or unresolved conflicts suspend publication.
A new checkout without a completed index cannot supply that completed view yet.

File watching and reconciliation update ordinary edits. The database can publish
its index changes transactionally, but external processes can still edit files
concurrently. Agents should read current source before relying on a retrieved
excerpt for a change.

## Running Muninn

Muninn consists of a CLI, a background indexing watcher, and a stdio MCP server
launched by the agent client. The database prerequisites are PostgreSQL,
pgvector, Apache AGE and pgcrypto. The recommended postgres-ai distribution
supplies those extensions together.

Embeddings can run locally after the model download. A hosted embedding backend
sends selected source chunks and query text to its provider. The MCP client also
receives source excerpts, so its own model and data settings still matter.

The [setup guide](https://github.com/kamysh/muninn/blob/main/docs/get-started.md)
covers installation. Agent setup documentation covers clients including Codex
and Claude Code. The project is written in Rust and licensed under Apache 2.0.

Related projects are [Mimir](https://github.com/kamysh/mimir), which preserves
decisions and reasoning across agent sessions, and
[Kryzhen](https://github.com/kamysh/kryzhen), the PostgreSQL migration library used
by Muninn.

This article was drafted by an AI assistant from the project's source code and
documentation. The invoice scenario is illustrative.

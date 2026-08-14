# Document-chunk summarization

## Status

Spec drafted and type-checks (`spec/Mimir/Documents.agda`, `agda --safe Mimir.agda`
exits 0). **No Rust written.** Per this project's absolute rule — no implementation
code without a governing, user-approved Agda spec first — this plan is waiting on
that approval before the Rust/MCP-tool work below begins.

Unlike this proposal set's other recent work, there is no empirical pain signal
forcing the question either way: nobody has hit "coarse document queries fail" as an
actual problem. This is a design proposal to accept or decline, not a fix for a
measured gap.

## Why

`DocumentChunk`/`load_document` (`crates/core/src/documents.rs`) does structured
construction — heading-bounded chunking — but only at one flat passage-level
granularity. `query_document` can retrieve individual passages; it has no way to
answer "what is this whole document about." A survey of general agent-memory
architectures (arXiv 2512.13564, Sec 5.1.1) names this pattern directly: partitioned
semantic summarization (RAPTOR's recursive clustering + per-cluster summary;
ReadAgent/LightMem's cluster-then-summarize) applied to raw/verbose source data —
which `DocumentChunk` content genuinely is, unlike mimir's belief graph (see the
"Note on where Sec 5.1.1 does not apply" reasoning below).

**Deliberately smaller than RAPTOR**: one summary chunk per *document*, not a full
recursive cluster tree. Nothing has established that finer-grained cluster summaries
are wanted, and a full RAPTOR tree is meaningfully more mechanism (multi-level
clustering, per-cluster summarization, tree navigation in `query_document`) than the
stated problem needs. Start with the smallest version that answers "what's this
document about"; a cluster tree is a possible future escalation if one-summary-per-
document turns out insufficient, not a starting assumption.

## Why generation stays outside mimir-core

mimir-core has no LLM-completion client — only embedding backends
(`crates/core/src/embed.rs`: Voyage/OpenAI/Local, vectors only, no chat/completion) —
and none is being added for this feature. This mirrors the reasoning that kept the
Experiential-forgetting judge outside mimir-core: it ships as
`tartar/mimir-judge-experiential.nix` (a weekly `systemd --user` timer running
`claude -p` headless against an isolated mimir-only MCP config — see
`~/.claude/mimir-judge-experiential-prompt.md`), not as Rust. Same principle here: the
caller is already an LLM, so mimir's role stays storage + retrieval, never generation.
Concretely: an interactive Claude Code session calls `load_document`, then writes the
summary itself and pushes it via `set_document_summary` — or a periodic job does the
same for documents that need re-summarizing after edits, same shape as that timer.

## The design — already spec'd in `spec/Mimir/Documents.agda`

`DocumentChunk` gains one field, `isSummary : Bool` (always `false` for every chunk
`load_document`'s parser produces). A summary chunk is otherwise a completely
ordinary `DocumentChunk` — same AGE vertex label, same `chunk_embeddings` row, same
`CONTAINS` parent-child machinery — so this needs **no new AGE label, no new table**,
and it participates in `query_document`'s existing ANN ranking unmodified: a summary
chunk can surface there on its own semantic merit, same as any passage chunk, with no
RRF change (unlike section 3's `prefer_type` work — this doesn't need weight-tuning
because "what's this document about" is a direct lookup, not a ranked query).

Two new spec functions, mirroring `clearDocument`'s existing style:

- `setDocumentSummary : String → DocumentChunk → ChunkStore → ChunkStore` — upsert.
  Removes any existing summary chunk for the path first (via the new `removeSummary`
  helper, which — unlike `clearDocument` — touches only the one summary chunk, never
  the document's passage chunks), then prepends the new one. Calling this again after
  a document is re-summarized replaces rather than accumulates.
- `getDocumentSummary : String → ChunkStore → Maybe DocumentChunk` — direct fetch by
  path, not a semantic search.

Invariant (stated, not proved from types — same status as the file's existing
cross-store consistency invariant): at most one summary chunk per `documentPath`,
maintained by the upsert's remove-then-insert pattern. `clearDocument`/
`delete_project` need no change — both already operate on every chunk matching
`documentPath`/`project`, which naturally includes a document's summary chunk since
it's just another `DocumentChunk`.

## MCP / CLI surface (not yet implemented)

```
set_document_summary(path, content, project?) → {"chunk_id": ID}
  Required: path (must already be loaded via load_document), content (caller-
            generated summary text)
  Optional: project (propagated to the summary chunk like any other)
  Behaviour: upsert, see setDocumentSummary above.
  Errors: embedding model unreachable (the summary chunk is embedded like any
          other chunk), path never loaded (nothing to summarize).

get_document_summary(path) → {id, documentPath, content} | {"summary": null}
  Required: path
  Not a semantic search — direct lookup, see getDocumentSummary above.

mimir doc summary set PATH CONTENT [--project NAME]     # CLI mirror
mimir doc summary get PATH                               # CLI mirror
```

`clear_document(path)`'s existing behaviour needs no code change but does change in
effect: it removes everything matching `path`, so it now also removes that
document's summary chunk. Worth a one-line doc-comment update in `store.rs` when this
ships, not a new code path.

## Acceptance criteria

- `set_document_summary` on an unloaded path errors; on a loaded path creates exactly
  one summary chunk (`isSummary = true`, `sectionPath = []`, `parentId = nothing`).
- Calling `set_document_summary` twice for the same path leaves exactly one summary
  chunk (the second call's content), never two.
- `get_document_summary` on a path with no summary set returns `{"summary": null}`,
  not an error.
- `clear_document(path)` removes the summary chunk along with the passage chunks;
  `get_document_summary` afterward returns `{"summary": null}` again.
- A summary chunk is a normal candidate in `query_document`'s existing ANN search —
  no special-casing, no ranking change, verified by a query whose best semantic match
  happens to be the summary chunk itself.
- `spec/Mimir/Documents.agda` continues to type-check under `agda --safe`.

## Sequencing

Self-contained — no dependency on any other pending mimir work. The natural
integration point is right after `load_document` in an interactive session (prompt
the agent, in `SKILL.md` or `CLAUDE.md`, to consider writing a summary after loading
a long document) or as a periodic job for documents that get re-loaded/edited
regularly, mirroring section 2's `mimir-judge-experiential` timer.

{-# OPTIONS --safe #-}
module Mimir.Documents where

open import Mimir.Types
open import Data.Bool            using (Bool; true; false; not; _∧_)
open import Data.Nat             using (ℕ; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties  using (≤-refl; ≤-trans)
open import Data.String          using (String; _≟_)
open import Data.Maybe           using (Maybe; just; nothing)
open import Data.List            using (List; _∷_; []; length; take; _++_)
open import Data.List.Properties using (length-++; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary     using (does)

-- ---------------------------------------------------------------------------
-- SectionPath — the heading breadcrumb for a chunk within a document.
--
-- Examples (for a markdown plan):
--   []                         root chunk  (document preamble text)
--   ["Task 2"]                 chunk directly under "## Task 2"
--   ["Task 2", "Step 3"]       chunk under "## Task 2" > "### Step 3"
--
-- Depth = length of SectionPath.  Root chunks have depth 0.
-- A chunk's parent has sectionPath = init of the chunk's sectionPath
-- (all but the last element), so parentDepth = chunkDepth − 1.
-- The parser enforces this: each heading starts a new chunk whose parent
-- is the innermost enclosing heading, or the document root at top level.
-- ---------------------------------------------------------------------------

SectionPath : Set
SectionPath = List String

chunkDepth : SectionPath → ℕ
chunkDepth = length

rootDepth-zero : chunkDepth [] ≡ 0
rootDepth-zero = refl

nestedDepth-suc : ∀ (h : String) (rest : SectionPath) →
  chunkDepth (h ∷ rest) ≡ Data.Nat.suc (chunkDepth rest)
nestedDepth-suc h rest = refl

-- ---------------------------------------------------------------------------
-- DocumentChunk — one markdown section bounded by heading boundaries.
-- Stored as an AGE vertex with label "DocumentChunk".
--
-- Two stores are maintained in sync (see CONSISTENCY INVARIANT below):
--
--   AGE graph: DocumentChunk vertices linked by CONTAINS edges.
--
--   PostgreSQL table (public schema):
--     CREATE TABLE chunk_embeddings (
--       chunk_id  UUID PRIMARY KEY,      -- matches DocumentChunk.chunkId
--       embedding vector(N)              -- N set by embedding model (e.g. 1024)
--     );
--     CREATE INDEX ON chunk_embeddings USING hnsw (embedding vector_cosine_ops);
--
-- load_document and clear_document must write/delete BOTH stores.
-- A failure between the two writes leaves the stores inconsistent (silent
-- misses on query_document, or orphaned rows in chunk_embeddings).
-- ---------------------------------------------------------------------------

record DocumentChunk : Set where
  constructor mkChunk
  field
    chunkId      : NodeId
    documentPath : String         -- source file; primary key for clear_document
    sectionPath  : SectionPath    -- [] for root chunks; h ∷ rest for nested chunks
    content      : String         -- raw markdown text of this chunk, OR (when
                                  -- isSummary ≡ true) LLM-generated summary text
    parentId     : Maybe NodeId   -- nothing for root chunks; just p otherwise
                                  -- invariant: parentId ≡ nothing ↔ sectionPath ≡ []
                                  -- (enforced by parser, not by this record type)
    project      : Maybe String   -- propagated from load_document's project argument
    isSummary    : Bool           -- false for every chunk load_document parses.
                                  -- true only for a chunk written by
                                  -- set_document_summary (section 5,
                                  -- docs/proposals/80-memory-evolution-open-
                                  -- questions.md). A summary chunk is a normal
                                  -- DocumentChunk otherwise — same AGE label,
                                  -- same chunk_embeddings row, same CONTAINS
                                  -- parent-child machinery — so it needs no new
                                  -- storage and participates in query_document's
                                  -- existing ANN ranking unmodified. Always a
                                  -- root chunk: sectionPath ≡ [], parentId ≡
                                  -- nothing (enforced by set_document_summary,
                                  -- not by this record type, same status as the
                                  -- parentId/sectionPath invariant above).

-- ---------------------------------------------------------------------------
-- CONTAINS — AGE edge label connecting parent DocumentChunk to child.
-- Structural only: no weight, no belief-inference propagation.
-- Kept separate from EdgeLabel (Types.agda) to avoid modifying the belief
-- graph propagation logic.
-- ensure_labels is extended at startup to also create the "DocumentChunk"
-- vertex label and "CONTAINS" edge label (see DocumentLabelState below).
-- ---------------------------------------------------------------------------

data DocumentEdgeLabel : Set where
  CONTAINS : DocumentEdgeLabel

-- CONTAINS never triggers belief propagation.
containsNoPropagate : ∀ (e : DocumentEdgeLabel) → e ≡ CONTAINS
containsNoPropagate CONTAINS = refl

-- ---------------------------------------------------------------------------
-- Embedding — abstract model of a pgvector entry.
-- Represented as List ℕ (integer-quantized float vector).
-- Real implementation: pgvector vector(N); cosine distance via <=> operator.
-- N must be consistent across all entries in chunk_embeddings — mixing
-- embedding models after data is loaded requires a full re-index.
-- ---------------------------------------------------------------------------

Embedding : Set
Embedding = List ℕ

record EmbeddingEntry : Set where
  constructor mkEmbed
  field
    embedChunkId : NodeId
    embedding    : Embedding

-- ---------------------------------------------------------------------------
-- Storage types
-- ---------------------------------------------------------------------------

ChunkStore     : Set
ChunkStore = List DocumentChunk

EmbeddingStore : Set
EmbeddingStore = List EmbeddingEntry

-- ---------------------------------------------------------------------------
-- CONSISTENCY INVARIANT (stated; not proved from types)
--
-- At all times, the two stores track exactly the same set of chunk IDs:
--   ∀ c ∈ ChunkStore. ∃! e ∈ EmbeddingStore. e.embedChunkId = c.chunkId
--   ∀ e ∈ EmbeddingStore. ∃! c ∈ ChunkStore. c.chunkId = e.embedChunkId
--
-- Maintained by:
--   load_document   — inserts N chunks into AGE and N rows into chunk_embeddings
--   clear_document  — deletes matching AGE vertices and their embedding rows
--   delete_project  — extended to also delete DocumentChunk vertices (see below)
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- matchesDocument: does a chunk belong to a given document path?
-- ---------------------------------------------------------------------------

matchesDocument : String → DocumentChunk → Bool
matchesDocument path c = does (DocumentChunk.documentPath c ≟ path)

-- ---------------------------------------------------------------------------
-- chunkMatchesProject: is a chunk tagged with a given project?
-- delete_project is extended to cover DocumentChunk vertices in addition to
-- Belief vertices.  Chunks with project = nothing are unaffected.
-- ---------------------------------------------------------------------------

chunkMatchesProject : String → DocumentChunk → Bool
chunkMatchesProject proj c with DocumentChunk.project c
... | nothing = false
... | just p  = does (p ≟ proj)

-- ---------------------------------------------------------------------------
-- isSummaryAndMatches: is this chunk the summary chunk for a given document?
-- ---------------------------------------------------------------------------

isSummaryAndMatches : String → DocumentChunk → Bool
isSummaryAndMatches path c = matchesDocument path c ∧ DocumentChunk.isSummary c

-- ---------------------------------------------------------------------------
-- removeSummary: drop the existing summary chunk for a document, if any.
-- Leaves every other chunk (passage or another document's summary) untouched
-- — the key difference from clearDocument, which drops the WHOLE document.
-- ---------------------------------------------------------------------------

removeSummary : String → ChunkStore → ChunkStore
removeSummary path []       = []
removeSummary path (c ∷ cs) with isSummaryAndMatches path c
... | true  = removeSummary path cs
... | false = c ∷ removeSummary path cs

-- removeSummary never increases the store size (same proof shape as
-- clearDocument-smaller below, which reuses its own copy of this helper —
-- defined here too since Agda processes the file top-to-bottom and that
-- copy isn't in scope yet at this point).
private
  n≤suc-n-doc : ∀ n → n ≤ Data.Nat.suc n
  n≤suc-n-doc Data.Nat.zero    = z≤n
  n≤suc-n-doc (Data.Nat.suc m) = s≤s (n≤suc-n-doc m)

removeSummary-smaller :
  ∀ (path : String) (cs : ChunkStore) →
  length (removeSummary path cs) ≤ length cs
removeSummary-smaller path []       = z≤n
removeSummary-smaller path (c ∷ cs) with isSummaryAndMatches path c
... | true  = ≤-trans (removeSummary-smaller path cs) (n≤suc-n-doc (length cs))
... | false = s≤s (removeSummary-smaller path cs)

-- ---------------------------------------------------------------------------
-- setDocumentSummary: upsert the one summary chunk for a document.
-- MCP tool: set_document_summary(path, content, project?) → {"chunk_id": ID}
--
-- Implementation: same two-store write as loadDocument (AGE vertex +
-- chunk_embeddings row) but for exactly one chunk, with isSummary = true,
-- sectionPath = [], parentId = nothing. Upsert semantics: any prior summary
-- chunk for the same path is removed first, so calling this again (e.g. after
-- a document is re-summarized following a re-load) replaces rather than
-- accumulates. Does NOT touch passage chunks — orthogonal to load_document/
-- clear_document, callable independently and in either order relative to
-- them.
--
-- Who calls this: NOT mimir itself. mimir-core has no LLM-completion client
-- (only embedding backends — see embed.rs) and none is being added for this
-- feature; the same reasoning that kept the Experiential-forgetting judge
-- (section 2) OUTSIDE mimir-core applies here. The caller (an interactive
-- Claude Code session right after load_document, or a periodic job like
-- section 2's) generates the summary text and pushes it via this tool.
-- mimir's role stays storage + retrieval, never generation.
-- ---------------------------------------------------------------------------

setDocumentSummary : String → DocumentChunk → ChunkStore → ChunkStore
setDocumentSummary path summary cs = summary ∷ removeSummary path cs

-- ---------------------------------------------------------------------------
-- getDocumentSummary: direct fetch of a document's summary chunk, if any.
-- MCP tool: get_document_summary(path) → chunk object | {"summary": null}
--
-- Deliberately NOT a semantic search like query_document — "what is this
-- document about" is an exact lookup by path, not a ranked query, so no RRF
-- weighting is involved (avoids repeating section 3's weight-tuning problem
-- for a case that doesn't need it). query_document's own ranking is
-- UNCHANGED by this feature: a summary chunk is embedded and stored exactly
-- like any passage chunk, so it can also surface there on its own semantic
-- merit — this tool exists only for the direct "give me the summary" ask.
-- ---------------------------------------------------------------------------

getDocumentSummary : String → ChunkStore → Maybe DocumentChunk
getDocumentSummary path []       = nothing
getDocumentSummary path (c ∷ cs) with isSummaryAndMatches path c
... | true  = just c
... | false = getDocumentSummary path cs

-- ---------------------------------------------------------------------------
-- AT-MOST-ONE-SUMMARY INVARIANT (stated; not proved from types — same status
-- as the CONSISTENCY INVARIANT above)
--
-- At all times, for every documentPath, at most one chunk in ChunkStore has
-- isSummary ≡ true for that path. Maintained by setDocumentSummary's
-- remove-then-insert pattern (never by clearDocument or loadDocument, which
-- are unaware of isSummary and simply carry it through on whatever chunks
-- they're given — load_document always constructs isSummary = false).
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- clearDocument: remove all chunks for a given file path.
-- MCP tool: clear_document(path) → {"cleared": N}
--
-- Implementation:
--   (1) Cypher: MATCH (c:DocumentChunk {documentPath: '<path>'}) DETACH DELETE c
--       DETACH DELETE removes all CONTAINS edges incident to deleted chunks.
--   (2) SQL:    DELETE FROM chunk_embeddings WHERE chunk_id IN (<ids from step 1>)
--
-- Returns {"cleared": 0} when path was not loaded — not an error.
-- ---------------------------------------------------------------------------

clearDocument : String → ChunkStore → ChunkStore
clearDocument path []       = []
clearDocument path (c ∷ cs) with not (matchesDocument path c)
... | true  = c ∷ clearDocument path cs
... | false = clearDocument path cs

private
  n≤suc-n : ∀ n → n ≤ Data.Nat.suc n
  n≤suc-n Data.Nat.zero    = z≤n
  n≤suc-n (Data.Nat.suc m) = s≤s (n≤suc-n m)

-- clearDocument never increases the store size.
clearDocument-smaller :
  ∀ (path : String) (cs : ChunkStore) →
  length (clearDocument path cs) ≤ length cs
clearDocument-smaller path []       = z≤n
clearDocument-smaller path (c ∷ cs) with not (matchesDocument path c)
... | true  = s≤s (clearDocument-smaller path cs)
... | false = ≤-trans (clearDocument-smaller path cs) (n≤suc-n (length cs))

-- clearDocument on an empty store is a no-op.
clearDocument-empty : ∀ (path : String) → clearDocument path [] ≡ []
clearDocument-empty _ = refl

-- ---------------------------------------------------------------------------
-- clearChunksByProject: bulk-delete chunks tagged with a project.
-- Called by the extended delete_project implementation alongside the
-- existing Belief deletion.  Modelled symmetrically to deleteProject
-- in Graph.agda.
-- ---------------------------------------------------------------------------

clearChunksByProject : String → ChunkStore → ChunkStore
clearChunksByProject proj []       = []
clearChunksByProject proj (c ∷ cs) with not (chunkMatchesProject proj c)
... | true  = c ∷ clearChunksByProject proj cs
... | false = clearChunksByProject proj cs

clearChunksByProject-smaller :
  ∀ (proj : String) (cs : ChunkStore) →
  length (clearChunksByProject proj cs) ≤ length cs
clearChunksByProject-smaller proj []       = z≤n
clearChunksByProject-smaller proj (c ∷ cs) with not (chunkMatchesProject proj c)
... | true  = s≤s (clearChunksByProject-smaller proj cs)
... | false = ≤-trans (clearChunksByProject-smaller proj cs) (n≤suc-n (length cs))

-- ---------------------------------------------------------------------------
-- loadDocument: parse and index a document.
-- MCP tool: load_document(path, project?) → {"loaded": N}
--
-- Behaviour:
--   (1) Clear any existing chunks for `path` (replace-on-reload semantics).
--   (2) Parse the document into heading-bounded chunks (the markdown parser
--       produces `newChunks`; all have documentPath = path).
--   (3) Insert new chunks into AGE.
--   (4) Compute embeddings for each new chunk and insert into chunk_embeddings.
--   (5) Auto-ground: for each new chunk, find existing beliefs whose stored
--       embedding has cosine similarity ≥ GROUND_THRESHOLD (0.80) to the
--       chunk embedding AND whose project is compatible (same project, or
--       chunk/belief project is absent). Create a GROUNDS edge for each match.
--       Formalised in Evidence.autoGroundChunks.
--
-- Calling load_document on an already-loaded document replaces the old
-- chunks rather than erroring — safe to call after document edits.
-- Returns an error if the embedding model is unreachable or unconfigured.
-- ---------------------------------------------------------------------------

loadDocument : String → List DocumentChunk → ChunkStore → ChunkStore
loadDocument path newChunks cs = newChunks ++ clearDocument path cs

-- Length of the store after loading.
loadDocument-length :
  ∀ (path : String) (newChunks : List DocumentChunk) (cs : ChunkStore) →
  length (loadDocument path newChunks cs) ≡
    length newChunks + length (clearDocument path cs)
loadDocument-length path newChunks cs = length-++ newChunks

-- Loading into an empty store yields exactly newChunks.
loadDocument-from-empty :
  ∀ (path : String) (newChunks : List DocumentChunk) →
  loadDocument path newChunks [] ≡ newChunks
loadDocument-from-empty path newChunks = ++-identityʳ newChunks

-- ---------------------------------------------------------------------------
-- query_document: semantic retrieval over loaded chunks.
-- MCP tool: query_document(context, project?, limit) → JSON array
--
-- Implementation:
--   (1) Embed the context string via the configured embedding model.
--   (2) SELECT chunk_id FROM chunk_embeddings
--         [WHERE chunk_id IN (ids of project-scoped chunks)]
--         ORDER BY embedding <=> $query_vec   -- cosine ANN via HNSW index
--         LIMIT k
--   (3) Fetch matched DocumentChunk vertices from AGE by ID.
--   (4) For each result, fetch its parent chunk via the CONTAINS edge
--       (one level up) to provide the heading context.
--   (5) Return results ordered by cosine similarity descending.
--
-- Each result object: {id, documentPath, sectionPath, content, parentContent?}
-- parentContent is the parent chunk's content (heading + immediate text),
-- present for all non-root results; absent for root chunks.
--
-- Cosine similarity ranking is not modelable in --safe Agda (requires
-- real-valued arithmetic).  The limit bound is provable:
-- ---------------------------------------------------------------------------

-- query_document result length ≤ limit.
-- Proof: same structure as take-length in Graph.agda.
queryDocument-limit-bound :
  ∀ (limit : ℕ) (results : ChunkStore) →
  length (take limit results) ≤ limit
queryDocument-limit-bound Data.Nat.zero    _        = z≤n
queryDocument-limit-bound (Data.Nat.suc n) []       = z≤n
queryDocument-limit-bound (Data.Nat.suc n) (_ ∷ cs) = s≤s (queryDocument-limit-bound n cs)

-- limit = 0 means no truncation: take 0 returns [].
-- The implementation interprets limit=0 as "no limit" and skips truncation;
-- the spec model does not capture this (take 0 = []).  The implementation
-- branches on limit before calling take.

-- ---------------------------------------------------------------------------
-- DocumentLabelState — the label/table provisioning the document overlay needs.
-- Startup idempotently ensures the document machinery exists alongside the
-- belief graph:
--   vertex label  "DocumentChunk"
--   edge label    "CONTAINS"
-- and the chunk_embeddings table + its ANN index, created if absent.
-- ---------------------------------------------------------------------------

record DocumentLabelState : Set where
  constructor mkDocLabels
  field
    documentChunkLabelCreated : Bool   -- AGE vertex label "DocumentChunk"
    containsLabelCreated      : Bool   -- AGE edge label "CONTAINS"
    embeddingTableCreated     : Bool   -- chunk_embeddings table + HNSW index in public schema

documentLabelsReady : DocumentLabelState → Bool
documentLabelsReady s =
  DocumentLabelState.documentChunkLabelCreated s ∧
  DocumentLabelState.containsLabelCreated      s ∧
  DocumentLabelState.embeddingTableCreated      s

ensureDocumentLabels : DocumentLabelState → DocumentLabelState
ensureDocumentLabels _ = mkDocLabels true true true

ensureDocumentLabels-idempotent :
  ∀ (s : DocumentLabelState) →
  ensureDocumentLabels (ensureDocumentLabels s) ≡ ensureDocumentLabels s
ensureDocumentLabels-idempotent _ = refl

ensureDocumentLabels-complete :
  ∀ (s : DocumentLabelState) →
  documentLabelsReady (ensureDocumentLabels s) ≡ true
ensureDocumentLabels-complete _ = refl

-- ---------------------------------------------------------------------------
-- MCP interface notes
-- ---------------------------------------------------------------------------
--
-- load_document(path, project?)
--   Required: path (file path, absolute or repo-relative)
--   Optional: project (string tag; if absent, chunks are unscoped)
--   Returns:  {"loaded": N}   N = number of chunks created
--   Errors:   embedding model unreachable, file not found, parse error
--
-- query_document(context, project?, limit)
--   Required: context (the query string to embed)
--   Optional: project (restrict search to chunks tagged with this project)
--             limit (integer ≥ 0; 0 = no limit)
--   Returns:  JSON array of {id, documentPath, sectionPath, content,
--               parentContent?} objects, ordered by cosine similarity desc.
--   Errors:   embedding model unreachable
--
-- clear_document(path)
--   Required: path
--   Returns:  {"cleared": N}  N = number of chunks removed (0 if not loaded)
--   No-op if path was never loaded. Also removes that document's summary
--   chunk, if any — clear_document is unaware of isSummary and removes
--   everything matching the path, summary included.
--
-- set_document_summary(path, content, project?)     [section 5, new]
--   Required: path (must already be loaded via load_document), content
--             (the summary text — caller-generated, see setDocumentSummary
--             above for why mimir itself never generates it)
--   Optional: project (propagated to the summary chunk like any other)
--   Returns:  {"chunk_id": ID}
--   Behaviour: upsert — replaces this document's existing summary chunk if
--     one exists, never accumulates. Independent of load_document/
--     clear_document; callable before or after either.
--   Errors:   embedding model unreachable (the summary chunk is embedded
--             like any other), path never loaded (no passage chunks to
--             summarize)
--
-- get_document_summary(path)                        [section 5, new]
--   Required: path
--   Returns:  {id, documentPath, content} | {"summary": null} if none set
--   Not a semantic search — direct lookup, see getDocumentSummary above.
--
-- delete_project (EXTENDED)
--   Now removes DocumentChunk vertices tagged with the project in addition
--   to Belief vertices.  Returns {"deleted": N} where N is the combined count
--   of Belief + DocumentChunk vertices removed.
--   EmbeddingStore rows for removed chunks are also deleted.
--
-- EMBEDDING CONFIG — required addition to config.toml:
--
--   [embeddings]
--   backend = "voyage"          # voyage | openai | local
--   model   = "voyage-3-lite"   # or voyage-code-3, text-embedding-3-small, …
--   api_key = "pa-..."          # from env or config; never committed to git
--
-- The embedding model must be consistent across all load_document calls.
-- Switching models after data is loaded produces incorrect similarity rankings
-- (vectors are not comparable across models).  To switch: clear all documents,
-- update config, reload.
-- ---------------------------------------------------------------------------

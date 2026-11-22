# How document search selects and ranks passages

Mimir embeds the query text, then searches a single database snapshot
for indexed passages. A project filter includes only passages tagged
with exactly that project. Without a project filter, Mimir searches
across projects. Each eligible passage has a usable index vector.

Results are ordered by cosine distance, closest first. Equal distances
may appear in either order. Omitting the result count returns all eligible
passages, and a positive count takes the first results in that order.
A result includes its passage UUID, document, section, and text. Parent
text is included when the parent still belongs to the same document
and project in that snapshot.

[PostgreSQL cosine distance](https://github.com/pgvector/pgvector#vector-operators) · [Rust document search](../../crates/core/src/lib.rs#L1028)

```agda
{-# OPTIONS --safe #-}
module Mimir.DocumentQuery where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Bool.ListAction using (all; any)
open import Data.Float.Base using (Float; isNaN; isInfinite; _<ᵇ_; _≤ᵇ_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text; nonblank)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.UUIDGroups using (UUID)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.Effects as Effects
import Mimir.PosteriorComputation as Lookup
import Mimir.RetrievalRanking as Ranking

record Hit : Set where
  constructor hit
  field identity : UUID; document : Text; section : List Text; content : Text; parentContent : Maybe Text

sameProject : Maybe Text → Maybe Text → Bool
sameProject nothing nothing = true
sameProject (just a) (just b) = does (a ≟Text b)
sameProject _ _ = false

matchesProject : Maybe Text → Documents.Chunk → Bool
matchesProject nothing chunk = true
matchesProject (just tag) chunk = sameProject (just tag) (Documents.Chunk.project chunk)

parentFor : List Documents.Chunk → Documents.Chunk → Maybe Text
parentFor chunks chunk with Documents.Chunk.parent chunk
... | nothing = nothing
... | just id with Lookup.lookup id (map (λ c → Documents.Chunk.identity c , c) chunks)
...   | nothing = nothing
...   | just parent with does (Documents.Chunk.document parent ≟Text Documents.Chunk.document chunk) ∧
                          sameProject (Documents.Chunk.project parent) (Documents.Chunk.project chunk)
...     | true = just (Documents.Chunk.content parent)
...     | false = nothing

project : List Documents.Chunk → Documents.Chunk → Hit
project chunks c = hit (Documents.Chunk.identity c) (Documents.Chunk.document c)
  (Documents.Chunk.section c) (Documents.Chunk.content c) (parentFor chunks c)

usableVector : Store.Vector → Bool
usableVector vector =
  all (λ x → not (isNaN x ∨ isInfinite x)) vector ∧
  any (λ x → (x <ᵇ 0.0) ∨ (0.0 <ᵇ x)) vector

Candidate = Documents.Chunk × Store.Vector

eligible : Maybe Text → List (UUID × Store.Vector) → List Documents.Chunk → List Candidate
eligible scope vectors [] = []
eligible scope vectors (chunk ∷ rest)
  with matchesProject scope chunk | Lookup.lookup (Documents.Chunk.identity chunk) vectors
... | true | just vector with usableVector vector
...   | true = (chunk , vector) ∷ eligible scope vectors rest
...   | false = eligible scope vectors rest
eligible scope vectors (chunk ∷ rest) | _ | _ = eligible scope vectors rest

-- PostgreSQL supplies the distance comparison. The spec constrains its
-- ordering and candidate coverage without implementing a cosine calculator.
Distance = Store.Vector → Store.Vector → Float

ordered : Distance → Store.Vector → List Candidate → Bool
ordered distance query [] = true
ordered distance query (_ ∷ []) = true
ordered distance query (first ∷ later@(second ∷ rest)) =
  (distance query (proj₂ first) ≤ᵇ distance query (proj₂ second)) ∧ ordered distance query later

data Effect : Set where
  embed : Text → Effect
  searchIndex : Store.Vector → Maybe ℕ → Maybe Text → Effect

Reply : Effect → Set
Reply (embed query) = Text ⊎ List Store.Vector
Reply (searchIndex vector limit scope) = Text ⊎ List Hit

Observed : Distance → Store.World → (effect : Effect) → Reply effect → Set
Observed distance before (searchIndex vector limit scope) (inj₂ hits) =
  Σ (List Candidate) (λ ranked →
    (ranked ↭ eligible scope (Store.World.chunkVectors before) chunks) ×
    ordered distance vector ranked ≡ true ×
    hits ≡ map (λ { (chunk , _) → project chunks chunk }) (Ranking.cap limit ranked))
  where chunks = Store.World.chunks before
Observed distance before effect reply = ⊤

module E = Effects.Protocol Effect Reply
open E
```

## Distinguish an empty result from unavailable search

A blank query asks the caller to supply search text. A missing provider,
a provider failure, an unusable provider reply, or an index failure
produces an unavailable outcome with a reason. Over MCP, a blank query
returns `needs_correction`, and unavailable search returns `needs_input`
with guidance. A successful search with no eligible indexed passages
returns an empty list.

A query vector must contain finite numbers and have a nonzero component
so cosine distance is defined. The provider must return exactly one
vector for the one query. Search leaves stored beliefs and evidence
unchanged. Similarity ranks passages for inspection and gives no new
evidence to a belief.

```agda
data Result : Set where
  invalidContext : Result
  unavailable : Text → Result
  found : List Hit → Result

afterSearch : Text ⊎ List Hit → Script Result
afterSearch (inj₁ error) = done (unavailable error)
afterSearch (inj₂ hits) = done (found hits)

invalidEmbedding : Result
invalidEmbedding = unavailable (toList "Semantic document search is unavailable. The embedding provider must return one finite, nonzero vector for the query. Correct the provider and retry.")

afterEmbedding : Maybe ℕ → Maybe Text → Text ⊎ List Store.Vector → Script Result
afterEmbedding limit scope (inj₁ error) = done (unavailable error)
afterEmbedding limit scope (inj₂ (vector ∷ [])) with usableVector vector
... | true = ask (searchIndex vector limit scope) afterSearch
... | false = done invalidEmbedding
afterEmbedding limit scope (inj₂ _) = done invalidEmbedding

start : Bool → Text → Maybe ℕ → Maybe Text → Script Result
start enabled query limit scope with nonblank query
... | false = done invalidContext
... | true with enabled
...   | false = done (unavailable (toList "Semantic document search is unavailable because no embedding provider is configured. Configure an embedding provider and retry."))
...   | true = ask (embed query) (afterEmbedding limit scope)
```

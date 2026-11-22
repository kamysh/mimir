# Reading the evidence for a belief

Mimir returns the passages that are currently linked to a belief as sources.
Each citation identifies the stored passage and includes its document path,
section path, trimmed text, and the weight of **that link**. A zero-weight
source still counts as a citation. The same passage can carry different weights
for different beliefs.

```agda
{-# OPTIONS --safe #-}
module Mimir.EvidenceRead where

open import Data.Bool using (not; _∧_)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.List using (List; []; _∷_; filterᵇ; map)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text; trim)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
import Mimir.DocumentStore as Documents
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as G
import Mimir.RetrievalRanking as Ranking
import Mimir.PosteriorComputation as Lookup
import Mimir.Effects as Effects

record Reference : Set where
  constructor reference
  field chunk : UUID; document : Text; section : List Text; snippet : Text; weight : Float

record Grounded : Set where
  constructor grounded
  field belief : G.BeliefValues; evidence : List Reference

referenceOf : Float → Documents.Chunk → Reference
referenceOf weight c = reference (Documents.Chunk.identity c) (Documents.Chunk.document c)
  (Documents.Chunk.section c) (trim (Documents.Chunk.content c)) weight
```

## Read the link and passage together

All citations in a reply come from one database read. Each returned row
contains a grounding link and its existing passage. A missing passage
contributes no citation and uses none of the requested count. For example,
when a document is replaced while evidence is being read, the reply sees the
links and passages from the same database view. A database error propagates
to the caller so an unsuccessful read cannot look like an empty list.

The query in [the store](../../crates/core/src/store.rs) matches both ends of
each grounding link and projects its passage and weight together.

```agda
record LinkedPassage : Set where
  constructor linkedPassage
  field
    belief : UUID
    passage : Documents.Chunk
    weight : Float

data Effect : Set where
  readEvidence : List UUID → Effect

Reply : Effect → Set
Reply (readEvidence ids) = Text ⊎ List LinkedPassage

linkedPassages : List UUID → Store.World → List LinkedPassage
linkedPassages ids before = collect (filterᵇ selected (Store.World.grounds before))
  where
  known = map G.BeliefValues.identity (Store.beliefs before)
  selected = λ link → Ranking.member (Store.Ground.belief link) ids ∧
                      Ranking.member (Store.Ground.belief link) known
  passages = map (λ chunk → Documents.Chunk.identity chunk , chunk) (Store.World.chunks before)

  collect : List Store.Ground → List LinkedPassage
  collect [] = []
  collect (link ∷ rest) with Lookup.lookup (Store.Ground.chunk link) passages
  ... | nothing = collect rest
  ... | just chunk =
    linkedPassage (Store.Ground.belief link) chunk (Store.Ground.weight link) ∷ collect rest

Observed : Store.World → (effect : Effect) → Reply effect → Set
Observed before (readEvidence ids) (inj₂ rows) = rows ↭ linkedPassages ids before
Observed before (readEvidence ids) (inj₁ error) = ⊤

module E = Effects.Protocol Effect Reply
open E
```

## Rank citations and preserve search order

Within a belief, Mimir returns stronger links first. Equal weights retain
the order of the database reply. Passage UUIDs identify passages and are used
only to test identity. The optional count applies separately to each belief
after missing passages have been excluded. Omitting it returns every linked
passage. The [public request decoder](PublicRequest.agda) requires a positive
count when the caller supplies one.

`get_evidence` reads sources for an exact belief UUID and returns the full
citation list. `query_relevant` with evidence uses the same search settings as
ordinary retrieval, including the requested belief type preference, then
attaches citations in the resulting belief order. The evidence read follows
ranking. Beliefs with no citations retain their place and carry an empty
evidence list. The semantic-search status comes from retrieval.

[ApplicationProtocol](ApplicationProtocol.agda) composes these steps.
[PublicEncoding](PublicEncoding.agda) defines the MCP reply and
[the service](../../crates/core/src/lib.rs) supplies citations to MCP and the CLI.

```agda
ranked : UUID → Maybe ℕ → List LinkedPassage → List Reference
ranked belief limit rows = map toReference (Ranking.cap limit (Ranking.sort
  (λ a b → not (LinkedPassage.weight a <ᵇ LinkedPassage.weight b))
  (filterᵇ (λ row → does (belief ≟UUID LinkedPassage.belief row)) rows)))
  where
  toReference : LinkedPassage → Reference
  toReference row = referenceOf (LinkedPassage.weight row) (LinkedPassage.passage row)

one : UUID → Maybe ℕ → Script (Text ⊎ List Reference)
one belief limit = ask (readEvidence (belief ∷ [])) (λ
  { (inj₁ error) → done (inj₁ error)
  ; (inj₂ rows) → done (inj₂ (ranked belief limit rows)) })

many : Maybe ℕ → List G.BeliefValues → Script (Text ⊎ List Grounded)
many limit [] = done (inj₂ [])
many limit beliefs@(_ ∷ _) = ask (readEvidence (map G.BeliefValues.identity beliefs)) (λ
  { (inj₁ error) → done (inj₁ error)
  ; (inj₂ rows) → done (inj₂ (map (attach rows) beliefs)) })
  where
  attach : List LinkedPassage → G.BeliefValues → Grounded
  attach rows belief = grounded belief (ranked (G.BeliefValues.identity belief) limit rows)
```

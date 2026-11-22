# How a review publishes new beliefs

A review can propose new beliefs about an experience. The caller chooses
an indexed passage for each new belief and provides its existing UUID.
Mimir prepares the belief's embedding before committing the review. If
preparation fails, the review and its proposed beliefs remain unsaved,
and the caller can correct the problem and submit the review again.

Before embedding a new belief, Mimir checks that the review still
targets the current experience and review revisions. The commit checks
again because either revision can change during preparation.

[Review service in Rust](../../crates/core/src/learning.rs#L442) · [Direct belief publication](BeliefEmbedding.lagda.md)

```agda
{-# OPTIONS --safe #-}
-- Review-created beliefs require the same prepared vector and indexed source
-- as independent beliefs. Preparation is private; publication changes all
-- required records together and does not invent evidence strength.
module Mimir.ReviewBeliefPreparation where

open import Data.Bool using (true; false)
open import Data.Float.Base using (isNaN; isInfinite)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
import Mimir.Text as Text
open import Relation.Nullary using (yes; no)
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.RetrievalRanking as Ranking
import Mimir.BeliefEmbedding as Belief
import Mimir.DocumentStore as Documents
import Mimir.CandidateRegistry as Registry
import Mimir.LearningCandidates as Candidates
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication

```

## Prepare one set of materials for each new belief

The preparation contract, `Complete`, relates the store before the
review to the proposed store. Each new belief must have one embedding
and one supporting passage. The passage must be the one selected in the
candidate declaration, contain text, and have an indexed vector. A passage
can be shared across projects or belong to the belief's project.
The belief embedding must be nonempty and contain only finite numbers.

One entry per new belief matters because publication writes one vector
and one source link per entry. Rust rejects repeated candidate keys,
stores preparation by candidate key, and PostgreSQL prevents two
candidate keys from sharing a stored identity. The Agda contract requires
unique belief identities in the prepared entries.

[Candidate validation](../../crates/core/src/learning.rs#L247) · [PostgreSQL candidate identity rule](../../crates/core/migrations/007_review_candidates.sql#L6) · [Material checks before commit](../../crates/core/src/store.rs#L560)

```agda
Material = UUID × Belief.Prepared

selectedPassage : UUID → Registry.Registry → Maybe UUID
selectedPassage id [] = nothing
selectedPassage id (row ∷ rest) with id ≟UUID Registry.Entry.nodeID row
... | no _ = selectedPassage id rest
... | yes _ with Registry.Entry.declaration row
...   | Candidates.belief key content memory source = source
...   | Candidates.patternCandidate key situation approach = nothing

record Complete (before proposed : Store.World) (materials : List Material) : Set where
  field
    -- Every newly published belief has a nonempty vector and an indexed
    -- supporting passage. The external preparation boundary validates support.
    coversNew : ∀ belief → belief ∈ Store.beliefs proposed →
      Ranking.lookup (Graph.BeliefValues.identity belief) (Store.beliefs before) ≡ nothing →
      Σ Belief.Prepared (λ material → (Graph.BeliefValues.identity belief , material) ∈ materials)
    onlyNew : ∀ id material → (id , material) ∈ materials →
      Ranking.lookup id (Store.beliefs before) ≡ nothing
    onePerBelief : Registry.IDs.Unique (map proj₁ materials)
    belongsToProposal : ∀ id material → (id , material) ∈ materials →
      Σ Graph.BeliefValues (λ belief → belief ∈ Store.beliefs proposed ×
        Graph.BeliefValues.identity belief ≡ id ×
        ((Documents.Chunk.project (Belief.Prepared.supportingPassage material) ≡ nothing) ⊎
         (Documents.Chunk.project (Belief.Prepared.supportingPassage material) ≡ Graph.BeliefValues.project belief)))
    supportIndexed : ∀ id material → (id , material) ∈ materials →
      let passage = Belief.Prepared.supportingPassage material in
      passage ∈ Store.World.chunks before ×
      Text.nonblank (Documents.Chunk.content passage) ≡ true ×
      Σ Store.Vector (λ vector → (Documents.Chunk.identity passage , vector) ∈ Store.World.chunkVectors before)
    finiteEmbedding : ∀ id material → (id , material) ∈ materials →
      All.All (λ x → isNaN x ≡ false × isInfinite x ≡ false) (Belief.vector material)
    selectedSupportMatches : ∀ id material → (id , material) ∈ materials →
      selectedPassage id (Publication.World.registry
        (Learning.World.publication (Store.World.learning proposed))) ≡
      just (Documents.Chunk.identity (Belief.Prepared.supportingPassage material))

```

## Commit the review and its materials together

The review commit publishes the new beliefs, their vectors and source
links together with the review. The link records the source with
weight zero. Attaching it leaves the proposed belief values unchanged.
Other evidence in the review can still affect the result.

Rust rechecks the selected passage before committing. The Agda
application protocol makes a failed commit leave the original store
unchanged. That lets the caller restart the original review after
correcting the cause.

[Agda commit rule](ApplicationProtocol.agda#L280) · [Rust review transaction](../../crates/core/src/store/learning.rs#L520) · [Why the source weight is zero](BeliefEmbedding.lagda.md#why-the-source-link-has-zero-evidence-weight)

```agda
vectorRow : Material → UUID × Store.Vector
vectorRow (id , material) = id , Belief.vector material

sourceRow : Material → Store.Ground
sourceRow (id , material) = Store.ground
  (Documents.Chunk.identity (Belief.Prepared.supportingPassage material)) id 0.0

-- A supporting passage is a source reference, not an agent-selected update
-- to probability. The proposed belief values are preserved exactly.
publish : List Material → Store.World → Store.World
publish materials proposed = record proposed
  { beliefVectors = map vectorRow materials ++ Store.World.beliefVectors proposed
  ; grounds = map sourceRow materials ++ Store.World.grounds proposed }

vectorStored : ∀ id material materials proposed → (id , material) ∈ materials →
  vectorRow (id , material) ∈ Store.World.beliefVectors (publish materials proposed)
vectorStored id material (entry ∷ rest) proposed (here refl) = here refl
vectorStored id material (entry ∷ rest) proposed (there found) =
  there (vectorStored id material rest proposed found)

sourceStored : ∀ id material materials proposed → (id , material) ∈ materials →
  sourceRow (id , material) ∈ Store.World.grounds (publish materials proposed)
sourceStored id material (entry ∷ rest) proposed (here refl) = here refl
sourceStored id material (entry ∷ rest) proposed (there found) =
  there (sourceStored id material rest proposed found)

```

## What the proof guarantees

For any proposed belief that was absent before the review, the proof
finds the prepared vector and zero-weight source link in the published
store. The preparation contract limits new materials to beliefs being
created. On an unchanged retry of a completed review, Rust returns the
existing candidate IDs without embedding or publishing those beliefs
again. A correction that introduces a genuinely new belief still
requires preparation.

[PostgreSQL checks for stale revisions and retry](../../crates/core/src/store/conformance.rs#L391)

```agda
allNewBeliefsPrepared : ∀ before proposed materials → Complete before proposed materials →
  ∀ belief → belief ∈ Store.beliefs proposed →
  Ranking.lookup (Graph.BeliefValues.identity belief) (Store.beliefs before) ≡ nothing →
  Σ Belief.Prepared (λ material →
    vectorRow (Graph.BeliefValues.identity belief , material) ∈ Store.World.beliefVectors (publish materials proposed) ×
    sourceRow (Graph.BeliefValues.identity belief , material) ∈ Store.World.grounds (publish materials proposed))
allNewBeliefsPrepared before proposed materials complete belief present absent
  with Complete.coversNew complete belief present absent
... | material , found = material ,
  vectorStored _ material materials proposed found , sourceStored _ material materials proposed found

beliefValuesUnchanged : ∀ materials proposed → Store.nodes (publish materials proposed) ≡ Store.nodes proposed
beliefValuesUnchanged materials proposed = refl
```

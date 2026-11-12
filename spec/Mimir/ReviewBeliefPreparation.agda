{-# OPTIONS --safe #-}
-- Review-created beliefs require the same prepared vector and indexed source
-- as independent beliefs. Preparation is private; publication changes all
-- required records together and does not invent evidence strength.
module Mimir.ReviewBeliefPreparation where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.UUIDGroups using (UUID)
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.RetrievalRanking as Ranking
import Mimir.BeliefEmbedding as Belief
import Mimir.DocumentStore as Documents

Material = UUID × Belief.Prepared

record Complete (before proposed : Store.World) (materials : List Material) : Set where
  field
    -- Every newly published belief has a nonempty vector and an indexed
    -- supporting passage. The external preparation boundary validates support.
    coversNew : ∀ belief → belief ∈ Store.beliefs proposed →
      Ranking.lookup (Graph.BeliefValues.identity belief) (Store.beliefs before) ≡ nothing →
      Σ Belief.Prepared (λ material → (Graph.BeliefValues.identity belief , material) ∈ materials)
    onlyNew : ∀ id material → (id , material) ∈ materials →
      Ranking.lookup id (Store.beliefs before) ≡ nothing
    belongsToProposal : ∀ id material → (id , material) ∈ materials →
      Σ Graph.BeliefValues (λ belief → belief ∈ Store.beliefs proposed ×
        Graph.BeliefValues.identity belief ≡ id)
    supportIndexed : ∀ id material → (id , material) ∈ materials →
      Belief.Prepared.supportingPassage material ∈ Store.World.chunks before

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

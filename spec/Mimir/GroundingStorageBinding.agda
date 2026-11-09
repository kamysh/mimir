{-# OPTIONS --safe #-}
-- Automatic grounding searches the selected physical vector table. Similarity
-- is 1 - cosine distance, and each selected identity is looked up separately.
module Mimir.GroundingStorageBinding where

open import Data.Float.Base using (Float; _-_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.ApplicationStore as Store
import Mimir.GroundingProtocol as Ground
import Mimir.StorageReadBinding as Reads
import Mimir.StorageSemantics as Semantics
import Mimir.PosteriorComputation as Posterior
import Mimir.RetrievalRanking as Ranking
import Mimir.DatabaseReadCommitted as Committed
open import Mimir.Text using (Text)

module Bound (database : ℕ) (calculator : Posterior.Calculator) (ops : Reads.VectorOperations) (reads : Committed.Contract Store.World) where
  private
    module R = Reads.Vectors ops
    module S = Semantics.Bound database calculator
    module C = Committed.Contract reads

  similarity : Store.Vector → ℕ × Store.Vector → ℕ × Float
  similarity query row = proj₁ row , 1.0 - Reads.VectorOperations.cosineDistance ops query (proj₂ row)

  data Receipt : (effect : Ground.Effect) → Ground.Reply effect → Set where
    chunks : ∀ query limit observation ids →
      (selection : R.Selected query limit nothing (Store.World.chunkVectors (C.snapshot observation)) ids) →
      Receipt (Ground.searchChunks query limit)
        (inj₂ (map (similarity query) (Ranking.cap limit (R.Selected.sorted selection))))
    beliefs : ∀ query limit observation ids →
      (selection : R.Selected query limit nothing (Store.World.beliefVectors (C.snapshot observation)) ids) →
      Receipt (Ground.searchBeliefs query limit)
        (inj₂ (map (similarity query) (Ranking.cap limit (R.Selected.sorted selection))))
    chunk : ∀ id observation → Receipt (Ground.getChunk id)
      (inj₂ (Store.chunk id (Store.World.chunks (C.snapshot observation))))
    belief : ∀ id observation → Receipt (Ground.getBelief id)
      (inj₂ (Ranking.lookup id (Store.beliefs (C.snapshot observation))))
    added : ∀ chunk belief weight → S.GroundSuccess chunk belief weight → Receipt (Ground.addGround chunk belief weight) (inj₂ tt)
    chunkSearchFailed : ∀ query limit error → Receipt (Ground.searchChunks query limit) (inj₁ error)
    beliefSearchFailed : ∀ query limit error → Receipt (Ground.searchBeliefs query limit) (inj₁ error)
    chunkFailed : ∀ id error → Receipt (Ground.getChunk id) (inj₁ error)
    beliefFailed : ∀ id error → Receipt (Ground.getBelief id) (inj₁ error)
    addFailed : ∀ chunk belief weight error → Receipt (Ground.addGround chunk belief weight) (inj₁ error)


{-# OPTIONS --safe #-}
-- Re-embedding prepares the whole current missing-vector selection privately
-- and publishes it once. It never saves partial progress for a later run.
module Mimir.Reembedding where

open import Data.Bool using (Bool; not)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ; length)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.UUIDGroups using (UUID)
open import Mimir.Text using (Text)
import Data.String
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.RetrievalRanking as Ranking
import Mimir.DatabaseTransaction as DB
import Mimir.Recovery as Recovery

missing : Store.World → List UUID
missing before = Ranking.unique (map Graph.BeliefValues.identity
  (filterᵇ (λ belief → not (Ranking.member (Graph.BeliefValues.identity belief)
    (map proj₁ (Store.World.beliefVectors before)))) (Store.beliefs before)))

-- The indexing is association, not numeric identity or UUID order. Every
-- selected belief has exactly its own nonempty prepared vector.
data PreparedVectors : List UUID → Set where
  none : PreparedVectors []
  prepared : ∀ id ids → Float → List Float → PreparedVectors ids → PreparedVectors (id ∷ ids)

rows : ∀ {ids} → PreparedVectors ids → List (UUID × Store.Vector)
rows none = []
rows (prepared id ids first rest remaining) = (id , first ∷ rest) ∷ rows remaining

preparedKeysMatch : ∀ ids (material : PreparedVectors ids) → map proj₁ (rows material) ≡ ids
preparedKeysMatch [] none = refl
preparedKeysMatch (id ∷ ids) (prepared .id .ids first rest remaining)
  rewrite preparedKeysMatch ids remaining = refl

data Preparation : Set where
  needsInput : Text → Text → Preparation
  ready : ∀ ids → PreparedVectors ids → Preparation

data Result : Set where
  reembedded : ℕ → Result
  needsDecision : Text → Text → Result

SameSelection : List UUID → Store.World → Set
SameSelection selected before = ∀ id → Ranking.member id selected ≡ Ranking.member id (missing before)

publish : ∀ {ids} → PreparedVectors ids → Store.World → Store.World
publish material before = record before { beliefVectors = rows material ++ Store.World.beliefVectors before }

beliefValuesUnchanged : ∀ ids (material : PreparedVectors ids) before →
  Store.nodes (publish material before) ≡ Store.nodes before
beliefValuesUnchanged ids material before = refl

module Operation (ids : List UUID) (material : PreparedVectors ids) where
  Reply = Text ⊎ DB.Receipt

  answer : Reply → Result
  answer (inj₁ reason) = needsDecision reason
    (Data.String.toList "No prepared vectors were published. Resolve the reported prerequisite and retry re-embedding from the beginning.")
  answer (inj₂ DB.aborted) = needsDecision
    (Data.String.toList "Re-embedding was rolled back; no prepared vectors were published.")
    (Data.String.toList "Check whether the selection or its ownership changed, resolve the reported prerequisite, and retry the command from the beginning.")
  answer (inj₂ DB.committed) = reembedded (length ids)

  Successful : Result → Set
  Successful (reembedded _) = ⊤
  Successful (needsDecision _ _) = ⊥

  Atomic : Store.World → ⊤ → Reply → Store.World → Set
  Atomic before tt (inj₁ _) after = after ≡ before
  Atomic before tt (inj₂ DB.aborted) after = after ≡ before
  Atomic before tt (inj₂ DB.committed) after = SameSelection ids before ×
    DB.Atomic before (publish material before) DB.committed after

  module R = Recovery Store.World ⊤ Result (λ _ → ⊤) (λ _ → Reply) Atomic
    (λ before after → after ≡ before) (λ _ _ → Store.World)
    (λ _ _ after → after) (λ _ after → after) Successful (λ _ → ⊤)

  succeeds : ∀ before reply after → Atomic before tt reply after →
    Successful (answer reply) → after ≡ publish material before
  succeeds before (inj₁ _) after receipt ()
  succeeds before (inj₂ DB.aborted) after receipt ()
  succeeds before (inj₂ DB.committed) after (selected , DB.committedAll) confirmed = refl

  failsUnchanged : ∀ before reply after → Atomic before tt reply after →
    ¬ Successful (answer reply) → after ≡ before
  failsUnchanged before (inj₁ _) after unchanged _ = unchanged
  failsUnchanged before (inj₂ DB.aborted) after unchanged _ = unchanged
  failsUnchanged before (inj₂ DB.committed) after receipt impossible = ⊥-elim (impossible tt)

  call : R.FinalCall ⊤
  call = record
    { effect = λ _ → tt ; answer = λ _ → answer
    ; expected = λ _ before _ → publish material before
    ; success = λ _ before reply after receipt confirmed _ → succeeds before reply after receipt confirmed
    ; failureUnchanged = λ _ → failsUnchanged
    ; crashUnchanged = λ _ _ unchanged → unchanged
    }
  module Proof = R.FinalPublication call
  recovery : R.Recoverable ⊤
  recovery = Proof.finalPublication

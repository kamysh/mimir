{-# OPTIONS --safe #-}
-- Automatic grounding uses all returned similarities, threshold .80 and
-- project compatibility. Each accepted pair
-- invokes GroundingPublication; a later failure retains prior committed pairs.
module Mimir.GroundingProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.CandidateGraph as Graph
import Mimir.GraphNumerics as N
import Mimir.Effects as Effects
import Mimir.RetrievalRanking as Ranking

compatible : Maybe Text → Maybe Text → Bool
compatible nothing actual = true
compatible (just wanted) nothing = true
compatible (just wanted) (just actual) = does (wanted ≟Text actual)

data Effect : Set where
  searchChunks searchBeliefs : Store.Vector → Ranking.Selection → Effect
  getChunk : ℕ → Effect
  getBelief : ℕ → Effect
  addGround : ℕ → ℕ → Float → Effect

Reply : Effect → Set
Reply (searchChunks vector limit) = Text ⊎ List (ℕ × Float)
Reply (searchBeliefs vector limit) = Text ⊎ List (ℕ × Float)
Reply (getChunk id) = Text ⊎ Maybe Documents.Chunk
Reply (getBelief id) = Text ⊎ Maybe Graph.BeliefValues
Reply (addGround chunk belief weight) = Text ⊎ ⊤

module E = Effects.Protocol Effect Reply
open E

data Result : Set where success invalidSimilarity : Result; failed : Text → Result

read : (effect : Effect) → ∀ {A} → Reply effect ≡ (Text ⊎ A) → (A → Script Result) → Script Result
read effect {A} same next = ask effect (λ response → receive (subst (λ X → X) same response))
  where
  receive : Text ⊎ A → Script Result
  receive (inj₁ error) = done (failed error)
  receive (inj₂ value) = next value

add : ℕ → ℕ → Float → Script Result → Script Result
add chunk belief weight next with N.probability weight
... | false = done invalidSimilarity
... | true = read (addGround chunk belief weight) refl (λ _ → next)

mutual
  beliefCandidates : Graph.BeliefValues → List (ℕ × Float) → Script Result
  beliefCandidates belief [] = done success
  beliefCandidates belief ((id , similarity) ∷ rest) with similarity <ᵇ 0.80
  ... | true = done success
  ... | false = read (getChunk id) refl (beliefChunk belief similarity rest)

  beliefChunk : Graph.BeliefValues → Float → List (ℕ × Float) → Maybe Documents.Chunk → Script Result
  beliefChunk belief similarity rest nothing = beliefCandidates belief rest
  beliefChunk belief similarity rest (just chunk) with compatible (Graph.BeliefValues.project belief) (Documents.Chunk.project chunk)
  ... | false = beliefCandidates belief rest
  ... | true = add (Documents.Chunk.identity chunk) (Graph.BeliefValues.identity belief) similarity (beliefCandidates belief rest)

groundBelief : Graph.BeliefValues → Store.Vector → Script Result
groundBelief belief vector = read (searchChunks vector nothing) refl (beliefCandidates belief)

mutual
  chunkCandidates : Documents.Chunk → List (ℕ × Float) → Script Result → Script Result
  chunkCandidates chunk [] next = next
  chunkCandidates chunk ((id , similarity) ∷ rest) next with similarity <ᵇ 0.80
  ... | true = next
  ... | false = read (getBelief id) refl (chunkBelief chunk similarity rest next)

  chunkBelief : Documents.Chunk → Float → List (ℕ × Float) → Script Result → Maybe Graph.BeliefValues → Script Result
  chunkBelief chunk similarity rest next nothing = chunkCandidates chunk rest next
  chunkBelief chunk similarity rest next (just belief) with compatible (Documents.Chunk.project chunk) (Graph.BeliefValues.project belief)
  ... | false = chunkCandidates chunk rest next
  ... | true = add (Documents.Chunk.identity chunk) (Graph.BeliefValues.identity belief) similarity (chunkCandidates chunk rest next)

groundChunks : List (Documents.Chunk × Store.Vector) → Script Result
groundChunks [] = done success
groundChunks ((chunk , vector) ∷ rest) = read (searchBeliefs vector nothing) refl
  (λ candidates → chunkCandidates chunk candidates (groundChunks rest))

globalCompatible : ∀ project → compatible project nothing ≡ true
globalCompatible nothing = refl
globalCompatible (just project) = refl

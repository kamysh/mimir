{-# OPTIONS --safe #-}
-- Insertion, optional embedding and grounding are ordered operations, not one
-- transaction. A later error cannot retract a previously acknowledged write.
-- Reembedding skips the initial snapshot of existing vectors and never grounds.
module Mimir.BeliefEmbedding where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.CandidateGraph as G
import Mimir.ApplicationStore as Store
import Mimir.IndependentProvenance as Origin
import Mimir.GroundingProtocol as Grounding
import Mimir.RetrievalRanking as Ranking
import Mimir.RetrievalProtocol as Retrieval
import Mimir.Effects as Effects

data Effect : Set where
  insert : G.BeliefValues → Maybe Origin.Provenance → Effect
  embed : Text → Effect
  upsert : ℕ → Store.Vector → Effect
  grounding : Grounding.Effect → Effect
  listBeliefs embeddedIDs : Effect
  progress : G.BeliefValues → Effect

Reply : Effect → Set
Reply (insert b origin) = Text ⊎ ⊤
Reply (embed content) = Text ⊎ List Store.Vector
Reply (upsert id vector) = Text ⊎ ⊤
Reply (grounding effect) = Grounding.Reply effect
Reply listBeliefs = Text ⊎ List G.BeliefValues
Reply embeddedIDs = Text ⊎ List ℕ
Reply (progress b) = Text ⊎ ⊤

module E = Effects.Protocol Effect Reply
open E

data Failure : Set where
  nativeFailure : Text → Failure
  groundingFailure : Grounding.Result → Failure

Result = Failure ⊎ ⊤

liftGrounding : Grounding.E.Script Grounding.Result → Script Grounding.Result
liftGrounding (Grounding.E.done result) = done result
liftGrounding (Grounding.E.ask effect next) = ask (grounding effect) (λ reply → liftGrounding (next reply))

finishGrounding : Grounding.Result → Script Result
finishGrounding Grounding.success = done (inj₂ tt)
finishGrounding result = done (inj₁ (groundingFailure result))

afterUpsert : Bool → G.BeliefValues → Store.Vector → Text ⊎ ⊤ → Script Result
afterUpsert ground b vector (inj₁ error) = done (inj₁ (nativeFailure error))
afterUpsert false b vector (inj₂ tt) = done (inj₂ tt)
afterUpsert true b vector (inj₂ tt) = liftGrounding (Grounding.groundBelief b vector) >>= finishGrounding

afterEmbed : Bool → G.BeliefValues → Text ⊎ List Store.Vector → Script Result
afterEmbed ground b (inj₁ error) = done (inj₁ (nativeFailure error))
afterEmbed ground b (inj₂ vectors) with Retrieval.last vectors
... | nothing = done (inj₂ tt)
... | just vector = ask (upsert (G.BeliefValues.identity b) vector) (afterUpsert ground b vector)

embedBelief : Bool → Bool → G.BeliefValues → Script Result
embedBelief false ground b = done (inj₂ tt)
embedBelief true ground b = ask (embed (G.BeliefValues.content b)) (afterEmbed ground b)

start : Bool → G.BeliefValues → Maybe Origin.Provenance → Script Result
start enabled b origin = ask (insert b origin) (λ
  { (inj₁ error) → done (inj₁ (nativeFailure error))
  ; (inj₂ tt) → embedBelief enabled true b })

record Counts : Set where
  constructor counts
  field embedded skipped : ℕ

data Backfill : Set where
  disabled : Backfill
  complete : Counts → Backfill
  interrupted : Counts → Failure → Backfill

mutual
  backfill : List ℕ → List G.BeliefValues → Counts → Script Backfill
  backfill ids [] count = done (complete count)
  backfill ids (b ∷ rest) count with Ranking.member (G.BeliefValues.identity b) ids
  ... | true = backfill ids rest (record count { skipped = suc (Counts.skipped count) })
  ... | false = embedBelief true false b >>= afterBackfill ids b rest count

  afterBackfill : List ℕ → G.BeliefValues → List G.BeliefValues → Counts → Result → Script Backfill
  afterBackfill ids b rest count (inj₁ error) = done (interrupted count error)
  afterBackfill ids b rest count (inj₂ tt) = ask (progress b) (λ
    { (inj₁ error) → done (interrupted next (nativeFailure error))
    ; (inj₂ tt) → backfill ids rest next })
    where next = record count { embedded = suc (Counts.embedded count) }

afterList : Text ⊎ List G.BeliefValues → Script Backfill
afterList (inj₁ error) = done (interrupted (counts 0 0) (nativeFailure error))
afterList (inj₂ []) = done (complete (counts 0 0))
afterList (inj₂ beliefs@(_ ∷ _)) = ask embeddedIDs (λ
  { (inj₁ error) → done (interrupted (counts 0 0) (nativeFailure error))
  ; (inj₂ ids) → backfill ids beliefs (counts 0 0) })

reembed : Bool → Script Backfill
reembed false = done disabled
reembed true = ask listBeliefs afterList

disabledEmbeddingHasNoEffects : ∀ ground b → embedBelief false ground b ≡ done (inj₂ tt)
disabledEmbeddingHasNoEffects ground b = refl

-- The count is acknowledged embed calls, not proof of vector creation. An
-- empty backend result is a successful no-op in the present service contract.
emptyEmbeddingHasNoWrite : ∀ ground b → afterEmbed ground b (inj₂ []) ≡ done (inj₂ tt)
emptyEmbeddingHasNoWrite ground b = refl

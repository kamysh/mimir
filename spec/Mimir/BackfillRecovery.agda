{-# OPTIONS --safe #-}
-- A backfill keeps its original source selection and truthful original counts.
-- Preparation is observed work; no caller supplies an expected vector/result.
module Mimir.BackfillRecovery where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; map; filterᵇ; length)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as Maybes
open import Data.Nat using (ℕ; _≤?_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.BeliefEmbedding as Backfill
import Mimir.CandidateGraph as Graph
import Mimir.EmbeddingLifecycle as Lifecycle
import Mimir.PublicEncoding as Encoding
import Mimir.RetrievalRanking as Ranking
import Mimir.StructuredValue as Wire

record Source : Set where
  constructor source
  field
    identity : ℕ
    content : Text
    project : Maybe Text
    alreadyEmbedded : Bool

before : Graph.BeliefValues → Graph.BeliefValues → Bool
before first second = does (Graph.BeliefValues.identity first ≤? Graph.BeliefValues.identity second)

capture : Store.World → List Source
capture snapshot = map fromBelief (Ranking.sort before (Store.beliefs snapshot))
  where
  fromBelief : Graph.BeliefValues → Source
  fromBelief belief = source (Graph.BeliefValues.identity belief)
    (Graph.BeliefValues.content belief) (Graph.BeliefValues.project belief)
    (Ranking.member (Graph.BeliefValues.identity belief)
      (map proj₁ (Store.World.beliefVectors snapshot)))

pending : List Source → List Source
pending = filterᵇ (λ item → not (Source.alreadyEmbedded item))

initiallySkipped : List Source → ℕ
initiallySkipped rows = length (filterᵇ Source.alreadyEmbedded rows)

module Encode (format : Encoding.Formatting) where
  module E = Encoding.Encode format

  row : Source → Wire.Value
  row item = Encoding.object
    (("id" , E.uuid (Source.identity item)) ∷
     ("content" , Wire.string (Source.content item)) ∷
     ("project" , Encoding.optional Wire.string (Source.project item)) ∷
     ("already_embedded" , Wire.boolean (Source.alreadyEmbedded item)) ∷ [])

  snapshot : List Source → Wire.Value
  snapshot rows = Encoding.object (("beliefs" , Wire.array (map row rows)) ∷ [])

-- These are observations, not a choice to overwrite, skip or cancel. The
-- operation must separately apply the agreed policy to each observed state.
data Current : Set where
  missing changed alreadyPresent pendingVector : Current

current : Source → Store.World → Current
current expected snapshot with Ranking.lookup (Source.identity expected) (Store.beliefs snapshot)
... | nothing = missing
... | just belief with does (Source.content expected ≟Text Graph.BeliefValues.content belief) ∧
  does (Maybes.≡-dec _≟Text_ (Source.project expected) (Graph.BeliefValues.project belief))
... | false = changed
... | true with Ranking.member (Source.identity expected) (map proj₁ (Store.World.beliefVectors snapshot))
... | true = alreadyPresent
... | false = pendingVector

active : ℕ → Graph.BeliefValues → Store.World → Bool
active token belief snapshot with Store.lookupCancellation snapshot token
... | just _ = false
... | nothing = Backfill.ownsBackfill belief snapshot

checkedOwnership : ℕ → Graph.BeliefValues → Store.World → Lifecycle.Ownership.State → Lifecycle.Ownership.State
checkedOwnership token belief snapshot owned with active token belief snapshot
... | true = owned
... | false = Lifecycle.Ownership.stop owned

cancelledOperationStopsItsJob : ∀ token belief snapshot owned cancelled →
  Store.lookupCancellation snapshot token ≡ just cancelled →
  checkedOwnership token belief snapshot owned ≡ Lifecycle.Ownership.stop owned
cancelledOperationStopsItsJob token belief snapshot owned cancelled recorded rewrite recorded = refl

{-# OPTIONS --safe #-}
-- Concrete revision storage is bounded by signed i64. The abstract revision
-- laws remain arithmetic laws; this adapter proves that admitted writes fit.
module Mimir.RevisionBounds where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _<_; _<?_; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.LearningContracts as Contracts

i64Maximum : ℕ
i64Maximum = 9223372036854775807

module Limited (Payload : Set) (same : DecidableEquality Payload) (maximum : ℕ) where
  module R = Contracts.Revision Payload same
  open R.Cell

  Bounds : R.Cell → Set
  Bounds s = current s ≤ maximum × review s ≤ maximum

  record Cell : Set where
    constructor boundedCell
    field state : R.Cell; bounds : Bounds state

  preservesBounds : ∀ s owner source expected payload valid after →
    Bounds s → expected < maximum →
    R.submit s owner source expected payload valid ≡ just after → Bounds after
  preservesBounds s owner source expected payload valid after bounds expectedBound result
    with owner ≟Text project s | source ≟ current s
  ... | no _ | _ with result
  ...   | ()
  preservesBounds s owner source expected payload valid after bounds expectedBound result | yes _ | no _ with result
  ... | ()
  preservesBounds s owner source expected payload valid after bounds expectedBound result | yes _ | yes _
    with R.replay s expected payload
  ... | true with result
  ...   | refl = bounds
  preservesBounds s owner source expected payload valid after bounds expectedBound result | yes _ | yes _ | false
    with expected ≟ review s | valid
  ... | no _ | _ with result
  ...   | ()
  preservesBounds s owner source expected payload valid after bounds expectedBound result | yes _ | yes _ | false | yes _ | false with result
  ... | ()
  preservesBounds s owner source .(review s) payload valid after bounds expectedBound result | yes _ | yes _ | false | yes refl | true with result
  ... | refl = proj₁ bounds , expectedBound

  submit : Cell → Text → ℕ → ℕ → Payload → Bool → Maybe Cell
  submit (boundedCell s bounds) owner source expected payload valid with expected <? maximum
  ... | no _ = nothing
  ... | yes expectedBound with R.submit s owner source expected payload valid in result
  ...   | nothing = nothing
  ...   | just after = just (boundedCell after
    (preservesBounds s owner source expected payload valid after bounds expectedBound result))

  acceptedRevisionsFit : ∀ (s : Cell) → current (Cell.state s) ≤ maximum × review (Cell.state s) ≤ maximum
  acceptedRevisionsFit = Cell.bounds

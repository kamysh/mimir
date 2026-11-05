{-# OPTIONS --safe #-}
-- A total array/object visitor loop. Its child parser must prove progress on
-- success, so termination follows from consumed input rather than a task cap.
module Mimir.JsonCollection where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s⁻¹)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.JsonControls as Controls
import Mimir.NumericTokens
import Mimir.JsonFlow as Flow
module F = Flow.F

record Control : Set where
  constructor collectionControl
  field
    next : Bool → ∀ input → Controls.C.Result Bool input
    emptyCode : Controls.Code
    empty : ∀ first → next first [] ≡ Controls.C.failure emptyCode [] [] refl

arrayControl : Control
arrayControl = collectionControl Controls.arrayNext (Controls.eofList , Mimir.NumericTokens.peek) (λ first → refl)

objectControl : Control
objectControl = collectionControl Controls.objectNext (Controls.eofObject , Mimir.NumericTokens.peek) (λ first → refl)

childBound : ∀ fuel {input} (before : F.Cursor input) (after : F.Cursor (F.Cursor.remaining before)) →
  length input ≤ suc fuel → 1 ≤ length (F.Cursor.consumed after) → length (F.Cursor.remaining after) ≤ fuel
childBound fuel before after bounded progress = s≤s⁻¹
  (≤-trans (Flow.positiveRemaining after progress) (≤-trans (Flow.remainingBound before) bounded))

loop : ∀ {Value} → Control → Flow.Parser Value → ∀ fuel first input → length input ≤ fuel → Flow.Result (List Value) input
loop control child zero first [] bounded = Flow.lift (Controls.C.fail (Control.emptyCode control) [])
loop control child zero first (byte ∷ rest) ()
loop control child (suc fuel) first input bounded with Control.next control first input
... | Controls.C.failure code consumed remaining exact = Flow.lift (Controls.C.failure code consumed remaining exact)
... | Controls.C.success false consumed remaining exact = Flow.ordinary (F.success [] (F.cursor consumed remaining exact))
... | Controls.C.success true consumed remaining exact with child remaining
...   | Flow.productive (Flow.panicked position) progress = Flow.prefix (F.cursor consumed remaining exact) (Flow.panicked position)
...   | Flow.productive (Flow.ordinary (F.failure error)) progress = Flow.prefix (F.cursor consumed remaining exact) (Flow.ordinary (F.failure error))
...   | Flow.productive (Flow.ordinary (F.success value position)) progress =
      Flow.prefix (F.cursor consumed remaining exact) (Flow.prefix position (Flow.map (value ∷_)
        (loop control child fuel false (F.Cursor.remaining position)
          (childBound fuel (F.cursor consumed remaining exact) position bounded progress))))

run : ∀ {Value} → Control → Flow.Parser Value → ∀ input → Flow.Result (List Value) input
run control child input = loop control child (length input) true input ≤-refl

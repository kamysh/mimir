{-# OPTIONS --safe #-}
-- Positional records preserve supplied-reader and explicit-default predicates.
module Mimir.SerdePositionalInvariant where

open import Data.Bool using (true; false)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
import Data.Nat as Nat
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeSlotInvariant as I
import Mimir.SerdeSuccess as S
import Mimir.SerdeFlow as Flow
import Mimir.SerdePositional as Positional
import Mimir.JsonControls as Controls
module F = Flow.F
open Sequence using (Field)

prepend : ∀ entry fields (properties : I.Predicates (entry ∷ fields)) value input
  (result : Flow.Result (Slots.Values fields) input) → properties zero value →
  S.Ensures (I.Valid fields (λ index → properties (suc index))) result →
  S.Ensures (I.Valid (entry ∷ fields) properties) (Flow.map (value ,_) result)
prepend entry fields properties value input result valid tailValid =
  S.map (I.Valid fields (λ index → properties (suc index))) (I.Valid (entry ∷ fields) properties)
    (value ,_) (λ values tail → λ { zero → valid ; (suc index) → tail index }) result tailValid

read : ∀ fields readers (properties : I.Predicates fields) →
  (∀ index input → S.Ensures (properties index)
    (Flow.Productive.result (Slots.readerAt fields index readers input))) →
  I.Defaults fields properties → ∀ offset first input →
  S.Ensures (I.Valid fields properties) (Positional.read fields readers offset first input)
read [] readers properties readersValid defaults offset first input = λ ()
read (entry ∷ fields) (reader , readers) properties readersValid defaults offset first input
  with Controls.arrayNext first input
... | Controls.C.failure code consumed remaining exact = tt
... | Controls.C.success false consumed remaining exact with Field.missing entry in fallback
...   | nothing = tt
...   | just value = S.prefix (I.Valid (entry ∷ fields) properties) (F.cursor consumed remaining exact)
  (Flow.map (value ,_) (Positional.read fields readers (Nat.suc offset) first remaining))
  (prepend entry fields properties value remaining (Positional.read fields readers (Nat.suc offset) first remaining)
    (defaults zero value fallback)
    (read fields readers (λ index → properties (suc index)) (λ index → readersValid (suc index))
      (λ index → defaults (suc index)) (Nat.suc offset) first remaining))
read (entry ∷ fields) (reader , readers) properties readersValid defaults offset first input
  | Controls.C.success true consumed remaining exact =
  S.prefix (I.Valid (entry ∷ fields) properties) (F.cursor consumed remaining exact)
    (Flow.andThen (Flow.Productive.result (reader remaining))
      (λ value rest → Flow.map (value ,_) (Positional.read fields readers (Nat.suc offset) false rest)))
    (S.andThen (properties zero) (I.Valid (entry ∷ fields) properties) (Flow.Productive.result (reader remaining))
      (λ value rest → Flow.map (value ,_) (Positional.read fields readers (Nat.suc offset) false rest))
      (readersValid zero remaining)
      (λ value valid rest → prepend entry fields properties value rest
        (Positional.read fields readers (Nat.suc offset) false rest) valid
        (read fields readers (λ index → properties (suc index)) (λ index → readersValid (suc index))
          (λ index → defaults (suc index)) (Nat.suc offset) false rest)))

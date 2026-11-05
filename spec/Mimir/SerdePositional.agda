{-# OPTIONS --safe #-}
-- Raw positional struct visitor. Descriptors carry explicit serde defaults;
-- an Option without a default attribute would need a required descriptor here.
-- The caller runs array cleanup after this visitor returns or rejects.
module Mimir.SerdePositional where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeFlow as Flow
import Mimir.JsonControls as Controls
import Mimir.Validation as V
module F = Flow.F
open Sequence using (Field)

missing : ℕ → Field → V.Fault
missing offset entry = V.fault (V.index offset ∷ V.fieldKey (Field.name entry) ∷ []) V.malformedInput "missing positional field"

read : ∀ fields → Slots.Readers fields → ℕ → Bool → ∀ input → Flow.Result (Slots.Values fields) input
read [] readers offset first input = Flow.done tt input
read (entry ∷ fields) (reader , readers) offset first input with Controls.arrayNext first input
... | Controls.C.failure code consumed remaining exact = Flow.lift (Controls.C.failure code consumed remaining exact)
... | Controls.C.success false consumed remaining exact with Field.missing entry
...   | nothing = Flow.prefix (F.cursor consumed remaining exact) (Flow.reject (missing offset entry) remaining)
...   | just value = Flow.prefix (F.cursor consumed remaining exact)
    (Flow.map (value ,_) (read fields readers (suc offset) first remaining))
read (entry ∷ fields) (reader , readers) offset first input | Controls.C.success true consumed remaining exact =
  Flow.prefix (F.cursor consumed remaining exact)
    (Flow.andThen (Flow.Productive.result (reader remaining)) λ value rest →
      Flow.map (value ,_) (read fields readers (suc offset) false rest))

body : ∀ fields → Slots.Readers fields → ∀ input → Flow.Result (Slots.Values fields) input
body fields readers = read fields readers 0 true

missingStops : ∀ entry fields reader readers offset first input consumed remaining exact →
  Controls.arrayNext first input ≡ Controls.C.success false consumed remaining exact → Field.missing entry ≡ nothing →
  read (entry ∷ fields) (reader , readers) offset first input ≡
    Flow.prefix (F.cursor consumed remaining exact) (Flow.reject (missing offset entry) remaining)
missingStops entry fields reader readers offset first input consumed remaining exact absent required rewrite absent | required = refl

defaultWhenAbsent : ∀ entry fields reader readers offset first input consumed remaining exact value →
  Controls.arrayNext first input ≡ Controls.C.success false consumed remaining exact → Field.missing entry ≡ just value →
  read (entry ∷ fields) (reader , readers) offset first input ≡
    Flow.prefix (F.cursor consumed remaining exact) (Flow.map (value ,_) (read fields readers (suc offset) first remaining))
defaultWhenAbsent entry fields reader readers offset first input consumed remaining exact value absent fallback rewrite absent | fallback = refl

suppliedFailure : ∀ entry fields reader readers offset first input consumed remaining exact error →
  Controls.arrayNext first input ≡ Controls.C.success true consumed remaining exact →
  Flow.Productive.result (reader remaining) ≡ Flow.ordinary (F.failure error) →
  read (entry ∷ fields) (reader , readers) offset first input ≡
    Flow.prefix (F.cursor consumed remaining exact) (Flow.ordinary (F.failure error))
suppliedFailure entry fields reader readers offset first input consumed remaining exact error present failed rewrite present | failed = refl

suppliedPanic : ∀ entry fields reader readers offset first input consumed remaining exact position →
  Controls.arrayNext first input ≡ Controls.C.success true consumed remaining exact →
  Flow.Productive.result (reader remaining) ≡ Flow.panicked position →
  read (entry ∷ fields) (reader , readers) offset first input ≡ Flow.panicked (F.append (F.cursor consumed remaining exact) position)
suppliedPanic entry fields reader readers offset first input consumed remaining exact position present panicked rewrite present | panicked = refl

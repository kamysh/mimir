{-# OPTIONS --safe #-}
-- Native arithmetic panic is not a syntax-error message. Every ordinary
-- parser diagnostic must carry a describable reason, preserved by cleanup.
module Mimir.JsonDiagnosticCode where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)
import Mimir.JsonFlow as Flow
import Mimir.JsonControls as Controls
import Mimir.JsonErrorDisplay as Display
import Mimir.NumericTokens as Numeric
module F = Flow.F

CodeSafe : Controls.Code → Set
CodeSafe (reason , position) = reason ≢ Controls.numericError Numeric.arithmeticPanic

Atomic : ∀ {Value input} → Controls.C.Result Value input → Set
Atomic (Controls.C.success value before rest exact) = ⊤
Atomic (Controls.C.failure code before rest exact) = CodeSafe code

Rejection : ∀ {input} → F.Rejected input → Set
Rejection failure = CodeSafe (F.Fault.code (F.Rejected.firstError failure))

Safe : ∀ {Value input} → Flow.Result Value input → Set
Safe (Flow.panicked position) = ⊤
Safe (Flow.ordinary (F.success value position)) = ⊤
Safe (Flow.ordinary (F.failure failure)) = Rejection failure

atomicPrefix : ∀ {Value input} bytes (result : Controls.C.Result Value input) → Atomic result → Atomic (Controls.C.prefix bytes result)
atomicPrefix bytes (Controls.C.success value before rest exact) checked = tt
atomicPrefix bytes (Controls.C.failure code before rest exact) checked = checked

atomicReframe : ∀ {Value input other} (exact : input ≡ other) (result : Controls.C.Result Value other) →
  Atomic result → Atomic (Controls.C.reframe exact result)
atomicReframe refl result checked = checked

lift : ∀ {Value input} (result : Controls.C.Result Value input) → Atomic result → Safe (Flow.lift result)
lift (Controls.C.success value before rest exact) checked = tt
lift (Controls.C.failure code before rest exact) checked = checked

prefixRejection : ∀ {input} before (failure : F.Rejected (F.Cursor.remaining {input} before)) →
  Rejection failure → Rejection (F.prefixRejected before failure)
prefixRejection before (F.rejected (F.fault code position) cleanup) checked = checked

extendRejection : ∀ {input} (failure : F.Rejected input) cleanup → Rejection failure → Rejection (F.extendRejected failure cleanup)
extendRejection (F.rejected (F.fault code position) oldCleanup) cleanup checked = checked

prefix : ∀ {Value input} before (result : Flow.Result Value (F.Cursor.remaining {input} before)) →
  Safe result → Safe (Flow.prefix before result)
prefix before (Flow.panicked position) checked = tt
prefix before (Flow.ordinary (F.success value after)) checked = tt
prefix before (Flow.ordinary (F.failure failure)) checked = prefixRejection before failure checked

map : ∀ {A B input} (change : A → B) (result : Flow.Result A input) → Safe result → Safe (Flow.map change result)
map change (Flow.panicked position) checked = tt
map change (Flow.ordinary (F.success value position)) checked = tt
map change (Flow.ordinary (F.failure failure)) checked = checked

andThen : ∀ {A B input} (result : Flow.Result A input) next → Safe result →
  (∀ value rest → Safe (next value rest)) → Safe (Flow.andThen {Second = B} result next)
andThen (Flow.panicked position) next checked children = tt
andThen (Flow.ordinary (F.failure failure)) next checked children = checked
andThen (Flow.ordinary (F.success value before)) next checked children =
  prefix before (next value (F.Cursor.remaining before)) (children value (F.Cursor.remaining before))

finalize : ∀ {Value input} (result : Flow.Result Value input) finish → Safe result →
  (∀ rest → Atomic (finish rest)) → Safe (Flow.finalize result finish)
finalize (Flow.panicked position) finish checked children = tt
finalize (Flow.ordinary (F.failure failure)) finish checked children = extendRejection failure
  (F.current (F.lift (finish (F.Cursor.remaining (F.finalCursor failure))))) checked
finalize (Flow.ordinary (F.success value before)) finish checked children
  with finish (F.Cursor.remaining before) | children (F.Cursor.remaining before)
... | Controls.C.success unit consumed remaining exact | safe = tt
... | Controls.C.failure code consumed remaining exact | safe = safe

productiveMap : ∀ {A B input} (change : A → B) (result : Flow.Productive A input) →
  Safe (Flow.Productive.result result) → Safe (Flow.Productive.result (Flow.mapProductive change result))
productiveMap change (Flow.productive result progress) = map change result

productiveBind : ∀ {A B input} (result : Flow.Productive A input) next → Safe (Flow.Productive.result result) →
  (∀ value rest → Safe (next value rest)) → Safe (Flow.Productive.result (Flow.bindProductive {Second = B} result next))
productiveBind (Flow.productive result progress) next = andThen result next

messageAvailable : ∀ reason → reason ≢ Controls.numericError Numeric.arithmeticPanic →
  Σ Text (λ text → Display.message reason ≡ just text)
messageAvailable Controls.eofValue checked = _ , refl
messageAvailable Controls.eofList checked = _ , refl
messageAvailable Controls.eofObject checked = _ , refl
messageAvailable Controls.expectedIdent checked = _ , refl
messageAvailable Controls.expectedValue checked = _ , refl
messageAvailable Controls.expectedColon checked = _ , refl
messageAvailable Controls.expectedListCommaOrEnd checked = _ , refl
messageAvailable Controls.expectedObjectCommaOrEnd checked = _ , refl
messageAvailable Controls.keyString checked = _ , refl
messageAvailable Controls.trailingComma checked = _ , refl
messageAvailable Controls.trailingCharacters checked = _ , refl
messageAvailable Controls.recursionLimit checked = _ , refl
messageAvailable (Controls.stringError code) checked = _ , refl
messageAvailable (Controls.numericError Numeric.invalidNumber) checked = _ , refl
messageAvailable (Controls.numericError Numeric.eofValue) checked = _ , refl
messageAvailable (Controls.numericError Numeric.numberOutOfRange) checked = _ , refl
messageAvailable (Controls.numericError Numeric.arithmeticPanic) checked = ⊥-elim (checked refl)

renderAvailable : ∀ {input} (failure : F.Rejected input) → Rejection failure →
  Σ Text (λ text → Display.renderRejected failure ≡ just text)
renderAvailable (F.rejected (F.fault (reason , mode) origin) cleanup) checked with messageAvailable reason checked
... | text , described rewrite described = Display.atPosition text (Display.locate mode origin) , refl

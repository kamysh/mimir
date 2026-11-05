{-# OPTIONS --safe #-}
-- A typed parser's first error is independent of its later cleanup cursor.
module Mimir.SerdeFailure where

open import Data.List using (List; []; _++_)
open import Data.Maybe using (just)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.JsonControls as Controls

record Rejected {Value input} (result : Flow.Result Value input) (code : Flow.Code) (suffix : List Byte) : Set where
  constructor rejected
  field
    origin : Flow.F.Cursor input
    observed : Flow.firstError result ≡ just (Flow.F.fault code origin)
    remaining : Flow.F.Cursor.remaining origin ≡ suffix

neverReturned : ∀ {Value input code suffix value rest} (result : Flow.Result Value input) →
  Rejected result code suffix → Back.Returned result value rest → ⊥
neverReturned {value = value} .(Flow.ordinary (Flow.F.success value position))
  (rejected origin () remaining) (Back.returned position refl rest)

fromSyntax : ∀ {Value} input code consumed remaining exact →
  Rejected {Value} (Flow.lift (Controls.C.failure {input = input} code consumed remaining exact))
    (Flow.syntaxFault code) remaining
fromSyntax input code consumed remaining exact = rejected (Flow.F.cursor consumed remaining exact) refl refl

observedSyntax : ∀ {Value} input (result : Controls.C.Result Value input) code consumed remaining exact →
  result ≡ Controls.C.failure code consumed remaining exact →
  Rejected (Flow.lift result) (Flow.syntaxFault code) remaining
observedSyntax input result code consumed remaining exact observed = subst
  (λ parsed →
     Rejected (Flow.lift parsed) (Flow.syntaxFault code) remaining)
  (sym observed) (fromSyntax input code consumed remaining exact)

map : ∀ {First Second input code suffix} (change : First → Second) (result : Flow.Result First input) →
  Rejected result code suffix → Rejected (Flow.map change result) code suffix
map change (Flow.panicked position) (rejected origin () remaining)
map change (Flow.ordinary (Flow.F.success value position)) (rejected origin () remaining)
map change (Flow.ordinary (Flow.F.failure error)) (rejected origin observed remaining) = rejected origin observed remaining

prefix : ∀ {Value input code suffix} (before : Flow.F.Cursor input)
  (result : Flow.Result Value (Flow.F.Cursor.remaining before)) →
  Rejected result code suffix → Rejected (Flow.prefix before result) code suffix
prefix before (Flow.panicked position) (rejected origin () remaining)
prefix before (Flow.ordinary (Flow.F.success value position)) (rejected origin () remaining)
prefix before (Flow.ordinary (Flow.F.failure (Flow.F.rejected error cleanup)))
  (rejected origin refl remaining) = rejected (Flow.F.append before origin) refl remaining

andThen : ∀ {First Second input code suffix} (result : Flow.Result First input)
  (next : First → ∀ rest → Flow.Result Second rest) →
  Rejected result code suffix → Rejected (Flow.andThen result next) code suffix
andThen (Flow.panicked position) next (rejected origin () remaining)
andThen (Flow.ordinary (Flow.F.success value position)) next (rejected origin () remaining)
andThen (Flow.ordinary (Flow.F.failure error)) next (rejected origin observed remaining) = rejected origin observed remaining

afterSuccess : ∀ {First Second input first middle code suffix} (result : Flow.Result First input)
  (next : First → ∀ rest → Flow.Result Second rest) →
  Back.Returned result first middle → Rejected (next first middle) code suffix →
  Rejected (Flow.andThen result next) code suffix
afterSuccess result next (Back.returned position refl refl) receipt = prefix position _ receipt

finalize : ∀ {Value input code suffix} (result : Flow.Result Value input) finish →
  Rejected result code suffix → Rejected (Flow.finalize result finish) code suffix
finalize (Flow.panicked position) finish (rejected origin () remaining)
finalize (Flow.ordinary (Flow.F.success value position)) finish (rejected origin () remaining)
finalize (Flow.ordinary (Flow.F.failure error)) finish (rejected origin observed remaining) = rejected origin observed remaining

mapProductive : ∀ {First Second input code suffix} (change : First → Second)
  (parsed : Flow.Productive First input) → Rejected (Flow.Productive.result parsed) code suffix →
  Rejected (Flow.Productive.result (Flow.mapProductive change parsed)) code suffix
mapProductive change (Flow.productive result progress) receipt = map change result receipt

bindProductive : ∀ {First Second input code suffix} (parsed : Flow.Productive First input)
  (next : First → ∀ rest → Flow.Result Second rest) →
  Rejected (Flow.Productive.result parsed) code suffix →
  Rejected (Flow.Productive.result (Flow.bindProductive parsed next)) code suffix
bindProductive (Flow.productive result progress) next receipt = andThen result next receipt

afterProductive : ∀ {First Second input first middle code suffix}
  (parsed : Flow.Productive First input) (next : First → ∀ rest → Flow.Result Second rest) →
  Back.Returned (Flow.Productive.result parsed) first middle →
  Rejected (next first middle) code suffix →
  Rejected (Flow.Productive.result (Flow.bindProductive parsed next)) code suffix
afterProductive (Flow.productive result progress) next receipt rejectedNext = afterSuccess result next receipt rejectedNext

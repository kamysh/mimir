{-# OPTIONS --safe #-}
-- Successful read-back receipts compose through the modeled serde operations.
import Mimir.FloatConversion
module Mimir.SerdeReadBackComposition (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Sum using (_⊎_; inj₂)
open import Data.List using ([]; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.SerdeContainer as Container
import Mimir.JsonControls as Controls
import Mimir.Validation as V
import Mimir.SerdeScalar as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.JsonWhitespace as White

map : ∀ {First Second input} (change : First → Second) {result : Flow.Result First input} {value suffix} →
  Back.Returned result value suffix → Back.Returned (Flow.map change result) (change value) suffix
map change (Back.returned position refl remaining) = Back.returned position refl remaining

prefix : ∀ {Value input} (before : Flow.F.Cursor input)
  {result : Flow.Result Value (Flow.F.Cursor.remaining before)} {value suffix} →
  Back.Returned result value suffix → Back.Returned (Flow.prefix before result) value suffix
prefix before (Back.returned position refl remaining) = Back.returned (Flow.F.append before position) refl remaining

validate : ∀ {First Second input} (check : First → V.Fault ⊎ Second)
  (parsed : Flow.Productive First input) {value output suffix} →
  Back.Returned (Flow.Productive.result parsed) value suffix → check value ≡ inj₂ output →
  Back.Returned (Flow.Productive.result (Flow.validate check parsed)) output suffix
validate check (Flow.productive result progress) (Back.returned position refl remaining) admitted
  rewrite admitted = Back.returned
    (Flow.F.append position
     (Flow.F.initial (Flow.F.Cursor.remaining position)))
    refl remaining

noWhitespace : ∀ {Value} (child : Flow.Parser Value) byte rest {value suffix} →
  White.Stopped (byte ∷ rest) → Back.Returns child (byte ∷ rest) value suffix →
  Back.Returned (Flow.Productive.result (Scalar.whitespace (byte ∷ rest) child)) value suffix
noWhitespace child byte rest stopped receipt with White.space? byte
... | yes space = ⊥-elim (stopped space)
... | no notSpace with child (byte ∷ rest) | receipt
...   | Flow.productive result progress | evidence = prefix (Flow.F.initial (byte ∷ rest)) evidence

container : ∀ {Value} byte rest (finish : ∀ input → Controls.C.Result ⊤ input)
  {result : Flow.Result Value rest} {value middle} →
  Back.Returned result value middle → ∀ consumed suffix exact →
  finish middle ≡ Controls.C.success tt consumed suffix exact →
  Back.Returned (Flow.Productive.result (Container.enter byte rest result finish)) value suffix
container byte rest finish (Back.returned position refl refl) consumed suffix exact closed = Back.returned
  (Flow.F.append (Flow.F.cursor (byte ∷ []) rest refl)
   (Flow.F.append position (Flow.F.cursor consumed suffix exact)))
  (Container.successfulClose byte rest _ position finish consumed
   suffix exact closed)
  refl

-- A successful first parser transfers its exact remaining input to the next.
andThen : ∀ {First Second input} (result : Flow.Result First input)
  (next : First → ∀ rest → Flow.Result Second rest) {first middle value suffix} →
  Back.Returned result first middle → Back.Returned (next first middle) value suffix →
  Back.Returned (Flow.andThen result next) value suffix
andThen result next
  (Back.returned position refl refl) tail = prefix position tail

-- Keep productive-parser mapping abstract while composing large concrete readers.
mapProductive : ∀ {First Second input} (change : First → Second)
  (parsed : Flow.Productive First input) {value suffix} →
  Back.Returned (Flow.Productive.result parsed) value suffix →
  Back.Returned (Flow.Productive.result (Flow.mapProductive change parsed)) (change value) suffix
mapProductive change (Flow.productive result progress) receipt = map change receipt

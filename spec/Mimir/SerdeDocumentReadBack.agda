{-# OPTIONS --safe #-}
-- Successful child reads compose with the actual document completion check.
import Mimir.FloatConversion
module Mimir.SerdeDocumentReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([])
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.SerdeReadBackComposition as ComposeDependency
private
  module Compose = ComposeDependency floatConversion
import Mimir.SerdeDocument as DocumentDependency
private
  module Document = DocumentDependency floatConversion
import Mimir.SignedMachine as Machine

bindProductive : ∀ {First Second input} (parsed : Flow.Productive First input)
  (next : First → ∀ rest → Flow.Result Second rest) {first middle value suffix} →
  Back.Returned (Flow.Productive.result parsed) first middle →
  Back.Returned (next first middle) value suffix →
  Back.Returned (Flow.Productive.result (Flow.bindProductive parsed next)) value suffix
bindProductive (Flow.productive result progress) next head tail = Compose.andThen result next head tail

module Parser (checks : Machine.OverflowChecks) where
  private module D = Document.Parser checks

  finishEmpty : Back.Returned (D.finish []) tt []
  finishEmpty = Back.returned (Flow.F.initial []) refl refl

  completed : ∀ {Value} (child : Flow.Parser Value) input value middle →
    Back.Returns child input value middle → Back.Returned (D.finish middle) tt [] →
    Back.Returns (D.read child) input value []
  completed child input value middle receipt finished = bindProductive (child input)
    (λ parsed rest → Flow.map (λ unit → parsed) (D.finish rest))
    receipt (Compose.map (λ unit → value) finished)

  exhausted : ∀ {Value} (child : Flow.Parser Value) input value →
    Back.Returns child input value [] → Back.Returns (D.read child) input value []
  exhausted child input value receipt = completed child input value [] receipt finishEmpty

{-# OPTIONS --safe #-}
-- Complete-document validation preserves the child's successful value laws.
import Mimir.FloatConversion
module Mimir.SerdeDocumentInvariant (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Unit using (⊤)
import Mimir.SerdeDocument as DocumentDependency
private
  module Document = DocumentDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S
import Mimir.SignedMachine as Machine

module Parser (checks : Machine.OverflowChecks) where
  private
    module D = Document.Parser checks

  read : ∀ {Value} (child : Flow.Parser Value) (property : Value → Set) →
    (∀ input → S.Ensures property (Flow.Productive.result (child input))) →
    ∀ input → S.Ensures property (Flow.Productive.result (D.read child input))
  read child property valid input = S.andThen property property (Flow.Productive.result (child input))
    (λ First Second → Flow.map (λ input₁ → First) (D.finish Second))
    (valid input)
    (λ before after result →
       S.map (λ _ → ⊤) property (λ next → before) (λ value _ → after)
       (D.finish result) (S.trivial (D.finish result)))

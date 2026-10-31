{-# OPTIONS --safe #-}
-- Validation can rely on an invariant proved for the parsed input value.
module Mimir.SerdeValidateInvariant where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S
import Mimir.Validation as V

validate : ∀ {First Second input} (before : First → Set) (after : Second → Set)
  (check : First → V.Fault ⊎ Second) →
  (∀ value → before value → ∀ output → check value ≡ inj₂ output → after output) →
  (parsed : Flow.Productive First input) →
  S.Ensures before (Flow.Productive.result parsed) →
  S.Ensures after (Flow.Productive.result (Flow.validate check parsed))
validate before after check preserves (Flow.productive (Flow.ordinary (Flow.F.success value position)) progress) valid
  with check value in selected
... | inj₁ error = tt
... | inj₂ output = preserves value valid output selected
validate before after check preserves (Flow.productive (Flow.ordinary (Flow.F.failure error)) progress) valid = tt
validate before after check preserves (Flow.productive (Flow.panicked position) progress) valid = tt

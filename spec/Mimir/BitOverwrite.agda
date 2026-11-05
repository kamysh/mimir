{-# OPTIONS --safe #-}
-- Independent meaning of AND-then-OR masks, for all bits and word widths.
module Mimir.BitOverwrite where

open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Mimir.Bits using (Bit; Word; O; I)
import Mimir.BitLogic as Logic

select : Bit → Bit → Bit → Bit
select keep O value with keep
... | O = O
... | I = value
select keep I value = I

maskMeaning : ∀ value keep forced →
  Logic.or (Logic.and value keep) forced ≡ select keep forced value
maskMeaning O O O = refl
maskMeaning O O I = refl
maskMeaning O I O = refl
maskMeaning O I I = refl
maskMeaning I O O = refl
maskMeaning I O I = refl
maskMeaning I I O = refl
maskMeaning I I I = refl

overwrite : ∀ {width} → Word width → Word width → Word width → Word width
overwrite [] [] [] = []
overwrite (keep ∷ keeps) (forced ∷ forces) (value ∷ values) =
  select keep forced value ∷ overwrite keeps forces values

wordMaskMeaning : ∀ {width} (values keeps forces : Word width) →
  Logic.wordOr (Logic.wordAnd values keeps) forces ≡ overwrite keeps forces values
wordMaskMeaning [] [] [] = refl
wordMaskMeaning (value ∷ values) (keep ∷ keeps) (forced ∷ forces) = cong₂ _∷_ (maskMeaning value keep forced) (wordMaskMeaning values keeps forces)

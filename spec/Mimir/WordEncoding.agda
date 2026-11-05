{-# OPTIONS --safe #-}
module Mimir.WordEncoding where

open import Data.Nat using (ℕ; zero; suc; _%_; NonZero; nonZero)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import Mimir.Bits using (Word; module Binary)

powerPositive : ∀ width → NonZero (Binary.power width)
powerPositive zero = nonZero
powerPositive (suc width) with Binary.power width | powerPositive width
... | zero | record { nonZero = () }
... | suc n | proof = nonZero

encode : ∀ width → .{{nz : NonZero (Binary.power width)}} → ℕ → Word width
encode width number = Binary.Expansion.digits
  (Binary.encode width (number % Binary.power width) (m%n<n number (Binary.power width)))

value : ∀ width → .{{nz : NonZero (Binary.power width)}} → ∀ number →
  Binary.value (encode width number) ≡ number % Binary.power width
value width number = Binary.decodeEncode width (number % Binary.power width) (m%n<n number (Binary.power width))

roundTrip : ∀ {width} → .{{nz : NonZero (Binary.power width)}} → (word : Word width) → encode width (Binary.value word) ≡ word
roundTrip {width} word = Binary.valueInjective _ word
  (trans (value width (Binary.value word)) (m<n⇒m%n≡m (Binary.valueBound word)))

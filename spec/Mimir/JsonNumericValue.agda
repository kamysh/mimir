{-# OPTIONS --safe #-}
-- Exact connection between the parser's bounded number variants and schema
-- validation. No decimal conversion or floating recomputation occurs here.
module Mimir.JsonNumericValue where

open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (s≤s)
open import Data.Nat.Properties using (≤-irrelevant)
open import Data.Product using (_,_)
import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import Mimir.Binary64 as B
import Mimir.FloatValue as A
import Mimir.JsonTree as Parsed
import Mimir.StructuredValue as Schema
import Mimir.NumericTokens as Numeric
import Mimir.Unsigned as Unsigned

finite : B.Sign → A.Magnitude → B.FiniteNumber
finite = A.finiteValue

preservesSign : ∀ sign amount →
  B.Word.sign (B.FiniteNumber.word (finite sign amount)) ≡ sign
preservesSign sign amount = refl

decode : Parsed.ScalarNumber → Schema.Value
decode (Parsed.unsigned number) = Schema.unsigned (Unsigned.UInt.number number)
decode (Parsed.signed number) = Schema.signed (Numeric.I64.Integer.number number)
decode (Parsed.floating sign amount) = Schema.floating (B.finite (finite sign amount))

unsignedRange : ∀ number → Unsigned.UInt.number number Data.Nat.≤ B.powerMinusOne 64
unsignedRange = Unsigned.UInt.bounded

floatingIsFinite : ∀ sign amount → B.IsFinite (B.finite (finite sign amount))
floatingIsFinite sign amount = Data.Unit.tt

{-# OPTIONS --safe #-}
-- Null optionals and successful non-null child reads preserve their suffixes.
import Mimir.FloatConversion
module Mimir.SerdeOptionReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (#_)
open import Data.List using ([]; _∷_; _++_)
open import Data.Maybe using (nothing; just)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; subst; sym)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.SerdeReadBackComposition as ComposeDependency
private
  module Compose = ComposeDependency floatConversion
import Mimir.SerdeOption as OptionDependency
private
  module Option = OptionDependency floatConversion
import Mimir.JsonWhitespace as White

null : ∀ {Value} (child : Flow.Parser Value) suffix →
  Back.Returns (Option.read child) ((# 110) ∷ (# 117) ∷ (# 108) ∷ (# 108) ∷ suffix) nothing suffix
null child suffix = Back.returned
  (Flow.F.cursor ((# 110) ∷ (# 117) ∷ (# 108) ∷ (# 108) ∷ []) suffix refl) refl refl

dispatchSome : ∀ {Value} (child : Flow.Parser Value) byte rest value suffix → byte ≢ (# 110) →
  Back.Returns child (byte ∷ rest) value suffix →
  Back.Returns (Option.dispatch child) (byte ∷ rest) (just value) suffix
dispatchSome child byte rest value suffix notNull receipt =
  subst (λ parsed → Back.Returned (Flow.Productive.result parsed) (just value) suffix)
    (sym (Option.otherUsesChild child byte rest notNull)) (Compose.map just receipt)

some : ∀ {Value} (child : Flow.Parser Value) byte rest value suffix → byte ≢ (# 110) →
  White.Stopped (byte ∷ rest) → Back.Returns child (byte ∷ rest) value suffix →
  Back.Returns (Option.read child) (byte ∷ rest) (just value) suffix
some child byte rest value suffix notNull stopped receipt =
  Compose.noWhitespace (Option.dispatch child) byte rest stopped
    (dispatchSome child byte rest value suffix notNull receipt)

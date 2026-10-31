{-# OPTIONS --safe #-}
-- Optional values recognize null without invoking the child visitor. All
-- other inputs use that visitor at the same recursion allowance.
import Mimir.FloatConversion
module Mimir.SerdeOption (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([]; _∷_)
open import Data.Fin using (#_; _≟_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeScalar as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion

dispatch : ∀ {Value} → Flow.Parser Value → Flow.Parser (Maybe Value)
dispatch child [] = Flow.mapProductive just (child [])
dispatch child input@(byte ∷ rest) with byte ≟ (# 110)
... | yes isNull = Flow.fromJsonProductive (Atoms.literal nothing byte ((# 117) ∷ (# 108) ∷ (# 108) ∷ []) rest)
... | no notNull = Flow.mapProductive just (child input)

read : ∀ {Value} → Flow.Parser Value → Flow.Parser (Maybe Value)
read child input = Scalar.whitespace input (dispatch child)

nullBypassesChild : ∀ {Value} (first second : Flow.Parser Value) byte rest → byte ≡ (# 110) →
  dispatch first (byte ∷ rest) ≡ dispatch second (byte ∷ rest)
nullBypassesChild first second byte rest matched with byte ≟ (# 110)
... | yes same = refl
... | no different = ⊥-elim (different matched)

otherUsesChild : ∀ {Value} (child : Flow.Parser Value) byte rest → byte ≢ (# 110) →
  dispatch child (byte ∷ rest) ≡ Flow.mapProductive just (child (byte ∷ rest))
otherUsesChild child byte rest different with byte ≟ (# 110)
... | yes same = ⊥-elim (different same)
... | no unequal = refl

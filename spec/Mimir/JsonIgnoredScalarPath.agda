{-# OPTIONS --safe #-}
-- Scalars return to the same enclosing container stack, preserving the suffix.
import Mimir.FloatConversion
module Mimir.JsonIgnoredScalarPath (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import Mimir.ByteText as Wire
import Mimir.JsonIgnoredStep as StepDependency
private
  module Step = StepDependency floatConversion
import Mimir.JsonIgnoredPath as PathDependency
private
  module Path = PathDependency floatConversion
import Mimir.JsonIgnoredReadBack as IgnoredDependency
private
  module Ignored = IgnoredDependency floatConversion
import Mimir.JsonIgnoredString as String
import Mimir.JsonIgnoredNumber as Number
import Mimir.JsonIgnoredNumberReadBack as Character
import Mimir.JsonIgnoredNumberSyntax as Syntax
import Mimir.JsonIgnoredNumberWireReadBack as NumericDependency
private
  module Numeric = NumericDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
module C = Step.C

advance : ∀ frames input (result : C.Result ⊤ input) suffix →
  Back.Returned (Flow.lift result) tt suffix →
  Step.Step.result (Step.transition (Step.value frames) input) ≡
    C.prefix [] (Step.advance (Step.boundary frames true) result) →
  Path.Path (Step.value frames) input (Step.boundary frames true) suffix
advance frames input (C.failure code consumed remaining exact) suffix (Back.returned position () end) equation
advance frames input (C.success tt consumed remaining exact) suffix (Back.returned position refl end) equation = subst
  (Path.Path (Step.value frames) input (Step.boundary frames true))
  end
  (Path.next (Step.boundary frames true) consumed remaining _
   equation Path.stop)

null : ∀ frames suffix → Path.Path (Step.value frames)
  ((# 110) ∷ (# 117) ∷ (# 108) ∷ (# 108) ∷ suffix) (Step.boundary frames true) suffix
null frames suffix = Path.next (Step.boundary frames true)
  (# 110 ∷ # 117 ∷ # 108 ∷ # 108 ∷ []) suffix refl refl Path.stop

boolean : ∀ frames value suffix → Path.Path (Step.value frames)
  (Ignored.spelling value ++ suffix) (Step.boundary frames true) suffix
boolean frames true suffix = Path.next (Step.boundary frames true) (Ignored.spelling true)
  suffix refl refl Path.stop
boolean frames false suffix = Path.next (Step.boundary frames true) (Ignored.spelling false)
  suffix refl refl Path.stop

string : ∀ frames body → String.ValidBody body → ∀ suffix →
  Path.Path (Step.value frames) ((# 34) ∷ (String.spellBody body ++ suffix)) (Step.boundary frames true) suffix
string frames body valid suffix with String.readBodyComplete body valid suffix
... | String.parsed .body checked .suffix exact , observed , refl , refl = Path.next (Step.boundary frames true)
  (# 34 ∷ String.spellBody body) suffix _
  (cong
   (λ result →
      C.prefix []
      (Step.Step.result
       (Step.consume (Step.boundary frames true) (# 34) result)))
   (Ignored.stringBodyResult (String.parsed body checked suffix exact)
    observed))
  Path.stop

numeric : ∀ frames input suffix → Numeric.Starts input →
  Back.Returned (Flow.lift (Step.numberResult (Number.readBytes input))) tt suffix →
  Path.Path (Step.value frames) input (Step.boundary frames true) suffix
numeric frames .(byte ∷ rest) suffix (Numeric.starts byte rest refl valid) receipt = advance frames (byte ∷ rest)
  (Step.numberResult (Number.readBytes (byte ∷ rest))) suffix receipt
  (Numeric.dispatch frames byte rest valid)

number : ∀ frames input suffix value → Wire.text input ≡ Syntax.spell value (Wire.text suffix) →
  Character.Stopped (Wire.text suffix) →
  Path.Path (Step.value frames) input (Step.boundary frames true) suffix
number frames input suffix value spelling stopped = numeric frames input suffix
  (Numeric.syntaxStart input value (Wire.text suffix) spelling)
  (Numeric.complete input suffix value spelling stopped)

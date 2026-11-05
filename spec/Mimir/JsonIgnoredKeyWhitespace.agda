{-# OPTIONS --safe #-}
-- Object-key parsing permits exactly JSON whitespace before the colon.
import Mimir.FloatConversion
module Mimir.JsonIgnoredKeyWhitespace (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (#_)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Mimir.JsonIgnoredStep as StepDependency
private
  module Step = StepDependency floatConversion
import Mimir.JsonIgnoredPath as PathDependency
private
  module Path = PathDependency floatConversion
import Mimir.JsonIgnoredString as String
import Mimir.JsonIgnoredReadBack as IgnoredDependency
private
  module Ignored = IgnoredDependency floatConversion
import Mimir.JsonWhitespace as White
import Mimir.JsonControls as Controls
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
module C = Step.C

colon : ∀ before → All White.Space before → ∀ suffix →
  Back.Returned (Flow.lift (Controls.colon (before ++ ((# 58) ∷ suffix)))) tt suffix
colon before valid suffix with White.take (before ++ ((# 58) ∷ suffix))
  | White.complete before valid ((# 58) ∷ suffix) (λ ())
... | White.run .before spaces .((# 58) ∷ suffix) refl stopped | refl , refl = Back.returned _ refl refl

andThen : ∀ input (result : C.Result ⊤ input) (next : ∀ rest → C.Result ⊤ rest) middle suffix →
  Back.Returned (Flow.lift result) tt middle →
  Back.Returned (Flow.lift (next middle)) tt suffix →
  Back.Returned (Flow.lift (C.andThen result (λ unit rest → next rest))) tt suffix
andThen input (C.failure code consumed remaining exact) next middle suffix (Back.returned position () end) receipt
andThen input (C.success tt consumed remaining exact) next .remaining suffix (Back.returned position refl refl) receipt = Path.prefixSuccess consumed remaining exact (next remaining)
  receipt

body : ∀ text → String.ValidBody text → ∀ suffix →
  Back.Returned (Flow.lift (Step.stringBody (String.spellBody text ++ suffix))) tt suffix
body text valid suffix with String.readBodyComplete text valid suffix
... | String.parsed .text checked .suffix exact , observed , refl , refl = Back.returned (Flow.F.cursor (String.spellBody text) suffix exact)
  (cong Flow.lift
   (Ignored.stringBodyResult (String.parsed text checked suffix exact)
    observed))
  refl

key : ∀ frames text → String.ValidBody text → ∀ before → All White.Space before → ∀ suffix →
  Path.Path (Step.key frames)
    ((# 34) ∷ (String.spellBody text ++ (before ++ ((# 58) ∷ suffix)))) (Step.value frames) suffix
key frames text valid before spaces suffix = Path.fromResult (Step.key frames) (Step.value frames)
  (# 34 ∷ String.spellBody text ++ before ++ # 58 ∷ suffix)
  (C.prefix (# 34 ∷ [])
   (C.andThen
    (Step.stringBody
     (String.spellBody text ++ before ++ # 58 ∷ suffix))
    (λ unit rest → Controls.colon rest)))
  suffix
  (Path.prefixSuccess (# 34 ∷ [])
   (String.spellBody text ++ before ++ # 58 ∷ suffix) refl
   (C.andThen
    (Step.stringBody
     (String.spellBody text ++ before ++ # 58 ∷ suffix))
    (λ unit rest → Controls.colon rest))
   (andThen (String.spellBody text ++ before ++ # 58 ∷ suffix)
    (Step.stringBody
     (String.spellBody text ++ before ++ # 58 ∷ suffix))
    Controls.colon (before ++ # 58 ∷ suffix) suffix
    (body text valid (before ++ # 58 ∷ suffix))
    (colon before spaces suffix)))
  refl

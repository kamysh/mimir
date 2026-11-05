{-# OPTIONS --safe #-}
-- Successful ignored-value executions preserve the exact trailing input.
import Mimir.FloatConversion
module Mimir.JsonIgnoredReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Bits using (Byte)
import Mimir.JsonControls as Controls
import Mimir.JsonIgnoredStep as StepDependency
private
  module Step = StepDependency floatConversion
import Mimir.JsonIgnoredRun as RunDependency
private
  module Run = RunDependency floatConversion
import Mimir.JsonIgnoredString as String
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
module C = Controls.C

received : ∀ {input} consumed suffix exact →
  Run.Execution (Step.value []) input (C.success tt consumed suffix exact) →
  Back.Returned (Flow.lift (Run.read input)) tt suffix
received {input} consumed suffix exact executed = Back.returned (Flow.F.cursor consumed suffix exact)
  (cong Flow.lift
   (Run.complete input (C.success tt consumed suffix exact) executed))
  refl

finish : ∀ {input} consumed suffix exact →
  Step.Step.result (Step.transition (Step.value []) input) ≡
    C.success (Step.next (Step.boundary [] true)) consumed suffix exact →
  Back.Returned (Flow.lift (Run.read input)) tt suffix
finish {input} consumed suffix refl first = received (consumed ++ []) suffix _
  (Run.continued (Step.boundary [] true) consumed suffix refl first
   (C.done tt suffix) (Run.completed [] suffix refl refl))

null : ∀ suffix → Back.Returned
  (Flow.lift (Run.read ((# 110) ∷ (# 117) ∷ (# 108) ∷ (# 108) ∷ suffix))) tt suffix
null suffix = finish (# 110 ∷ # 117 ∷ # 108 ∷ # 108 ∷ []) suffix refl refl

spelling : Bool → List Byte
spelling true = (# 116) ∷ (# 114) ∷ (# 117) ∷ (# 101) ∷ []
spelling false = (# 102) ∷ (# 97) ∷ (# 108) ∷ (# 115) ∷ (# 101) ∷ []

boolean : ∀ value suffix → Back.Returned
  (Flow.lift (Run.read (spelling value ++ suffix))) tt suffix
boolean true suffix = finish (spelling true) suffix refl refl
boolean false suffix = finish (spelling false) suffix refl refl

stringBodyResult : ∀ {input} (parsed : String.Parsed input) →
  String.readBody input ≡ inj₂ parsed →
  Step.stringBody input ≡ C.success tt (String.spellBody (String.Parsed.body parsed))
    (String.Parsed.rest parsed) (String.Parsed.exact parsed)
stringBodyResult receipt observed rewrite observed = refl

string : ∀ body → String.ValidBody body → ∀ suffix → Back.Returned
  (Flow.lift (Run.read ((# 34) ∷ (String.spellBody body ++ suffix)))) tt suffix
string body valid suffix with String.readBodyComplete body valid suffix
... | String.parsed .body checked .suffix exact , observed , refl , refl = finish (# 34 ∷ String.spellBody body) suffix _
  (cong
   (λ result →
      C.prefix []
      (Step.Step.result
       (Step.consume (Step.boundary [] true) (# 34) result)))
   (stringBodyResult (String.parsed body checked suffix exact)
    observed))

{-# OPTIONS --safe #-}
-- Container delimiters and keys are actual iterative skip transitions.
import Mimir.FloatConversion
module Mimir.JsonIgnoredContainerPath (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_; _≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)
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
module C = Step.C

arrayOpen : ∀ frames suffix → Path.Path (Step.value frames) ((# 91) ∷ suffix)
  (Step.boundary (Step.array ∷ frames) false) suffix
arrayOpen frames suffix = Path.next (Step.boundary (Step.array ∷ frames) false) (# 91 ∷ [])
  suffix refl refl Path.stop

objectOpen : ∀ frames suffix → Path.Path (Step.value frames) ((# 123) ∷ suffix)
  (Step.boundary (Step.object ∷ frames) false) suffix
objectOpen frames suffix = Path.next (Step.boundary (Step.object ∷ frames) false) (# 123 ∷ [])
  suffix refl refl Path.stop

close : ∀ frame frames first suffix →
  Path.Path (Step.boundary (frame ∷ frames) first) (Step.closer frame ∷ suffix)
    (Step.boundary frames true) suffix
close Step.array frames first suffix = Path.next (Step.boundary frames true) (# 93 ∷ []) suffix refl refl
  Path.stop
close Step.object frames first suffix = Path.next (Step.boundary frames true) (# 125 ∷ []) suffix refl refl
  Path.stop

comma : ∀ frame frames suffix →
  Path.Path (Step.boundary (frame ∷ frames) true) ((# 44) ∷ suffix)
    (Step.memberState frame frames) suffix
comma Step.array frames suffix = Path.next (Step.value (Step.array ∷ frames)) (# 44 ∷ []) suffix
  refl refl Path.stop
comma Step.object frames suffix = Path.next (Step.key (Step.object ∷ frames)) (# 44 ∷ []) suffix refl
  refl Path.stop

arrayFirstStep : ∀ frames byte rest → White.Stopped (byte ∷ rest) → byte ≢ (# 93) →
  Step.Step.result (Step.transition (Step.boundary (Step.array ∷ frames) false) (byte ∷ rest)) ≡
  Step.Step.result (Step.transition (Step.value (Step.array ∷ frames)) (byte ∷ rest))
arrayFirstStep frames byte rest stopped notClose with White.space? byte
... | yes space = ⊥-elim (stopped space)
... | no notSpace with byte ≟ (# 93)
...   | yes same = ⊥-elim (notClose same)
...   | no other = refl

arrayFirst : ∀ frames byte rest suffix → White.Stopped (byte ∷ rest) → byte ≢ (# 93) →
  Path.Path (Step.value (Step.array ∷ frames)) (byte ∷ rest) (Step.boundary (Step.array ∷ frames) true) suffix →
  Path.Path (Step.boundary (Step.array ∷ frames) false) (byte ∷ rest) (Step.boundary (Step.array ∷ frames) true) suffix
arrayFirst frames byte rest suffix stopped notClose (Path.next following consumed remaining exact observed tail) = Path.next following consumed remaining exact
  (trans (arrayFirstStep frames byte rest stopped notClose) observed)
  tail

objectFirst : ∀ frames rest suffix →
  Path.Path (Step.key (Step.object ∷ frames)) ((# 34) ∷ rest) (Step.boundary (Step.object ∷ frames) true) suffix →
  Path.Path (Step.boundary (Step.object ∷ frames) false) ((# 34) ∷ rest) (Step.boundary (Step.object ∷ frames) true) suffix
objectFirst frames rest suffix (Path.next following consumed remaining exact observed tail) = Path.next following consumed remaining exact observed tail

key : ∀ frames body → String.ValidBody body → ∀ suffix →
  Path.Path (Step.key frames) ((# 34) ∷ (String.spellBody body ++ ((# 58) ∷ suffix)))
    (Step.value frames) suffix
key frames body valid suffix with String.readBodyComplete body valid ((# 58) ∷ suffix)
... | String.parsed .body checked .((# 58) ∷ suffix) refl , observed , refl , refl = Path.next (Step.value frames)
  (# 34 ∷ String.spellBody body ++ # 58 ∷ []) suffix _
  (cong
   (λ result →
      C.prefix []
      (Step.Step.result
       (Step.consume (Step.value frames) (# 34)
        (C.andThen result (λ unit rest → Controls.colon rest)))))
   (Ignored.stringBodyResult
    (String.parsed body checked (# 58 ∷ suffix) refl) observed))
  Path.stop

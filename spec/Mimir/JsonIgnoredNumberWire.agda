{-# OPTIONS --safe #-}
-- Transport ignored-number grammar completeness to actual byte inputs,
-- preserving both the consumed number and every byte of the suffix.
module Mimir.JsonIgnoredNumberWire where

open import Data.List using (List; _++_)
open import Data.List.Properties using (map-++; ++-cancelʳ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.JsonIgnoredNumber as N
import Mimir.JsonIgnoredNumberComplete as Complete
import Mimir.JsonNumber as G
import Mimir.JsonNumberSuffix as Suffix
import Mimir.JsonNumberWire as Grammar
import Mimir.ByteText as Wire
module B = N.Bridge.B

data Succeeded {input : List Byte} (suffix : List Byte) : B.Result ⊤ input → Set where
  success : ∀ consumed exact → Succeeded suffix (B.success tt consumed suffix exact)

transport : ∀ {input suffix} {result : N.C.Result ⊤ (Wire.text input)} →
  Complete.Succeeded (Wire.text suffix) result → Succeeded suffix (N.Bridge.transport result)
transport {input} {suffix} (Complete.success consumed exact) = subst
  (λ tail → Succeeded tail (N.Bridge.transport (N.C.success tt consumed (Wire.text suffix) exact)))
  (Wire.bytesText suffix _) (success _ _)

spellingText : ∀ form suffix → Wire.text (Grammar.spell form ++ suffix) ≡ G.spell form ++ Wire.text suffix
spellingText form suffix = trans (map-++ Wire.character (Grammar.spell form) suffix)
  (cong (_++ Wire.text suffix) (Grammar.Prefix.spellingText form))

readComplete : ∀ form suffix → Suffix.Terminal (Wire.text suffix) →
  Succeeded suffix (N.readBytes (Grammar.spell form ++ suffix))
readComplete form suffix terminal = transport
  (subst (λ input → Complete.Succeeded (Wire.text suffix) (N.read input))
    (sym (spellingText form suffix)) (Complete.readComplete form (Wire.text suffix) terminal))

consumedExact : ∀ prefix suffix {result : B.Result ⊤ (prefix ++ suffix)} →
  Succeeded suffix result → B.consumed result ≡ prefix
consumedExact prefix suffix (success consumed exact) = sym (++-cancelʳ suffix prefix consumed exact)

remainingExact : ∀ {input suffix} {result : B.Result ⊤ input} →
  Succeeded suffix result → B.remaining result ≡ suffix
remainingExact (success consumed exact) = refl

cannotFail : ∀ {input suffix} {result : B.Result ⊤ input} → Succeeded suffix result →
  ∀ code consumed remaining exact → result ≢ B.failure code consumed remaining exact
cannotFail (success consumed′ exact′) code consumed remaining exact ()

consumesNumber : ∀ form suffix → Suffix.Terminal (Wire.text suffix) →
  B.consumed (N.readBytes (Grammar.spell form ++ suffix)) ≡ Grammar.spell form
consumesNumber form suffix terminal = consumedExact (Grammar.spell form) suffix (readComplete form suffix terminal)

preservesSuffix : ∀ form suffix → Suffix.Terminal (Wire.text suffix) →
  B.remaining (N.readBytes (Grammar.spell form ++ suffix)) ≡ suffix
preservesSuffix form suffix terminal = remainingExact (readComplete form suffix terminal)

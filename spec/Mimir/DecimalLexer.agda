{-# OPTIONS --safe #-}
-- Maximal ASCII-digit prefixes for JSON numeric syntax. A leading sign is not
-- accepted here; the enclosing grammar decides which signs are permitted.
module Mimir.DecimalLexer where

open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (∷-injectiveˡ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Mimir.Text using (Text)
import Mimir.Unsigned as D

NotDigit : Char → Set
NotDigit c = ∀ d → c ≢ D.character d

Stopped : Text → Set
Stopped [] = ⊤
Stopped (c ∷ cs) = NotDigit c

nothingNotJust : ∀ {A : Set} {x : A} → nothing ≢ just x
nothingNotJust ()

notDecoded : ∀ c → D.decodeDigit c ≡ nothing → NotDigit c
notDecoded c absent d refl = nothingNotJust (trans (sym absent) (D.decodeComplete d))

DigitAt : Char → Set
DigitAt c = Σ[ d ∈ D.Digit ] c ≡ D.character d

classify : (c : Char) → Dec (DigitAt c)
classify c with D.decodeDigit c in found
... | nothing = no (λ { (d , same) → notDecoded c found d same })
... | just (D.readDigit d same) = yes (d , same)

classifyComplete : ∀ d → classify (D.character d) ≡ yes (d , refl)
classifyComplete D.d0 = refl
classifyComplete D.d1 = refl
classifyComplete D.d2 = refl
classifyComplete D.d3 = refl
classifyComplete D.d4 = refl
classifyComplete D.d5 = refl
classifyComplete D.d6 = refl
classifyComplete D.d7 = refl
classifyComplete D.d8 = refl
classifyComplete D.d9 = refl

record Run (input : Text) : Set where
  constructor run
  field
    digits : List D.Digit
    suffix : Text
    reconstruct : input ≡ map D.character digits ++ suffix
    stopped : Stopped suffix

take : (input : Text) → Run input
take [] = run [] [] refl tt
take (c ∷ cs) with classify c
... | no notDigit = run [] (c ∷ cs) refl (λ d same → notDigit (d , same))
... | yes (d , same) with take cs
...   | run digits rest equation stopped = run (d ∷ digits) rest
  (trans (cong (_∷ cs) same) (cong (D.character d ∷_) equation)) stopped

maximal : ∀ input → Stopped (Run.suffix (take input))
maximal input = Run.stopped (take input)

exactReconstruction : ∀ input → input ≡ map D.character (Run.digits (take input)) ++ Run.suffix (take input)
exactReconstruction input = Run.reconstruct (take input)

stoppedRun : ∀ {input} (r : Run input) → Stopped input →
  Run.digits r ≡ [] × Run.suffix r ≡ input
stoppedRun (run [] suffix reconstruct terminal) stopped = refl , sym reconstruct
stoppedRun {[]} (run (d ∷ ds) suffix () terminal) stopped
stoppedRun {c ∷ cs} (run (d ∷ ds) suffix reconstruct terminal) stopped =
  ⊥-elim (stopped d (∷-injectiveˡ reconstruct))

complete : ∀ digits rest → Stopped rest →
  Run.digits (take (map D.character digits ++ rest)) ≡ digits ×
  Run.suffix (take (map D.character digits ++ rest)) ≡ rest
complete [] rest stopped = stoppedRun (take rest) stopped
complete (d ∷ ds) rest stopped rewrite classifyComplete d
  with take (map D.character ds ++ rest) | complete ds rest stopped
... | run digits suffix reconstruct terminal | sameDigits , sameSuffix =
  cong (d ∷_) sameDigits , sameSuffix

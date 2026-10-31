{-# OPTIONS --safe #-}
-- Ignored string syntax: arbitrary non-control literal bytes and syntactically
-- valid escapes. No UTF-8 assembly or surrogate-pair validation is performed.
module Mimir.JsonIgnoredString where

open import Data.Fin using (#_; toℕ; _≟_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; length-++-≤ʳ)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (zero; suc; _≤_; _≤?_; s≤s⁻¹; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.Bits using (Byte)
import Mimir.JsonString as String
import Mimir.JsonStringParser as Decoded
import Mimir.JsonIgnoredEscape as Escape

module Fault = Decoded.Fault

data Atom : Set where
  literal : Byte → Atom
  escaped : Escape.Raw → Atom

Valid : Atom → Set
Valid (literal byte) = String.Literal byte
Valid (escaped raw) = ⊤

spell : Atom → List Byte
spell (literal byte) = byte ∷ []
spell (escaped raw) = (# 92) ∷ Escape.spell raw

Body = List Atom
ValidBody = All Valid

spellBody : Body → List Byte
spellBody [] = (# 34) ∷ []
spellBody (atom ∷ rest) = spell atom ++ spellBody rest

record Parsed (input : List Byte) : Set where
  constructor parsed
  field body : Body; valid : ValidBody body; rest : List Byte; exact : input ≡ spellBody body ++ rest

escapeFailure : ∀ {input} → Escape.Fault.Failure input → Fault.Failure input
escapeFailure (Escape.Fault.failed code consumed remaining exact) =
  Fault.failed (Decoded.escapeError code) consumed remaining exact

escapeSuffixBound : ∀ fuel {input} (result : Escape.Parsed input) → length input ≤ fuel →
  length (Escape.Parsed.rest result) ≤ fuel
escapeSuffixBound fuel (Escape.parsed raw rest refl) bound =
  ≤-trans (length-++-≤ʳ rest {xs = Escape.spell raw}) bound

prepend : ∀ atom → Valid atom → ∀ {input suffix} → input ≡ spell atom ++ suffix →
  Parsed suffix → Parsed input
prepend atom valid exact (parsed body admitted rest bodyExact) =
  parsed (atom ∷ body) (valid All.∷ admitted) rest
    (trans exact (trans (cong (spell atom ++_) bodyExact)
      (sym (++-assoc (spell atom) (spellBody body) rest))))

continue : ∀ atom → Valid atom → ∀ {input suffix} → input ≡ spell atom ++ suffix →
  Fault.Failure suffix ⊎ Parsed suffix → Fault.Failure input ⊎ Parsed input
continue atom valid exact (inj₁ failure) = inj₁ (Fault.reframe exact (Fault.prefix (spell atom) failure))
continue atom valid exact (inj₂ result) = inj₂ (prepend atom valid exact result)

readBounded : ∀ fuel input → length input ≤ fuel → Fault.Failure input ⊎ Parsed input
readBounded fuel [] bound = inj₁ (Fault.end [] Decoded.eofString)
readBounded zero (byte ∷ input) ()
readBounded (suc fuel) (byte ∷ input) bound with byte ≟ (# 34)
... | yes refl = inj₂ (parsed [] All.[] input refl)
... | no notQuote with byte ≟ (# 92)
...   | yes refl with Escape.parse input
...     | inj₁ failure = inj₁ (Fault.prefix ((# 92) ∷ []) (escapeFailure failure))
...     | inj₂ result = continue (escaped (Escape.Parsed.raw result)) tt
        (cong ((# 92) ∷_) (Escape.Parsed.exact result))
        (readBounded fuel (Escape.Parsed.rest result) (escapeSuffixBound fuel result (s≤s⁻¹ bound)))
readBounded (suc fuel) (byte ∷ input) bound | no notQuote | no notSlash with 32 ≤? toℕ byte
... | no control = inj₁ (Fault.failed Decoded.controlCharacter [] (byte ∷ input) refl)
... | yes large = continue (literal byte) (large , notQuote , notSlash) refl
    (readBounded fuel input (s≤s⁻¹ bound))

readBody : ∀ input → Fault.Failure input ⊎ Parsed input
readBody input = readBounded (length input) input ≤-refl

bodyPositive : ∀ body rest → 1 ≤ length (spellBody body ++ rest)
bodyPositive [] rest = s≤s z≤n
bodyPositive (literal byte ∷ body) rest = s≤s z≤n
bodyPositive (escaped raw ∷ body) rest = s≤s z≤n

BodySuccess : ∀ fuel body rest → length (spellBody body ++ rest) ≤ fuel → Set
BodySuccess fuel body rest bound = Σ (Parsed (spellBody body ++ rest)) (λ result →
  readBounded fuel (spellBody body ++ rest) bound ≡ inj₂ result ×
    (Parsed.body result ≡ body × Parsed.rest result ≡ rest))

bodyComplete : ∀ fuel body → ValidBody body → ∀ rest bound → BodySuccess fuel body rest bound
bodyComplete zero body valid rest bound = ⊥-elim (Decoded.oneNotZero (≤-trans (bodyPositive body rest) bound))
bodyComplete (suc fuel) [] All.[] rest bound = parsed [] All.[] rest refl , refl , refl , refl
bodyComplete (suc fuel) (literal byte ∷ body) ((low , notQuote , notSlash) All.∷ valid) rest bound
  with byte ≟ (# 34)
... | yes same = ⊥-elim (notQuote same)
... | no checkedQuote with byte ≟ (# 92)
...   | yes same = ⊥-elim (notSlash same)
...   | no checkedSlash with 32 ≤? toℕ byte
...     | no rejected = ⊥-elim (rejected low)
...     | yes checkedLow with bodyComplete fuel body valid rest (s≤s⁻¹ bound)
...       | parsed .body checked .rest exact , observed , refl , refl
            rewrite observed = _ , refl , refl , refl
bodyComplete (suc fuel) (escaped raw ∷ body) (tt All.∷ valid) rest bound
  rewrite ++-assoc (Escape.spell raw) (spellBody body) rest |
    Escape.parseComplete raw (spellBody body ++ rest)
  with bodyComplete fuel body valid rest
    (escapeSuffixBound fuel (Escape.parsed raw (spellBody body ++ rest) refl) (s≤s⁻¹ bound))
... | parsed .body checked .rest exact , observed , refl , refl
      rewrite observed = _ , refl , refl , refl

readBodyComplete : ∀ body → ValidBody body → ∀ rest →
  Σ (Parsed (spellBody body ++ rest)) (λ result →
    readBody (spellBody body ++ rest) ≡ inj₂ result ×
      (Parsed.body result ≡ body × Parsed.rest result ≡ rest))
readBodyComplete body valid rest = bodyComplete (length (spellBody body ++ rest)) body valid rest ≤-refl

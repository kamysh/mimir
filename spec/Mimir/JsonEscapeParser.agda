{-# OPTIONS --safe #-}
-- JSON String escape parser for SliceRead semantics, including failure
-- consumption. The independent grammar is Mimir.JsonEscape.Raw/Valid.
module Mimir.JsonEscapeParser where

open import Data.Fin using (#_; _≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Nat using (_≤?_; _<?_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.Bits using (Byte)
import Mimir.ByteCursor as Cursor
import Mimir.HexEscape as Hex
import Mimir.UTF16Escape as U
import Mimir.JsonEscape as Grammar

-- These names retain serde_json's categories. Its lone-leading category
-- also reports a lone trailing surrogate or an invalid second surrogate.
data Code : Set where eofString invalidEscape unexpectedEndHex loneSurrogate : Code

module Fault = Cursor.WithCode Code
open Fault using (Failure; failed)

record Parsed (input : List Byte) : Set where
  constructor parsed
  field
    raw : Grammar.Raw
    valid : Grammar.Valid raw
    rest : List Byte
    exact : input ≡ Grammar.spell raw ++ rest

hexFailure : ∀ {input} → Hex.Failure input → Failure input
hexFailure {input} (Hex.truncated short) = Fault.end input eofString
hexFailure (Hex.invalid a b c d rest exact rejected) =
  failed invalidEscape (a ∷ b ∷ c ∷ d ∷ []) rest exact

trailing? : ∀ unit → Dec (U.Trailing (U.value unit))
trailing? unit = (56320 ≤? U.value unit) ×-dec (U.value unit <? 57344)

record Tail (input : List Byte) : Set where
  constructor tail
  field
    digits : Hex.Four
    valid : U.Trailing (U.value (Hex.unit digits))
    rest : List Byte
    exact : input ≡ (# 92) ∷ (# 117) ∷ (Hex.spell digits ++ rest)

readTail : ∀ input → Failure input ⊎ Tail input
readTail [] = inj₁ (Fault.end [] eofString)
readTail (first ∷ rest) with first ≟ (# 92)
... | no _ = inj₁ (failed unexpectedEndHex (first ∷ []) rest refl)
... | yes refl with rest
...   | [] = inj₁ (Fault.end ((# 92) ∷ []) eofString)
...   | second ∷ rest with second ≟ (# 117)
...     | no _ = inj₁ (failed unexpectedEndHex ((# 92) ∷ second ∷ []) rest refl)
...     | yes refl with Hex.parse rest
...       | inj₁ failure = inj₁ (Fault.prefix ((# 92) ∷ (# 117) ∷ []) (hexFailure failure))
...       | inj₂ (Hex.parsed digits rest exact) with trailing? (Hex.unit digits)
...         | no _ = inj₁ (failed loneSurrogate ((# 92) ∷ (# 117) ∷ Hex.spell digits) rest
              (cong (λ bytes → (# 92) ∷ (# 117) ∷ bytes) exact))
...         | yes valid = inj₂ (tail digits valid rest (cong (λ bytes → (# 92) ∷ (# 117) ∷ bytes) exact))

parseUnicode : ∀ input → Failure ((# 117) ∷ input) ⊎ Parsed ((# 117) ∷ input)
parseUnicode input with Hex.parse input
... | inj₁ failure = inj₁ (Fault.prefix ((# 117) ∷ []) (hexFailure failure))
... | inj₂ (Hex.parsed first rest exact) with U.classify (Hex.unit first)
...   | U.literal valid = inj₂ (parsed (Grammar.unit first) valid rest (cong ((# 117) ∷_) exact))
...   | U.loneTrailing invalid = inj₁ (failed loneSurrogate ((# 117) ∷ Hex.spell first) rest (cong ((# 117) ∷_) exact))
...   | U.needsTrailing leading with readTail rest
...     | inj₁ failure = inj₁ (Fault.reframe (cong ((# 117) ∷_) exact)
          (Fault.prefix ((# 117) ∷ Hex.spell first) failure))
...     | inj₂ (tail second trailing rest tailExact) = inj₂
          (parsed (Grammar.pair first second) (leading , trailing) rest
            (cong ((# 117) ∷_) (trans exact
              (trans (cong (Hex.spell first ++_) tailExact)
                (sym (++-assoc (Hex.spell first) ((# 92) ∷ (# 117) ∷ Hex.spell second) rest))))))

parse : ∀ input → Failure input ⊎ Parsed input
parse [] = inj₁ (Fault.end [] eofString)
parse (first ∷ rest) with Grammar.read first
... | yes (Grammar.readShort escape refl) = inj₂ (parsed (Grammar.short escape) tt rest refl)
... | no _ with first ≟ (# 117)
...   | yes refl = parseUnicode rest
...   | no _ = inj₁ (failed invalidEscape (first ∷ []) rest refl)

tailComplete : ∀ digits → U.Trailing (U.value (Hex.unit digits)) → ∀ rest →
  Σ (Tail ((# 92) ∷ (# 117) ∷ (Hex.spell digits ++ rest))) (λ result →
    readTail ((# 92) ∷ (# 117) ∷ (Hex.spell digits ++ rest)) ≡ inj₂ result ×
    (Tail.digits result ≡ digits × Tail.rest result ≡ rest))
tailComplete digits valid rest rewrite Hex.parseComplete digits rest with trailing? (Hex.unit digits)
... | yes admitted = tail digits admitted rest refl , refl , refl , refl
... | no rejected = ⊥-elim (rejected valid)

unitComplete : ∀ digits → Grammar.Valid (Grammar.unit digits) → ∀ rest →
  Σ (Parsed (Grammar.spell (Grammar.unit digits) ++ rest)) (λ result →
    parseUnicode (Hex.spell digits ++ rest) ≡ inj₂ result ×
    (Parsed.raw result ≡ Grammar.unit digits × Parsed.rest result ≡ rest))
unitComplete digits valid rest with U.classifyLiteral (Hex.unit digits) valid
... | admitted , observed rewrite Hex.parseComplete digits rest | observed =
  parsed (Grammar.unit digits) admitted rest refl , refl , refl , refl

pairComplete : ∀ first second → Grammar.Valid (Grammar.pair first second) → ∀ rest →
  Σ (Parsed (Grammar.spell (Grammar.pair first second) ++ rest)) (λ result →
    parseUnicode ((Hex.spell first ++ ((# 92) ∷ (# 117) ∷ Hex.spell second)) ++ rest) ≡ inj₂ result ×
    (Parsed.raw result ≡ Grammar.pair first second × Parsed.rest result ≡ rest))
pairComplete first second (leading , trailing) rest
  with U.classifyLeading (Hex.unit first) leading | tailComplete second trailing rest
... | admitted , classified | tail .second checked .rest exact , observed , refl , refl
  rewrite ++-assoc (Hex.spell first) ((# 92) ∷ (# 117) ∷ Hex.spell second) rest |
    Hex.parseComplete first ((# 92) ∷ (# 117) ∷ (Hex.spell second ++ rest)) |
    classified | observed = _ , refl , refl , refl

parseComplete : ∀ raw → Grammar.Valid raw → ∀ rest →
  Σ (Parsed (Grammar.spell raw ++ rest)) (λ result →
    parse (Grammar.spell raw ++ rest) ≡ inj₂ result ×
    (Parsed.raw result ≡ raw × Parsed.rest result ≡ rest))
parseComplete (Grammar.short escape) valid rest rewrite Grammar.readComplete escape =
  parsed (Grammar.short escape) tt rest refl , refl , refl , refl
parseComplete (Grammar.unit digits) valid rest = unitComplete digits valid rest
parseComplete (Grammar.pair first second) valid rest = pairComplete first second valid rest

parseGiven : ∀ {input} (expected : Parsed input) →
  Σ (Parsed input) (λ actual → parse input ≡ inj₂ actual ×
    (Parsed.raw actual ≡ Parsed.raw expected × Parsed.rest actual ≡ Parsed.rest expected))
parseGiven (parsed raw valid rest refl) = parseComplete raw valid rest

interpretationUnique : ∀ {input} (first second : Parsed input) →
  Parsed.raw first ≡ Parsed.raw second × Parsed.rest first ≡ Parsed.rest second
interpretationUnique first second with parseGiven first | parseGiven second
... | actual , readFirst , firstRaw , firstRest | other , readSecond , secondRaw , secondRest =
  trans (sym firstRaw) (trans (cong Parsed.raw same) secondRaw) ,
  trans (sym firstRest) (trans (cong Parsed.rest same) secondRest)
  where
  same = inj₂-injective (trans (sym readFirst) readSecond)

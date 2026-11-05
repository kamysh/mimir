{-# OPTIONS --safe #-}
-- serde_json::read::ignore_escape accepts any four hexadecimal digits after
-- u. It does not require a scalar value or a paired surrogate.
module Mimir.JsonIgnoredEscape where

open import Data.Fin using (#_; _≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Bits using (Byte)
import Mimir.JsonEscape as Escape
import Mimir.JsonEscapeParser as Decoded
import Mimir.HexEscape as Hex

module Fault = Decoded.Fault

data Raw : Set where
  short : Escape.Short → Raw
  unicode : Hex.Four → Raw

spell : Raw → List Byte
spell (short value) = Escape.marker value ∷ []
spell (unicode digits) = (# 117) ∷ Hex.spell digits

record Parsed (input : List Byte) : Set where
  constructor parsed
  field raw : Raw; rest : List Byte; exact : input ≡ spell raw ++ rest

fromHex : ∀ {input} → Hex.Failure input ⊎ Hex.Parsed input →
  Fault.Failure ((# 117) ∷ input) ⊎ Parsed ((# 117) ∷ input)
fromHex (inj₁ failure) = inj₁ (Fault.prefix ((# 117) ∷ []) (Decoded.hexFailure failure))
fromHex (inj₂ (Hex.parsed digits rest exact)) =
  inj₂ (parsed (unicode digits) rest (cong ((# 117) ∷_) exact))

unicodeEscape : ∀ input → Fault.Failure ((# 117) ∷ input) ⊎ Parsed ((# 117) ∷ input)
unicodeEscape input = fromHex (Hex.parse input)

parse : ∀ input → Fault.Failure input ⊎ Parsed input
parse [] = inj₁ (Fault.end [] Decoded.eofString)
parse (first ∷ rest) with Escape.read first
... | yes (Escape.readShort value refl) = inj₂ (parsed (short value) rest refl)
... | no notShort with first ≟ (# 117)
...   | yes refl = unicodeEscape rest
...   | no notUnicode = inj₁ (Fault.failed Decoded.invalidEscape (first ∷ []) rest refl)

unicodeComplete : ∀ digits rest → unicodeEscape (Hex.spell digits ++ rest) ≡
  inj₂ (parsed (unicode digits) rest refl)
unicodeComplete digits rest = cong fromHex (Hex.parseComplete digits rest)

parseComplete : ∀ raw rest → parse (spell raw ++ rest) ≡ inj₂ (parsed raw rest refl)
parseComplete (short value) rest rewrite Escape.readComplete value = refl
parseComplete (unicode digits) rest = unicodeComplete digits rest

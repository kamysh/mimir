{-# OPTIONS --safe #-}
-- Canonical UUID JSON strings, exact byte size, and parser composition.
-- This handles string payloads; record visitors separately reject nonstrings.
module Mimir.UUIDJson where

open import Data.Fin using (Fin; #_; toℕ)
import Data.Fin.Properties as Fin
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
import Data.Vec as V
open import Data.Nat using (_<?_; _+_; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (_×-dec_; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.ASCIIText as ASCII
import Mimir.ByteHex as Pair
import Mimir.LowerHex as Lower
import Mimir.HexEscape as Hex
import Mimir.HexBytes as Bytes
import Mimir.UUIDGroups as G
import Mimir.UUIDHyphenated as H
import Mimir.UUIDParse as P
import Mimir.JsonString as String
import Mimir.JsonLiteral as Literal
import Mimir.JsonStringParser as Parser
import Mimir.UTF8Text as UTF8

Glyph : Byte → Set
Glyph byte = ASCII.ASCII byte × String.Literal byte

abstract
  lowerGlyph : ∀ digit → Glyph (Hex.byte (Hex.lowerDigit digit))
  lowerGlyph = toWitness {a? = Fin.all? (λ digit →
    (toℕ (Hex.byte (Hex.lowerDigit digit)) <? 128) ×-dec String.literal? (Hex.byte (Hex.lowerDigit digit)))} tt

  dashGlyph : Glyph (# 45)
  dashGlyph = toWitness {a? = (45 <? 128) ×-dec String.literal? (# 45)} tt

digitGlyphs : ∀ digits → All Glyph (V.toList (Pair.spellDigits digits))
digitGlyphs (low V.∷ high V.∷ V.[]) = lowerGlyph high All.∷ lowerGlyph low All.∷ All.[]

hexGlyphs : ∀ {count} (bytes : V.Vec Byte count) → All Glyph (Bytes.encode bytes)
hexGlyphs V.[] = All.[]
hexGlyphs (byte V.∷ bytes) = ++⁺ (digitGlyphs (Lower.digits byte)) (hexGlyphs bytes)

groupGlyphs : ∀ parts → All Glyph (H.spell parts)
groupGlyphs (G.groups first second third fourth fifth) = ++⁺ (hexGlyphs first)
  (dashGlyph All.∷ ++⁺ (hexGlyphs second) (dashGlyph All.∷ ++⁺ (hexGlyphs third)
    (dashGlyph All.∷ ++⁺ (hexGlyphs fourth) (dashGlyph All.∷ hexGlyphs fifth))))

admitted : ∀ value → All String.Literal (H.encode value)
admitted value = All.map proj₂ (groupGlyphs (G.split value))

decoded : ∀ value → UTF8.Decoded (H.encode value)
decoded value = ASCII.decode (All.map proj₁ (groupGlyphs (G.split value)))

render : G.UUID → String.StringValue
render value = String.stringValue (Literal.literalBody (H.encode value))
  (Literal.literalValid (admitted value))
  (subst UTF8.Decoded (sym (Literal.literalOutput (H.encode value) (admitted value))) (decoded value))

payload : String.StringValue → List Byte
payload value = String.bodyOutput (String.StringValue.body value) (String.StringValue.valid value)

payloadExact : ∀ value → payload (render value) ≡ H.encode value
payloadExact value = Literal.literalOutput (H.encode value) (admitted value)

read : String.StringValue → P.Result
read value = P.read (payload value)

roundTrip : ∀ value → read (render value) ≡ P.accepted value
roundTrip value = trans (cong P.read (payloadExact value)) (P.canonicalRoundTrip value)

literalSpelling : ∀ bytes → String.spellBody (Literal.literalBody bytes) ≡ bytes ++ ((# 34) ∷ [])
literalSpelling [] = refl
literalSpelling (byte ∷ bytes) = cong (byte ∷_) (literalSpelling bytes)

wire : G.UUID → List Byte
wire value = String.spellString (String.StringValue.body (render value))

wireExact : ∀ value → wire value ≡ (# 34) ∷ (H.encode value ++ ((# 34) ∷ []))
wireExact value = cong ((# 34) ∷_) (literalSpelling (H.encode value))

wireLength : ∀ value → length (wire value) ≡ 38
wireLength value = trans (cong length (wireExact value))
  (cong suc (trans (length-++ (H.encode value) {ys = (# 34) ∷ []}) (cong (_+ 1) (H.uuidLength value))))

sameBodyPayload : ∀ first second → String.StringValue.body first ≡ String.StringValue.body second → payload first ≡ payload second
sameBodyPayload (String.stringValue body first decoded₁) (String.stringValue .body second decoded₂) refl =
  String.bodyOutputIndependent body first second

parsedRoundTrip : ∀ value rest → Σ (Parser.Parsed (wire value ++ rest)) (λ result →
  Parser.parse (wire value ++ rest) ≡ inj₂ result ×
    (Parser.Parsed.rest result ≡ rest × read (Parser.Parsed.value result) ≡ P.accepted value))
parsedRoundTrip value rest with Parser.parseComplete (render value) rest
... | result , observed , sameBody , sameRest , sameValues = result , observed , sameRest ,
  trans (cong P.read (sameBodyPayload (Parser.Parsed.value result) (render value) sameBody)) (roundTrip value)

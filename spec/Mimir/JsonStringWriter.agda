{-# OPTIONS --safe #-}
-- JSON string serialization: quote/backslash escapes, the five short control
-- escapes, lowercase hexadecimal for other C0 controls, and verbatim UTF-8
-- otherwise. The proof preserves scalar numbers, not proof-object identity.
module Mimir.JsonStringWriter where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; _+_; _≤_; _<_; _<?_; _≟_)
open import Data.Nat.Properties using (m≤m+n; <-≤-trans; ≮⇒≥)
open import Data.Product using (_×_; _,_; Σ; proj₂)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)
import Mimir.JsonString as String
import Mimir.JsonStringParser as Parser
import Mimir.JsonLiteral as Literal
import Mimir.JsonEscape as Escape
import Mimir.HexEscape as Hex
import Mimir.UTF16Escape as Unit
import Mimir.UnicodeScalar as Number
import Mimir.UTF8Packet as Packet
import Mimir.UTF8Text as UTF8

point : Packet.Scalar → ℕ
point value = Packet.codePoint (Packet.Scalar.raw value)

record Step (original : Packet.Scalar) : Set where
  constructor step
  field
    body : String.Body
    valid : String.ValidBody body
    emitted : Packet.Scalar
    bytes : String.bodyOutput body valid ≡ Packet.encode (Packet.Scalar.raw emitted)
    samePoint : point emitted ≡ point original

escapeStep : ∀ original raw (valid : Escape.Valid raw) → Escape.number raw ≡ point original → Step original
escapeStep original raw valid same = step (String.escaped raw ∷ []) (valid All.∷ All.[])
  (Number.Encoded.value (Escape.encode raw valid))
  (++-identityʳ (Packet.encode (Packet.Scalar.raw (Number.Encoded.value (Escape.encode raw valid)))))
  (trans (Number.Encoded.exact (Escape.encode raw valid)) same)

rawStep : ∀ original → Literal.Regular (point original) → Step original
rawStep original regular = step (Literal.literalBody (Packet.encode (Packet.Scalar.raw original)))
  (Literal.literalValid (Literal.packetLiteral (Packet.Scalar.raw original) regular)) original
  (Literal.literalOutput (Packet.encode (Packet.Scalar.raw original)) (Literal.packetLiteral (Packet.Scalar.raw original) regular)) refl

abstract
  padding : ∀ number extra → number ≤ number + extra
  padding = m≤m+n

controlStep : ∀ original → point original < 32 → Step original
controlStep original small = escapeStep original (Escape.unit digits)
  (subst Number.Valid (sym exact) (proj₂ (Packet.Scalar.canonical original))) exact
  where
  bound = <-≤-trans small (padding 32 224)
  low = Unit.offsetWord 8 0 (point original) bound
  word = Hex.byteUnit low
  digits = Hex.fromUnit word
  exact = trans (cong Unit.value (Hex.fromUnitExact word))
    (trans (Hex.byteUnitValue low) (Unit.offsetValue 8 0 (point original) bound))

choose : ∀ original → Step original
choose original with point original ≟ 34
... | yes same = escapeStep original (Escape.short Escape.quotation) tt (sym same)
... | no notQuote with point original ≟ 92
...   | yes same = escapeStep original (Escape.short Escape.backslash) tt (sym same)
...   | no notSlash with point original <? 32
...     | no notControl = rawStep original (≮⇒≥ notControl , notQuote , notSlash)
...     | yes control with point original ≟ 8
...       | yes same = escapeStep original (Escape.short Escape.backspace) tt (sym same)
...       | no _ with point original ≟ 9
...         | yes same = escapeStep original (Escape.short Escape.tab) tt (sym same)
...         | no _ with point original ≟ 10
...           | yes same = escapeStep original (Escape.short Escape.newline) tt (sym same)
...           | no _ with point original ≟ 12
...             | yes same = escapeStep original (Escape.short Escape.formfeed) tt (sym same)
...             | no _ with point original ≟ 13
...               | yes same = escapeStep original (Escape.short Escape.carriageReturn) tt (sym same)
...               | no _ = controlStep original control

appendValid : ∀ {left right} → String.ValidBody left → String.ValidBody right → String.ValidBody (left ++ right)
appendValid All.[] right = right
appendValid (valid All.∷ rest) right = valid All.∷ appendValid rest right

appendOutput : ∀ left right (first : String.ValidBody left) (second : String.ValidBody right) →
  String.bodyOutput (left ++ right) (appendValid first second) ≡ String.bodyOutput left first ++ String.bodyOutput right second
appendOutput [] right All.[] second = refl
appendOutput (atom ∷ rest) right (valid All.∷ remaining) second
  rewrite appendOutput rest right remaining second =
  sym (++-assoc (String.output atom valid) (String.bodyOutput rest remaining) (String.bodyOutput right second))

codes : List Packet.Scalar → List ℕ
codes = map point

record Serialized (original : List Packet.Scalar) : Set where
  constructor serialized
  field
    body : String.Body
    valid : String.ValidBody body
    emitted : List Packet.Scalar
    bytes : String.bodyOutput body valid ≡ UTF8.encode emitted
    samePoints : codes emitted ≡ codes original

serialize : ∀ original → Serialized original
serialize [] = serialized [] All.[] [] refl refl
serialize (first ∷ rest) with choose first | serialize rest
... | step body valid emitted bytes same | serialized tail admitted values tailBytes tailSame =
  serialized (body ++ tail) (appendValid valid admitted) (emitted ∷ values)
    (trans (appendOutput body tail valid admitted) (cong₂ _++_ bytes tailBytes))
    (cong₂ _∷_ same tailSame)

render : List Packet.Scalar → String.StringValue
render original with serialize original
... | serialized body valid emitted bytes same = String.stringValue body valid (UTF8.decoded emitted bytes)

renderMeaning : ∀ original → codes (String.values (render original)) ≡ codes original
renderMeaning original with serialize original
... | serialized body valid emitted bytes same = same

codesFromRaw : ∀ values → codes values ≡ map Packet.codePoint (map Packet.Scalar.raw values)
codesFromRaw [] = refl
codesFromRaw (first ∷ rest) = cong (point first ∷_) (codesFromRaw rest)

rawSameCodes : ∀ first second → map Packet.Scalar.raw first ≡ map Packet.Scalar.raw second → codes first ≡ codes second
rawSameCodes first second same = trans (codesFromRaw first)
  (trans (cong (map Packet.codePoint) same) (sym (codesFromRaw second)))

roundTrip : ∀ original rest →
  Σ (Parser.Parsed (String.spellString (String.StringValue.body (render original)) ++ rest)) (λ result →
    Parser.parse (String.spellString (String.StringValue.body (render original)) ++ rest) ≡ inj₂ result ×
    (Parser.Parsed.rest result ≡ rest × codes (String.values (Parser.Parsed.value result)) ≡ codes original))
roundTrip original rest with Parser.parseComplete (render original) rest
... | result , observed , sameBody , sameRest , sameValues = result , observed , sameRest ,
  trans (rawSameCodes (String.values (Parser.Parsed.value result)) (String.values (render original)) sameValues)
    (renderMeaning original)

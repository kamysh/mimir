{-# OPTIONS --safe #-}
-- The human-readable UUID visitor accepts JSON strings only. The explicit
-- invalid-scalar branch covers the wider Agda Char domain; admitted Rust
-- strings cannot take that branch. UUID parse failures retain their source.
module Mimir.UUIDSchema where

open import Data.Char using (toℕ)
open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum.Properties
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
import Mimir.Text as Text
import Mimir.UnicodeText as Unicode
import Mimir.UnicodeScalar as Scalar
import Mimir.UnicodeCursorBytes as Bytes
import Mimir.DecodedText as Decoded
import Mimir.UTF8Text as UTF8
import Mimir.UUIDGroups as G
import Mimir.UUIDHyphenated as H
import Mimir.UUIDParse as P
import Mimir.UUIDJson as JSON
import Mimir.StructuredValue as Schema

data Error : Set where
  expectedString : Schema.Value → Error
  invalidScalar : Text.Text → Error
  invalidUUID : P.Failure → Error

result : P.Result → Error ⊎ G.UUID
result (P.accepted value) = inj₂ value
result (P.rejected diagnostic) = inj₁ (invalidUUID diagnostic)

decodeText : Text.Text → Error ⊎ G.UUID
decodeText text with Unicode.valid? text
... | no invalid = inj₁ (invalidScalar text)
... | yes admitted = result (P.read (Bytes.encoded text admitted))

decode : Schema.Value → Error ⊎ G.UUID
decode (Schema.string text) = decodeText text
decode other = inj₁ (expectedString other)

text : G.UUID → Text.Text
text value = Decoded.text (UTF8.Decoded.values (JSON.decoded value))

valid : ∀ value → Unicode.Valid (text value)
valid value = Decoded.valid (UTF8.Decoded.values (JSON.decoded value))

encode : G.UUID → Schema.Value
encode value = Schema.string (text value)

validIrrelevant : ∀ {text} (first second : Unicode.Valid text) → first ≡ second
validIrrelevant = Unicode.validIrrelevant

encodingExact : ∀ value (admitted : Unicode.Valid (text value)) → Bytes.encoded (text value) admitted ≡ H.encode value
encodingExact value admitted = trans (cong (Bytes.encoded (text value)) (validIrrelevant admitted (valid value)))
  (Bytes.decodedBytesExact (JSON.decoded value))

roundTrip : ∀ value → decode (encode value) ≡ inj₂ value
roundTrip value with Unicode.valid? (text value)
... | no impossible = ⊥-elim (impossible (valid value))
... | yes admitted = cong result (trans (cong P.read (encodingExact value admitted)) (P.canonicalRoundTrip value))

admittedText : ∀ input (admitted : Unicode.Valid input) →
  decodeText input ≡ result (P.read (Bytes.encoded input admitted))
admittedText input admitted with Unicode.valid? input
... | no impossible = ⊥-elim (impossible admitted)
... | yes actual = cong (λ proof → result (P.read (Bytes.encoded input proof))) (validIrrelevant actual admitted)

encodeInjective : ∀ {left right} → encode left ≡ encode right → left ≡ right
encodeInjective {left} {right} same = Data.Sum.Properties.inj₂-injective
  (trans (Relation.Binary.PropositionalEquality.sym (roundTrip left)) (trans (cong decode same) (roundTrip right)))

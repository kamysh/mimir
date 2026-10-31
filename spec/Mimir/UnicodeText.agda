{-# OPTIONS --safe #-}
-- Bridge from the existing Char-sequence model to explicit scalar/UTF-8
-- semantics. Admission requires scalar numbers, rather than postulating an
-- unchecked Char/fromNat conversion inverse.
module Mimir.UnicodeText where

open import Data.Char using (Char; toℕ)
open import Data.Char.Properties using (toℕ-injective)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (inj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Mimir.Text using (Text)
open import Mimir.Collections using (all?)
import Mimir.UnicodeScalar as Number
import Mimir.UTF8Packet as Packet
import Mimir.UTF8Text as UTF8

Valid : Text → Set
Valid = All (λ c → Number.Valid (toℕ c))

valid? : ∀ text → Dec (Valid text)
valid? = all? (λ c → Number.valid? (toℕ c))

validIrrelevant : ∀ {text} (first second : Valid text) → first ≡ second
validIrrelevant [] [] = refl
validIrrelevant {char ∷ chars} (first ∷ rest) (second ∷ remaining) =
  cong₂ _∷_ (Number.validIrrelevant (toℕ char) first second) (validIrrelevant rest remaining)

data Represents : Text → List Packet.Scalar → Set where
  empty : Represents [] []
  more : ∀ {c chars value values} → toℕ c ≡ Packet.codePoint (Packet.Scalar.raw value) →
    Represents chars values → Represents (c ∷ chars) (value ∷ values)

encodeValues : ∀ {text} → Valid text → List Packet.Scalar
encodeValues [] = []
encodeValues {c ∷ chars} (valid ∷ rest) = Number.Encoded.value (Number.encode (toℕ c) valid) ∷ encodeValues rest

encodingRepresentsText : ∀ {text} (valid : Valid text) → Represents text (encodeValues valid)
encodingRepresentsText [] = empty
encodingRepresentsText {c ∷ chars} (valid ∷ rest) =
  more (sym (Number.Encoded.exact (Number.encode (toℕ c) valid))) (encodingRepresentsText rest)

representsUnique : ∀ {first second values} → Represents first values → Represents second values → first ≡ second
representsUnique empty empty = refl
representsUnique (more {c = first} headFirst tailFirst) (more {c = second} headSecond tailSecond) =
  cong₂ _∷_ (toℕ-injective first second (trans headFirst (sym headSecond))) (representsUnique tailFirst tailSecond)

transfer : ∀ {text first second} → Represents text first →
  map Packet.Scalar.raw first ≡ map Packet.Scalar.raw second → Represents text second
transfer {second = []} empty equal = empty
transfer {second = _ ∷ _} empty ()
transfer {second = []} (more head tail) ()
transfer {second = value ∷ values} (more head tail) equal =
  more (trans head (cong Packet.codePoint (∷-injectiveˡ equal))) (transfer tail (∷-injectiveʳ equal))

decodePreservesText : ∀ {text} (valid : Valid text) (result : UTF8.Decoded (UTF8.encode (encodeValues valid))) →
  Represents text (UTF8.Decoded.values result)
decodePreservesText valid result = transfer (encodingRepresentsText valid)
  (UTF8.decodePreservesRawValues (encodeValues valid) result)

roundTrip : ∀ {text} (valid : Valid text) →
  Σ (UTF8.Decoded (UTF8.encode (encodeValues valid))) (λ result →
    UTF8.decode (UTF8.encode (encodeValues valid)) ≡ inj₂ result × Represents text (UTF8.Decoded.values result))
roundTrip valid with UTF8.decodeComplete (encodeValues valid)
... | result , observed = result , observed , decodePreservesText valid result

noTextRewriting : ∀ {original other} (valid : Valid original)
  (result : UTF8.Decoded (UTF8.encode (encodeValues valid))) →
  Represents other (UTF8.Decoded.values result) → original ≡ other
noTextRewriting valid result other = representsUnique (decodePreservesText valid result) other

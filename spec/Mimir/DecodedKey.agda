{-# OPTIONS --safe #-}
-- Byte-key equality and decoded schema-text equality agree in both directions.
-- No distinct canonical JSON keys are merged by the schema conversion.
module Mimir.DecodedKey where

import Data.Char as Char
open import Data.Fin using (toℕ)
import Data.Fin.Properties as Fin
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Properties as List
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Mimir.Bits using (Byte)
import Mimir.UTF8Packet as Packet
import Mimir.UTF8Text as UTF8
import Mimir.UTF8ScalarIdentity as Identity
import Mimir.ScalarCharacter as Character
import Mimir.DecodedText as Decoded
import Mimir.UnicodeText as Unicode
import Mimir.JsonStoredValue as Stored
import Mimir.Text as Text
import Mimir.ByteKeyOrder as Key

text : ∀ {name} → Stored.KeyValid name → Text.Text
text key = Decoded.text (Stored.KeyValid.values key)

record Encoded (source : Text.Text) : Set where
  constructor encoded
  field name : Key.Key; valid : Stored.KeyValid name; exact : text valid ≡ source

fromText : ∀ source → Unicode.Valid source → Encoded source
fromText source admitted = encoded (map toℕ (UTF8.encode values))
  (Stored.validKey values refl (Stored.byteCodesValid (UTF8.encode values))) (Decoded.roundTrip admitted)
  where values = Unicode.encodeValues admitted

textDeterminesRaw : ∀ first second → Decoded.text first ≡ Decoded.text second →
  map Packet.Scalar.raw first ≡ map Packet.Scalar.raw second
textDeterminesRaw [] [] same = refl
textDeterminesRaw [] (_ ∷ _) ()
textDeterminesRaw (_ ∷ _) [] ()
textDeterminesRaw (first ∷ rest) (second ∷ tail) same = cong₂ _∷_
  (Identity.rawUnique (Packet.Scalar.raw first) (Packet.Scalar.raw second)
    (Packet.Scalar.canonical first) (Packet.Scalar.canonical second)
    (trans (sym (Character.exact first))
      (trans (cong Char.toℕ (List.∷-injectiveˡ same)) (Character.exact second))))
  (textDeterminesRaw rest tail (List.∷-injectiveʳ same))

rawDeterminesBytes : ∀ first second → map Packet.Scalar.raw first ≡ map Packet.Scalar.raw second →
  UTF8.encode first ≡ UTF8.encode second
rawDeterminesBytes [] [] same = refl
rawDeterminesBytes [] (_ ∷ _) ()
rawDeterminesBytes (_ ∷ _) [] ()
rawDeterminesBytes (first ∷ rest) (second ∷ tail) same = cong₂ _++_
  (cong Packet.encode (List.∷-injectiveˡ same)) (rawDeterminesBytes rest tail (List.∷-injectiveʳ same))

byteNumbersInjective : ∀ (first second : List Byte) → map toℕ first ≡ map toℕ second → first ≡ second
byteNumbersInjective [] [] same = refl
byteNumbersInjective [] (_ ∷ _) ()
byteNumbersInjective (_ ∷ _) [] ()
byteNumbersInjective (first ∷ rest) (second ∷ tail) same = cong₂ _∷_
  (Fin.toℕ-injective (List.∷-injectiveˡ same)) (byteNumbersInjective rest tail (List.∷-injectiveʳ same))

sameTextSameKey : ∀ {first second} (firstValid : Stored.KeyValid first) (secondValid : Stored.KeyValid second) →
  text firstValid ≡ text secondValid → first ≡ second
sameTextSameKey firstValid secondValid same = trans (Stored.KeyValid.exact firstValid)
  (trans (cong (map toℕ) (rawDeterminesBytes (Stored.KeyValid.values firstValid) (Stored.KeyValid.values secondValid)
    (textDeterminesRaw (Stored.KeyValid.values firstValid) (Stored.KeyValid.values secondValid) same)))
    (sym (Stored.KeyValid.exact secondValid)))

sameKeySameText : ∀ {first second} (firstValid : Stored.KeyValid first) (secondValid : Stored.KeyValid second) →
  first ≡ second → text firstValid ≡ text secondValid
sameKeySameText firstValid secondValid same = Unicode.representsUnique
  (Unicode.transfer (Decoded.represents (Stored.KeyValid.values firstValid))
    (UTF8.sameBytesSameRawValues (Stored.KeyValid.values firstValid) (Stored.KeyValid.values secondValid)
      (byteNumbersInjective (UTF8.encode (Stored.KeyValid.values firstValid)) (UTF8.encode (Stored.KeyValid.values secondValid))
      (trans (sym (Stored.KeyValid.exact firstValid)) (trans same (Stored.KeyValid.exact secondValid))))))
  (Decoded.represents (Stored.KeyValid.values secondValid))

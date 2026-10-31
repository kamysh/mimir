{-# OPTIONS --safe #-}
-- Reconcile the scalar-sequence parser cursor with Rust &str byte offsets.
-- Validity and all bytes are preserved on success and on failure alike.
module Mimir.UnicodeCursorBytes where

open import Data.List using ([]; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; length-++-≤ˡ)
open import Data.List.Relation.Unary.All using ([]; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat using (_≤_)
open import Data.Char using (toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text; byteLength)
import Mimir.UnicodeText as Unicode
import Mimir.UnicodeChecksum as Checksum
import Mimir.UTF8Text as UTF8
import Mimir.UTF8Packet as Packet
import Mimir.UnicodeScalar as Scalar
open import Mimir.Bits using (Byte)
import Mimir.DecodedText as Decoded
import Mimir.DecodedTextByteLength as Length
import Mimir.DecodedKey as Key
import Mimir.UnicodeParser as U
module Raw = U.Raw

encoded : ∀ text → Unicode.Valid text → Data.List.List Byte
encoded text valid = UTF8.encode (Unicode.encodeValues valid)

encodedLength : ∀ text valid → byteLength text ≡ length (encoded text valid)
encodedLength text valid = trans (cong byteLength (sym (Decoded.roundTrip valid)))
  (Length.exactByteLength (Unicode.encodeValues valid))

decodedEncoding : ∀ values → encoded (Decoded.text values) (Decoded.valid values) ≡ UTF8.encode values
decodedEncoding values = Key.rawDeterminesBytes (Unicode.encodeValues (Decoded.valid values)) values
  (Key.textDeterminesRaw (Unicode.encodeValues (Decoded.valid values)) values (Decoded.roundTrip (Decoded.valid values)))

decodedBytesExact : ∀ {input} (decodedInput : UTF8.Decoded input) →
  encoded (Decoded.text (UTF8.Decoded.values decodedInput)) (Decoded.valid (UTF8.Decoded.values decodedInput)) ≡ input
decodedBytesExact decodedInput = trans (decodedEncoding (UTF8.Decoded.values decodedInput)) (sym (UTF8.Decoded.exact decodedInput))

appendBytes : ∀ first second (valid : Unicode.Valid (first ++ second)) →
  encoded (first ++ second) valid ≡ encoded first (All.++⁻ˡ first valid) ++ encoded second (All.++⁻ʳ first valid)
appendBytes [] second valid = refl
appendBytes (char ∷ rest) second (head ∷ tail) =
  trans (cong (Packet.encode (Packet.Scalar.raw (Scalar.Encoded.value (Scalar.encode (toℕ char) head))) ++_)
    (appendBytes rest second tail))
    (sym (++-assoc _ (encoded rest (All.++⁻ˡ rest tail)) (encoded second (All.++⁻ʳ rest tail))))

consumedValid : ∀ {A input} (result : Raw.Result A input) → Unicode.Valid input → Unicode.Valid (Raw.consumed result)
consumedValid result valid = U.Keep.prefix _ (Raw.consumed result) (Raw.remaining result) (Raw.reconstruct result) valid

conservation : ∀ {A input} (result : Raw.Result A input) valid →
  encoded input valid ≡ encoded (Raw.consumed result) (consumedValid result valid) ++
    encoded (Raw.remaining result) (U.remainingValid result valid)
conservation (Raw.success value before after refl) valid = appendBytes before after valid
conservation (Raw.failure code before after refl) valid = appendBytes before after valid

offsetBound : ∀ {A input} (result : Raw.Result A input) valid → byteLength (Raw.consumed result) ≤ length (encoded input valid)
offsetBound {input = input} result valid = subst (λ prefix → prefix ≤ length (encoded input valid))
  (sym (encodedLength (Raw.consumed result) (consumedValid result valid)))
  (subst (λ input → length (encoded (Raw.consumed result) (consumedValid result valid)) ≤ length input)
    (sym (conservation result valid)) (length-++-≤ˡ (encoded (Raw.consumed result) (consumedValid result valid))))

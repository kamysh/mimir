{-# OPTIONS --safe #-}
-- Connect valid lossy-rendered bytes to the established Agda Char model.
-- Character construction uses the checked full scalar conversion boundary.
module Mimir.UTF8LossyText where

open import Data.List using (List; length)
open import Data.Nat using (_≤_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.Text as Text
import Mimir.UnicodeText as Unicode
import Mimir.DecodedText as Decoded
import Mimir.UnicodeCursorBytes as Cursor
import Mimir.UTF8Text as UTF8
import Mimir.UTF8LossyBytes as Bytes
import Mimir.UTF8LossyValid as Valid
import Mimir.UTF8LossyIdentity as Identity

text : List Byte → Text.Text
text input = Decoded.text (UTF8.Decoded.values (Valid.decoded input))

valid : ∀ input → Unicode.Valid (text input)
valid input = Decoded.valid (UTF8.Decoded.values (Valid.decoded input))

bytesExact : ∀ input → Cursor.encoded (text input) (valid input) ≡ Bytes.decode input
bytesExact input = Cursor.decodedBytesExact (Valid.decoded input)

byteLengthExact : ∀ input → Text.byteLength (text input) ≡ length (Bytes.decode input)
byteLengthExact input = trans (Cursor.encodedLength (text input) (valid input)) (cong length (bytesExact input))

byteBound : ∀ input → Text.byteLength (text input) ≤ 3 * length input
byteBound input = subst (_≤ 3 * length input) (sym (byteLengthExact input)) (Bytes.decodedBound input)

sourceUnchanged : ∀ source (admitted : Unicode.Valid source) → text (Cursor.encoded source admitted) ≡ source
sourceUnchanged source admitted = Unicode.representsUnique
  (Unicode.transfer (Decoded.represents actual)
    (UTF8.sameBytesSameRawValues actual expected encodedEqual))
  (Unicode.encodingRepresentsText admitted)
  where
  actual = UTF8.Decoded.values (Valid.decoded (Cursor.encoded source admitted))
  expected = Unicode.encodeValues admitted
  encodedEqual : UTF8.encode actual ≡ UTF8.encode expected
  encodedEqual = trans (sym (UTF8.Decoded.exact (Valid.decoded (Cursor.encoded source admitted))))
    (Identity.encodedUnchanged expected)

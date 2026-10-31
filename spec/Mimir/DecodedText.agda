{-# OPTIONS --safe #-}
-- Total scalar-to-schema text conversion, with exact scalar identity and
-- round-trip preservation of every admitted Unicode text.
module Mimir.DecodedText where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
import Mimir.Text as Text
import Mimir.UnicodeText as Unicode
import Mimir.UnicodeScalar as Scalar
import Mimir.UTF8Packet as Packet
import Mimir.ScalarCharacter as Character

text : List Packet.Scalar → Text.Text
text = map Character.character

represents : ∀ values → Unicode.Represents (text values) values
represents [] = Unicode.empty
represents (value ∷ rest) = Unicode.more (Character.exact value) (represents rest)

valid : ∀ values → Unicode.Valid (text values)
valid [] = All.[]
valid (value ∷ rest) = subst Scalar.Valid (sym (Character.exact value))
  (proj₂ (Packet.Scalar.canonical value)) All.∷ valid rest

roundTrip : ∀ {original} (admitted : Unicode.Valid original) →
  text (Unicode.encodeValues admitted) ≡ original
roundTrip admitted = Unicode.representsUnique (represents (Unicode.encodeValues admitted))
  (Unicode.encodingRepresentsText admitted)

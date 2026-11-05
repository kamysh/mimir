{-# OPTIONS --safe #-}
-- Lexical JSON string grammar over bytes, followed by validation of the
-- assembled decoded bytes. UTF-8 validation is deliberately not performed
-- before escape parsing reaches the closing quote.
module Mimir.JsonString where

open import Data.Fin using (#_; toℕ; _≟_)
open import Data.List using (List; []; _∷_; _++_; length)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (_≤_; _≤?_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable.Core using (_×-dec_; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)
open import Mimir.Bits using (Byte)
import Mimir.JsonEscape as Escape
import Mimir.UnicodeScalar as Number
import Mimir.UTF8Packet as Packet
import Mimir.UTF8Text as UTF8

Literal : Byte → Set
Literal byte = 32 ≤ toℕ byte × (byte ≢ (# 34) × byte ≢ (# 92))

literal? : ∀ byte → Dec (Literal byte)
literal? byte = (32 ≤? toℕ byte) ×-dec (¬? (byte ≟ (# 34)) ×-dec ¬? (byte ≟ (# 92)))

data Atom : Set where
  literal : Byte → Atom
  escaped : Escape.Raw → Atom

Valid : Atom → Set
Valid (literal byte) = Literal byte
Valid (escaped raw) = Escape.Valid raw

spell : Atom → List Byte
spell (literal byte) = byte ∷ []
spell (escaped raw) = (# 92) ∷ Escape.spell raw

output : ∀ atom → Valid atom → List Byte
output (literal byte) valid = byte ∷ []
output (escaped raw) valid = Packet.encode (Packet.Scalar.raw (Number.Encoded.value (Escape.encode raw valid)))

outputIndependent : ∀ atom first second → output atom first ≡ output atom second
outputIndependent (literal byte) first second = refl
outputIndependent (escaped raw) first second =
  cong (λ valid → Packet.encode (Packet.Scalar.raw (Number.Encoded.value (Number.encode (Escape.number raw) valid))))
    (Number.validIrrelevant (Escape.number raw) (Escape.numberValid raw first) (Escape.numberValid raw second))

spellPositive : ∀ atom → 1 ≤ length (spell atom)
spellPositive (literal byte) = s≤s z≤n
spellPositive (escaped raw) = s≤s z≤n

Body = List Atom
ValidBody = All Valid

-- Includes the closing quotation mark, but not the opening one.
spellBody : Body → List Byte
spellBody [] = (# 34) ∷ []
spellBody (atom ∷ rest) = spell atom ++ spellBody rest

spellString : Body → List Byte
spellString body = (# 34) ∷ spellBody body

bodyOutput : ∀ body → ValidBody body → List Byte
bodyOutput [] All.[] = []
bodyOutput (atom ∷ rest) (valid All.∷ remaining) = output atom valid ++ bodyOutput rest remaining

bodyOutputIndependent : ∀ body first second → bodyOutput body first ≡ bodyOutput body second
bodyOutputIndependent [] All.[] All.[] = refl
bodyOutputIndependent (atom ∷ rest) (valid All.∷ remaining) (other All.∷ others) =
  cong₂ _++_ (outputIndependent atom valid other) (bodyOutputIndependent rest remaining others)

record StringValue : Set where
  constructor stringValue
  field
    body : Body
    valid : ValidBody body
    decoded : UTF8.Decoded (bodyOutput body valid)

values : StringValue → List Packet.Scalar
values value = UTF8.Decoded.values (StringValue.decoded value)

assembledExactly : ∀ value → bodyOutput (StringValue.body value) (StringValue.valid value) ≡ UTF8.encode (values value)
assembledExactly value = UTF8.Decoded.exact (StringValue.decoded value)

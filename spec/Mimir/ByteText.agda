{-# OPTIONS --safe #-}
-- A byte-to-character bridge for lexical parsers, not a UTF-8 decoder. It
-- represents each byte by its same-number Latin-1 character. The inverse law
-- is proved over the entire 256-element domain by constructive finite decision.
module Mimir.ByteText where

open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (all?; toℕ-injective; toℕ-fromℕ<; toℕ<n)
import Data.Char as Char
open import Data.Char.Properties using () renaming (toℕ-injective to charInjective)
open import Data.List using (List; []; _∷_; map)
import Data.List.Properties
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (_<_; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import Mimir.Bits using (Byte)

character : Byte → Char.Char
character byte = Char.fromℕ (toℕ byte)

abstract
  characterNumber : ∀ byte → Char.toℕ (character byte) ≡ toℕ byte
  characterNumber = toWitness {a? = all? (λ byte → Char.toℕ (character byte) ≟ toℕ byte)} tt

characterInjective : ∀ first second → character first ≡ character second → first ≡ second
characterInjective first second same = toℕ-injective
  (trans (Relation.Binary.PropositionalEquality.sym (characterNumber first))
    (trans (cong Char.toℕ same) (characterNumber second)))

Bounded : Char.Char → Set
Bounded char = Char.toℕ char < 256

byte : ∀ char → Bounded char → Byte
byte char valid = fromℕ< valid

byteCharacter : ∀ char valid → character (byte char valid) ≡ char
byteCharacter char valid = charInjective _ _
  (trans (characterNumber (byte char valid)) (toℕ-fromℕ< valid))

characterBounded : ∀ value → Bounded (character value)
characterBounded value rewrite characterNumber value = toℕ<n value

characterByte : ∀ value valid → byte (character value) valid ≡ value
characterByte value valid = toℕ-injective (trans (toℕ-fromℕ< valid) (characterNumber value))

text : List Byte → List Char.Char
text = map character

textBounded : ∀ values → All Bounded (text values)
textBounded [] = All.[]
textBounded (value ∷ rest) = characterBounded value All.∷ textBounded rest

bytes : ∀ chars → All Bounded chars → List Byte
bytes [] All.[] = []
bytes (char ∷ rest) (valid All.∷ remaining) = byte char valid ∷ bytes rest remaining

textBytes : ∀ chars valid → text (bytes chars valid) ≡ chars
textBytes [] All.[] = refl
textBytes (char ∷ rest) (valid All.∷ remaining) rewrite byteCharacter char valid | textBytes rest remaining = refl

bytesText : ∀ values valid → bytes (text values) valid ≡ values
bytesText [] All.[] = refl
bytesText (value ∷ rest) (valid All.∷ remaining) rewrite characterByte value valid | bytesText rest remaining = refl

textInjective : ∀ first second → text first ≡ text second → first ≡ second
textInjective [] [] same = refl
textInjective [] (_ ∷ _) ()
textInjective (_ ∷ _) [] ()
textInjective (first ∷ rest) (second ∷ tail) same = cong₂ _∷_
  (characterInjective first second (Data.List.Properties.∷-injectiveˡ same))
  (textInjective rest tail (Data.List.Properties.∷-injectiveʳ same))

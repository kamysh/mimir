{-# OPTIONS --safe #-}
-- Canonical unsigned bytes select the numeric token and cannot start with space.
import Mimir.FloatConversion
module Mimir.SerdeNumberStart (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (∷-injectiveˡ)
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Empty using (⊥)
open import Mimir.Bits using (Byte)
import Mimir.ByteText as Wire
import Mimir.JsonNumberWire as Encoding
import Mimir.JsonIntegerWriter as Writer
import Mimir.NatDecimal as Decimal
import Mimir.Unsigned as D
import Mimir.JsonTreeParser as TokensDependency
private
  module Tokens = TokensDependency floatConversion
import Mimir.JsonWhitespace as White

digitToken : ∀ digit → Tokens.classify (Wire.byte (D.character digit) (Encoding.digitBounded digit)) ≡ Tokens.numberToken
digitToken D.d0 = refl
digitToken D.d1 = refl
digitToken D.d2 = refl
digitToken D.d3 = refl
digitToken D.d4 = refl
digitToken D.d5 = refl
digitToken D.d6 = refl
digitToken D.d7 = refl
digitToken D.d8 = refl
digitToken D.d9 = refl

characterToken : ∀ byte digit → Wire.character byte ≡ D.character digit → Tokens.classify byte ≡ Tokens.numberToken
characterToken byte digit same = trans
  (cong Tokens.classify
   (Wire.characterInjective byte
    (Wire.byte (D.character digit) (Encoding.digitBounded digit))
    (trans same
     (sym
      (Wire.byteCharacter (D.character digit)
       (Encoding.digitBounded digit))))))
  (digitToken digit)

notSpace : ∀ byte → Tokens.classify byte ≡ Tokens.numberToken → White.Space byte → ⊥
notSpace byte () White.sp
notSpace byte () White.ht
notSpace byte () White.lf
notSpace byte () White.cr

record Starts (input : List Byte) : Set where
  constructor starts
  field
    first : Byte
    rest : List Byte
    exact : input ≡ first ∷ rest
    classified : Tokens.classify first ≡ Tokens.numberToken

fromText : ∀ input digit tail → Wire.text input ≡ D.character digit ∷ tail → Starts input
fromText (byte ∷ input) digit tail same = starts byte input refl
  (characterToken byte digit (∷-injectiveˡ same))

unsigned : ∀ number → Starts (Encoding.spell (Writer.form (+ number)))
unsigned number = fromText (Encoding.spell (Writer.form (+ number)))
  (Decimal.Decimal.head (Decimal.encode number))
  (map D.character (Decimal.Decimal.tail (Decimal.encode number)))
  (trans (Encoding.Prefix.spellingText (Writer.form (+ number)))
   (Writer.spelling (+ number)))

append : ∀ {input} → Starts input → ∀ suffix → Starts (input ++ suffix)
append (starts first rest refl classified) suffix = starts first (rest ++ suffix) refl classified

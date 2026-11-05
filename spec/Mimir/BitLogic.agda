{-# OPTIONS --safe #-}
module Mimir.BitLogic where

open import Data.Vec using ([]; _∷_; map; zipWith)
open import Data.Fin using (toℕ)
open import Data.Nat using (_+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Mimir.Bits using (Bit; Word; O; I)

invert : Bit → Bit
invert O = I
invert I = O

and or xor : Bit → Bit → Bit
and O other = O
and I other = other
or O other = other
or I other = I
xor O other = other
xor I other = invert other

choose : Bit → Bit → Bit → Bit
choose O second third = third
choose I second third = second

majority : Bit → Bit → Bit → Bit
majority O O third = O
majority O I third = third
majority I O third = third
majority I I third = I

chooseXor : ∀ first second third → xor third (and first (xor second third)) ≡ choose first second third
chooseXor O O O = refl
chooseXor O O I = refl
chooseXor O I O = refl
chooseXor O I I = refl
chooseXor I O O = refl
chooseXor I O I = refl
chooseXor I I O = refl
chooseXor I I I = refl

chooseMasks : ∀ first second third → xor (and first second) (and (invert first) third) ≡ choose first second third
chooseMasks O second third = refl
chooseMasks I O third = refl
chooseMasks I I third = refl

majorityXor : ∀ first second third →
  xor (xor (and first second) (and first third)) (and second third) ≡ majority first second third
majorityXor O O third = refl
majorityXor O I third = refl
majorityXor I O O = refl
majorityXor I O I = refl
majorityXor I I O = refl
majorityXor I I I = refl

fullAdder : ∀ first second carry →
  toℕ (xor (xor first second) carry) + toℕ (majority first second carry) * 2 ≡ toℕ first + toℕ second + toℕ carry
fullAdder O O O = refl
fullAdder O O I = refl
fullAdder O I O = refl
fullAdder O I I = refl
fullAdder I O O = refl
fullAdder I O I = refl
fullAdder I I O = refl
fullAdder I I I = refl

wordAnd wordOr wordXor : ∀ {width} → Word width → Word width → Word width
wordAnd = zipWith and
wordOr = zipWith or
wordXor = zipWith xor

wordNot : ∀ {width} → Word width → Word width
wordNot = map invert

orComm : ∀ first second → or first second ≡ or second first
orComm O O = refl
orComm O I = refl
orComm I O = refl
orComm I I = refl

wordOrComm : ∀ {width} (first second : Word width) → wordOr first second ≡ wordOr second first
wordOrComm [] [] = refl
wordOrComm (a ∷ first) (b ∷ second) = cong₂ _∷_ (orComm a b) (wordOrComm first second)

wordChoose wordMajority : ∀ {width} → Word width → Word width → Word width → Word width
wordChoose [] [] [] = []
wordChoose (a ∷ first) (b ∷ second) (c ∷ third) = choose a b c ∷ wordChoose first second third
wordMajority [] [] [] = []
wordMajority (a ∷ first) (b ∷ second) (c ∷ third) = majority a b c ∷ wordMajority first second third

wordChooseXor : ∀ {width} (first second third : Word width) →
  wordXor third (wordAnd first (wordXor second third)) ≡ wordChoose first second third
wordChooseXor [] [] [] = refl
wordChooseXor (a ∷ first) (b ∷ second) (c ∷ third) = cong₂ _∷_ (chooseXor a b c) (wordChooseXor first second third)

wordChooseMasks : ∀ {width} (first second third : Word width) →
  wordXor (wordAnd first second) (wordAnd (wordNot first) third) ≡ wordChoose first second third
wordChooseMasks [] [] [] = refl
wordChooseMasks (a ∷ first) (b ∷ second) (c ∷ third) = cong₂ _∷_ (chooseMasks a b c) (wordChooseMasks first second third)

wordMajorityXor : ∀ {width} (first second third : Word width) →
  wordXor (wordXor (wordAnd first second) (wordAnd first third)) (wordAnd second third) ≡ wordMajority first second third
wordMajorityXor [] [] [] = refl
wordMajorityXor (a ∷ first) (b ∷ second) (c ∷ third) = cong₂ _∷_ (majorityXor a b c) (wordMajorityXor first second third)

{-# OPTIONS --safe #-}
-- Full finite-domain proof of Agda's scalar-to-Char conversion. The closed
-- computations are checked by Agda; they are not postulates or runtime tests.
module Mimir.ScalarCharacter where

import Data.Char as Char
open import Data.Bool using (Bool; true; T)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; _≟_; _<?_; _≤_; _<_; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (≮⇒≥; ≡ᵇ⇒≡)
open import Data.Product using (proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (does; yes; no)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
import Mimir.UnicodeScalar as Scalar
import Mimir.UTF8Packet as Packet
import Mimir.FiniteBooleanRange as Range
open import Mimir.ScalarCharacterCheck using (testSound; module C)
import Mimir.ScalarCharacter.Plane0 as P0
import Mimir.ScalarCharacter.Plane1 as P1
import Mimir.ScalarCharacter.Plane2 as P2
import Mimir.ScalarCharacter.Plane3 as P3
import Mimir.ScalarCharacter.Plane4 as P4
import Mimir.ScalarCharacter.Plane5 as P5
import Mimir.ScalarCharacter.Plane6 as P6
import Mimir.ScalarCharacter.Plane7 as P7
import Mimir.ScalarCharacter.Plane8 as P8
import Mimir.ScalarCharacter.Plane9 as P9
import Mimir.ScalarCharacter.Plane10 as P10
import Mimir.ScalarCharacter.Plane11 as P11
import Mimir.ScalarCharacter.Plane12 as P12
import Mimir.ScalarCharacter.Plane13 as P13
import Mimir.ScalarCharacter.Plane14 as P14
import Mimir.ScalarCharacter.Plane15 as P15
import Mimir.ScalarCharacter.Plane16 as P16

Coverage : ℕ → ℕ → Set
Coverage width start = ∀ number → start ≤ number → number < start + Range.span width →
  Scalar.Valid number → Char.toℕ (Char.fromℕ number) ≡ number

cover : ∀ width start → T (C.all width start) → Coverage width start
cover width start checked number lower upper valid = testSound number valid (C.every width start checked number lower upper)

joinCoverage : ∀ width start → Coverage width start → Coverage width (start + Range.span width) →
  Coverage (Data.Nat.suc width) start
joinCoverage width start first second number lower upper valid with number <? start + Range.span width
... | yes left = first number lower left valid
... | no right = second number (≮⇒≥ right) (subst (number <_) (Range.rangeEnd start width) upper) valid

abstract
  firstBlock : Coverage 20 0
  firstBlock = joinCoverage 19 0
    (joinCoverage 18 0
      (joinCoverage 17 0 (joinCoverage 16 0 (cover 16 0 P0.checked) (cover 16 65536 P1.checked))
        (joinCoverage 16 131072 (cover 16 131072 P2.checked) (cover 16 196608 P3.checked)))
      (joinCoverage 17 262144 (joinCoverage 16 262144 (cover 16 262144 P4.checked) (cover 16 327680 P5.checked))
        (joinCoverage 16 393216 (cover 16 393216 P6.checked) (cover 16 458752 P7.checked))))
    (joinCoverage 18 524288
      (joinCoverage 17 524288 (joinCoverage 16 524288 (cover 16 524288 P8.checked) (cover 16 589824 P9.checked))
        (joinCoverage 16 655360 (cover 16 655360 P10.checked) (cover 16 720896 P11.checked)))
      (joinCoverage 17 786432 (joinCoverage 16 786432 (cover 16 786432 P12.checked) (cover 16 851968 P13.checked))
        (joinCoverage 16 917504 (cover 16 917504 P14.checked) (cover 16 983040 P15.checked))))

  lastBlock : Coverage 16 1048576
  lastBlock = cover 16 1048576 P16.checked

  characterNumber : ∀ number → Scalar.Valid number → Char.toℕ (Char.fromℕ number) ≡ number
  characterNumber number valid with number <? 1048576
  ... | yes low = firstBlock number z≤n low valid
  ... | no high = lastBlock number (≮⇒≥ high) (s≤s (proj₁ valid)) valid

character : Packet.Scalar → Char.Char
character value = Char.fromℕ (Packet.codePoint (Packet.Scalar.raw value))

exact : ∀ value → Char.toℕ (character value) ≡ Packet.codePoint (Packet.Scalar.raw value)
exact value = characterNumber (Packet.codePoint (Packet.Scalar.raw value)) (proj₂ (Packet.Scalar.canonical value))

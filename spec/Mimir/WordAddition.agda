{-# OPTIONS --safe #-}
-- An executable ripple-carry word adder with a general integer conservation
-- law. Discarding the final carry is exactly unsigned wrapping addition.
module Mimir.WordAddition where

open import Data.Vec using ([]; _∷_)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; _+_; _*_; _%_; NonZero)
open import Data.Nat.Properties using (*-identityʳ; +-identityʳ; +-comm; +-assoc)
open import Data.Nat.DivMod using ([m+kn]%n≡m%n; m<n⇒m%n≡m; %-distribˡ-+)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Mimir.Bits using (Bit; Word; O; module Binary)
open import Mimir.BitLogic using (xor; majority; fullAdder)
import Mimir.WordEncoding as Encoding

addCarry : ∀ {width} → Bit → Word width → Word width → Word width × Bit
addCarry carry [] [] = [] , carry
addCarry carry (a ∷ first) (b ∷ second) with addCarry (majority a b carry) first second
... | result , overflow = (xor (xor a b) carry ∷ result) , overflow

gather : ∀ low tail carry power → low + tail * 2 + carry * (power * 2) ≡ low + (tail + carry * power) * 2
gather = solve 4 (λ low tail carry power →
  low :+ tail :* con 2 :+ carry :* (power :* con 2) := low :+ (tail :+ carry :* power) :* con 2) refl

splay : ∀ low first second carry → low + (first + second + carry) * 2 ≡ (low + carry * 2) + (first + second) * 2
splay = solve 4 (λ low first second carry →
  low :+ (first :+ second :+ carry) :* con 2 := (low :+ carry :* con 2) :+ (first :+ second) :* con 2) refl

spread : ∀ a b carry first second → (a + b + carry) + (first + second) * 2 ≡ (a + first * 2) + (b + second * 2) + carry
spread = solve 5 (λ a b carry first second →
  (a :+ b :+ carry) :+ (first :+ second) :* con 2 := (a :+ first :* con 2) :+ (b :+ second :* con 2) :+ carry) refl

conservation : ∀ {width} carry (first second : Word width) →
  Binary.value (proj₁ (addCarry carry first second)) + toℕ (proj₂ (addCarry carry first second)) * Binary.power width ≡
  Binary.value first + Binary.value second + toℕ carry
conservation carry [] [] = *-identityʳ (toℕ carry)
conservation {Data.Nat.suc width} carry (a ∷ first) (b ∷ second)
  with addCarry (majority a b carry) first second | conservation (majority a b carry) first second
... | result , overflow | induction =
  trans (gather (toℕ (xor (xor a b) carry)) (Binary.value result) (toℕ overflow) (Binary.power width))
  (trans (cong (λ tail → toℕ (xor (xor a b) carry) + tail * 2) induction)
  (trans (splay (toℕ (xor (xor a b) carry)) (Binary.value first) (Binary.value second) (toℕ (majority a b carry)))
  (trans (cong (λ low → low + (Binary.value first + Binary.value second) * 2) (fullAdder a b carry))
    (spread (toℕ a) (toℕ b) (toℕ carry) (Binary.value first) (Binary.value second)))))

add : ∀ {width} → Word width → Word width → Word width
add first second = proj₁ (addCarry O first second)

wrappingValue : ∀ {width} .{{nz : NonZero (Binary.power width)}} (first second : Word width) →
  Binary.value (add first second) ≡ (Binary.value first + Binary.value second) % Binary.power width
wrappingValue {width} first second =
  trans (sym (m<n⇒m%n≡m (Binary.valueBound (add first second))))
  (trans (sym ([m+kn]%n≡m%n (Binary.value (add first second))
    (toℕ (proj₂ (addCarry O first second))) (Binary.power width)))
    (cong (_% Binary.power width) (trans (conservation O first second)
      (+-identityʳ (Binary.value first + Binary.value second)))))

commutative : ∀ {width} .{{nz : NonZero (Binary.power width)}} (first second : Word width) → add first second ≡ add second first
commutative {width} first second = Binary.valueInjective (add first second) (add second first)
  (trans (wrappingValue first second)
    (trans (cong (_% Binary.power width) (+-comm (Binary.value first) (Binary.value second)))
      (sym (wrappingValue second first))))

addEncoded : ∀ width → .{{nz : NonZero (Binary.power width)}} → ∀ first second →
  add (Encoding.encode width first) (Encoding.encode width second) ≡ Encoding.encode width (first + second)
addEncoded width first second = Binary.valueInjective _ _
  (trans (wrappingValue (Encoding.encode width first) (Encoding.encode width second))
  (trans (cong₂ (λ a b → (a + b) % Binary.power width) (Encoding.value width first) (Encoding.value width second))
  (trans (sym (%-distribˡ-+ first second (Binary.power width)))
    (sym (Encoding.value width (first + second))))))

addAsEncoded : ∀ {width} → .{{nz : NonZero (Binary.power width)}} → (first second : Word width) →
  add first second ≡ Encoding.encode width (Binary.value first + Binary.value second)
addAsEncoded {width} first second = Binary.valueInjective _ _
  (trans (wrappingValue first second) (sym (Encoding.value width (Binary.value first + Binary.value second))))

associative : ∀ {width} → .{{nz : NonZero (Binary.power width)}} → (first second third : Word width) →
  add (add first second) third ≡ add first (add second third)
associative {width} first second third =
  trans (cong₂ add (addAsEncoded first second) (sym (Encoding.roundTrip third)))
  (trans (addEncoded width (Binary.value first + Binary.value second) (Binary.value third))
  (trans (cong (Encoding.encode width) (+-assoc (Binary.value first) (Binary.value second) (Binary.value third)))
  (trans (sym (addEncoded width (Binary.value first) (Binary.value second + Binary.value third)))
    (cong₂ add (Encoding.roundTrip first) (sym (addAsEncoded second third))))))

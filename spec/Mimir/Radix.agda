{-# OPTIONS --safe #-}
-- Fixed-width, least-significant-first positional representation. Symbolic
-- radix/width proofs are shared by byte, Unicode and bit-field encodings.
module Mimir.Radix where

open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n; toℕ-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _/_; _%_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-monoˡ-<; *-monoˡ-≤; <-≤-trans;
  +-assoc; *-assoc; *-identityʳ; *-distribʳ-+)
open import Data.Nat.DivMod using (_divMod_; _mod_; DivMod; m<n*o⇒m/o<n;
  [m+kn]%n≡m%n; m<n⇒m%n≡m; +-distrib-/-∣ʳ; m<n⇒m/n≡0; m*n/n≡m)
open import Data.Nat.Divisibility.Core using (divides)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

module Base (baseMinusOne : ℕ) where
  radix : ℕ
  radix = suc baseMinusOne

  power : ℕ → ℕ
  power zero = 1
  power (suc width) = power width * radix

  value : ∀ {width} → Vec (Fin radix) width → ℕ
  value [] = 0
  value (digit ∷ rest) = toℕ digit + value rest * radix

  valueBound : ∀ {width} (digits : Vec (Fin radix) width) → value digits < power width
  valueBound [] = s≤s z≤n
  valueBound (digit ∷ rest) = <-≤-trans
    (+-monoˡ-< (value rest * radix) (toℕ<n digit))
    (*-monoˡ-≤ radix (valueBound rest))

  record Expansion (width number : ℕ) : Set where
    constructor expansion
    field digits : Vec (Fin radix) width; exact : value digits ≡ number

  encode : ∀ width number → number < power width → Expansion width number
  encode zero zero bound = expansion [] refl
  encode zero (suc number) (s≤s ())
  encode (suc width) number bound with encode width (number / radix)
    (m<n*o⇒m/o<n {m = number} {n = power width} {o = radix} bound)
  ... | expansion digits exact = expansion ((number mod radix) ∷ digits)
      (trans (cong (λ high → toℕ (number mod radix) + high * radix) exact)
        (sym (DivMod.property (number divMod radix))))

  lowDigit : ∀ {width} (digit : Fin radix) (rest : Vec (Fin radix) width) →
    value (digit ∷ rest) % radix ≡ toℕ digit
  lowDigit digit rest = trans ([m+kn]%n≡m%n (toℕ digit) (value rest) radix)
    (m<n⇒m%n≡m {n = radix} {m = toℕ digit} (toℕ<n digit))

  highDigits : ∀ {width} (digit : Fin radix) (rest : Vec (Fin radix) width) →
    value (digit ∷ rest) / radix ≡ value rest
  highDigits digit rest = trans
    (+-distrib-/-∣ʳ (toℕ digit) {n = value rest * radix} {d = radix} (divides (value rest) refl))
    (cong₂ _+_ (m<n⇒m/n≡0 {m = toℕ digit} {n = radix} (toℕ<n digit))
      (m*n/n≡m (value rest) radix))

  valueInjective : ∀ {width} (first second : Vec (Fin radix) width) →
    value first ≡ value second → first ≡ second
  valueInjective [] [] equal = refl
  valueInjective (first ∷ rest) (second ∷ tail) equal = cong₂ _∷_
    (toℕ-injective (trans (sym (lowDigit first rest))
      (trans (cong (_% radix) equal) (lowDigit second tail))))
    (valueInjective rest tail (trans (sym (highDigits first rest))
      (trans (cong (_/ radix) equal) (highDigits second tail))))

  decodeEncode : ∀ width number bound → value (Expansion.digits (encode width number bound)) ≡ number
  decodeEncode width number bound = Expansion.exact (encode width number bound)

  encodeDecode : ∀ {width} (digits : Vec (Fin radix) width) →
    Expansion.digits (encode width (value digits) (valueBound digits)) ≡ digits
  encodeDecode {width} digits = valueInjective _ digits (decodeEncode width (value digits) (valueBound digits))

  abstract
    valueAppend : ∀ {lowWidth highWidth} (low : Vec (Fin radix) lowWidth) (high : Vec (Fin radix) highWidth) →
      value (low ++ high) ≡ value low + value high * power lowWidth
    valueAppend [] high = sym (*-identityʳ (value high))
    valueAppend {suc width} (digit ∷ low) high
      rewrite valueAppend low high |
        *-distribʳ-+ radix (value low) (value high * power width) |
        *-assoc (value high) (power width) radix =
      sym (+-assoc (toℕ digit) (value low * radix) (value high * (power width * radix)))

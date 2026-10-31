{-# OPTIONS --safe #-}
-- UTF-16 hexadecimal escape interpretation used by serde_json String values.
-- This is not serde_json's byte-string/WTF-8 mode, which Mimir does not use
-- for JSON string fields.
module Mimir.UTF16Escape where

open import Data.Nat using (ℕ; _+_; _*_; _∸_; _≤_; _≤?_; _<_; _<?_; s≤s⁻¹; NonZero)
open import Data.Nat.Properties using (≮⇒≥; <-≤-trans; ≤-trans; m≤m+n; m≤n+m;
  m<n+o⇒m∸n<o; +-monoˡ-<; +-comm; ≤-<-trans; <-irrefl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (_++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Mimir.Bits using (Word)
import Mimir.Bits as Bits
import Mimir.UnicodeScalar as Number

Unit = Word 16

value : Unit → ℕ
value = Bits.Binary.value

Leading : ℕ → Set
Leading number = 55296 ≤ number × number < 56320

Trailing : ℕ → Set
Trailing number = 56320 ≤ number × number < 57344

abstract
  padding : ∀ number extra → number ≤ number + extra
  padding = m≤m+n

  offsetFloor : ∀ small gap rest → small ≤ rest + (small + gap)
  offsetFloor small gap rest = ≤-trans (padding small gap) (m≤n+m (small + gap) rest)

  unitUpper : ∀ unit → value unit ≤ 1114111
  unitUpper unit = s≤s⁻¹ (<-≤-trans (Bits.Binary.valueBound unit) (padding 65536 1048576))

data First (unit : Unit) : Set where
  literal : Number.Valid (value unit) → First unit
  needsTrailing : Leading (value unit) → First unit
  loneTrailing : Trailing (value unit) → First unit

classify : ∀ unit → First unit
classify unit with value unit <? 55296
... | yes before = literal (unitUpper unit , inj₁ before)
... | no notBefore with value unit <? 56320
...   | yes leading = needsTrailing (≮⇒≥ notBefore , leading)
...   | no notLeading with value unit <? 57344
...     | yes trailing = loneTrailing (≮⇒≥ notLeading , trailing)
...     | no notTrailing = literal (unitUpper unit , inj₂ (≮⇒≥ notTrailing))

leadingNotValid : ∀ number → Leading number → Number.Valid number → ⊥
leadingNotValid number (lower , upper) (_ , inj₁ before) = <-irrefl refl (≤-<-trans lower before)
leadingNotValid number (lower , upper) (_ , inj₂ after) =
  <-irrefl refl (≤-<-trans (≤-trans (padding 56320 1024) after) upper)

trailingNotValid : ∀ number → Trailing number → Number.Valid number → ⊥
trailingNotValid number (lower , upper) (_ , inj₁ before) =
  <-irrefl refl (≤-<-trans (≤-trans (padding 55296 1024) lower) before)
trailingNotValid number (lower , upper) (_ , inj₂ after) = <-irrefl refl (≤-<-trans after upper)

leadingNotTrailing : ∀ number → Leading number → Trailing number → ⊥
leadingNotTrailing number (_ , upper) (lower , _) = <-irrefl refl (≤-<-trans lower upper)

classifyLiteral : ∀ unit → Number.Valid (value unit) →
  Σ (Number.Valid (value unit)) (λ valid → classify unit ≡ literal valid)
classifyLiteral unit valid with classify unit in observed
... | literal admitted = admitted , refl
... | needsTrailing leading = ⊥-elim (leadingNotValid (value unit) leading valid)
... | loneTrailing trailing = ⊥-elim (trailingNotValid (value unit) trailing valid)

classifyLeading : ∀ unit → Leading (value unit) →
  Σ (Leading (value unit)) (λ leading → classify unit ≡ needsTrailing leading)
classifyLeading unit leading with classify unit in observed
... | literal valid = ⊥-elim (leadingNotValid (value unit) leading valid)
... | needsTrailing admitted = admitted , refl
... | loneTrailing trailing = ⊥-elim (leadingNotTrailing (value unit) leading trailing)

abstract
  offsetWord : ∀ width base number → .{{NonZero (Bits.Binary.power width)}} →
    number < base + Bits.Binary.power width → Word width
  offsetWord width base number bound = Bits.Binary.Expansion.digits
    (Bits.Binary.encode width (number ∸ base)
      (m<n+o⇒m∸n<o number base {o = Bits.Binary.power width} bound))

  offsetValue : ∀ width base number → .{{nz : NonZero (Bits.Binary.power width)}} → ∀ bound →
    Bits.Binary.value (offsetWord width base number {{nz}} bound) ≡ number ∸ base
  offsetValue width base number bound = Bits.Binary.decodeEncode width (number ∸ base)
    (m<n+o⇒m∸n<o number base {o = Bits.Binary.power width} bound)

leadingBits : ∀ number → Leading number → Word 10
leadingBits number bounds = offsetWord 10 55296 number (proj₂ bounds)

trailingBits : ∀ number → Trailing number → Word 10
trailingBits number bounds = offsetWord 10 56320 number (proj₂ bounds)

leadingValue : ∀ number bounds → Bits.Binary.value (leadingBits number bounds) ≡ number ∸ 55296
leadingValue number bounds = offsetValue 10 55296 number (proj₂ bounds)

trailingValue : ∀ number bounds → Bits.Binary.value (trailingBits number bounds) ≡ number ∸ 56320
trailingValue number bounds = offsetValue 10 56320 number (proj₂ bounds)

pairValue : Word 10 → Word 10 → ℕ
pairValue high low = Bits.Binary.value (low ++ high) + 65536

abstract
  pairValid : ∀ high low → Number.Valid (pairValue high low)
  pairValid high low =
    s≤s⁻¹ (+-monoˡ-< 65536 (Bits.Binary.valueBound (low ++ high))) ,
    inj₂ (offsetFloor 57344 8192 (Bits.Binary.value (low ++ high)))

pairFormula : ∀ first leading second trailing →
  pairValue (leadingBits first leading) (trailingBits second trailing) ≡
    ((first ∸ 55296) * 1024 + (second ∸ 56320)) + 65536
pairFormula first leading second trailing
  rewrite Bits.Binary.valueAppend (trailingBits second trailing) (leadingBits first leading) |
    leadingValue first leading | trailingValue second trailing =
  cong (_+ 65536) (+-comm (second ∸ 56320) ((first ∸ 55296) * 1024))

record PairResult (first second : ℕ) : Set where
  constructor pairResult
  field
    encoded : Number.Encoded (((first ∸ 55296) * 1024 + (second ∸ 56320)) + 65536)

combine : ∀ first → Leading first → ∀ second → Trailing second → PairResult first second
combine first leading second trailing = pairResult
  (subst Number.Encoded (pairFormula first leading second trailing)
    (Number.encode (pairValue (leadingBits first leading) (trailingBits second trailing))
      (pairValid (leadingBits first leading) (trailingBits second trailing))))

data PairCheck (first second : Unit) : Set where
  paired : Leading (value first) → Trailing (value second) →
    PairResult (value first) (value second) → PairCheck first second
  invalidFirst : (Leading (value first) → ⊥) → PairCheck first second
  invalidSecond : (Trailing (value second) → ⊥) → PairCheck first second

checkPair : ∀ first second → PairCheck first second
checkPair first second with 55296 ≤? value first
... | no notHigh = invalidFirst (λ valid → notHigh (proj₁ valid))
... | yes startsHigh with value first <? 56320
...   | no notHigh = invalidFirst (λ valid → notHigh (proj₂ valid))
...   | yes endsHigh with 56320 ≤? value second
...     | no notLow = invalidSecond (λ valid → notLow (proj₁ valid))
...     | yes startsLow with value second <? 57344
...       | no notLow = invalidSecond (λ valid → notLow (proj₂ valid))
...       | yes endsLow = paired (startsHigh , endsHigh) (startsLow , endsLow)
          (combine (value first) (startsHigh , endsHigh) (value second) (startsLow , endsLow))

record Accepted (first second : Unit) (result : PairCheck first second) : Set where
  constructor accepted
  field
    leading : Leading (value first)
    trailing : Trailing (value second)
    payload : PairResult (value first) (value second)
    observed : result ≡ paired leading trailing payload

validPairAccepted : ∀ first second → Leading (value first) → Trailing (value second) →
  (result : PairCheck first second) → Accepted first second result
validPairAccepted first second high low (paired leading trailing payload) = accepted leading trailing payload refl
validPairAccepted first second high low (invalidFirst rejected) = ⊥-elim (rejected high)
validPairAccepted first second high low (invalidSecond rejected) = ⊥-elim (rejected low)

checkPairComplete : ∀ first second → Leading (value first) → Trailing (value second) →
  Accepted first second (checkPair first second)
checkPairComplete first second high low = validPairAccepted first second high low (checkPair first second)

invalidFirstNeverAccepted : ∀ first second → (Leading (value first) → ⊥) →
  ∀ result → Accepted first second result → ⊥
invalidFirstNeverAccepted first second rejected result acceptedResult = rejected (Accepted.leading acceptedResult)

invalidSecondNeverAccepted : ∀ first second → (Trailing (value second) → ⊥) →
  ∀ result → Accepted first second result → ⊥
invalidSecondNeverAccepted first second rejected result acceptedResult = rejected (Accepted.trailing acceptedResult)

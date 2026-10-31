{-# OPTIONS --safe #-}
-- Public numeric validation is over the exact value of the received binary64
-- datum. NaNs and infinities are rejected before any comparison or arithmetic.
module Mimir.NumericValidation where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; -_; _≤_)
open import Data.Rational.Properties using (_≤?_; _≟_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Binary64
open import Mimir.Validation

Between : ℚ → ℚ → Number → Set
Between lower upper (finite n) = lower ≤ value n × value n ≤ upper
Between lower upper (nonfinite _ _) = ⊥

checkFinite : ∀ n → Checked (IsFinite n)
checkFinite n = check (fault [] invalidNumber "number must be finite") (isFinite? n)

checkBetween : ∀ lower upper n → Checked (Between lower upper n)
checkBetween lower upper (nonfinite _ _) = rejected
  (fault [] invalidNumber "number must be finite") (λ proof → proof)
checkBetween lower upper (finite n) = combine
  (check (fault [] invalidNumber "number is below the permitted bound") (lower ≤? value n))
  (check (fault [] invalidNumber "number is above the permitted bound") (value n ≤? upper))

IsZero : Number → Set
IsZero (finite n) = value n ≡ 0ℚ
IsZero (nonfinite _ _) = ⊥

checkZero : ∀ n → Checked (IsZero n)
checkZero (nonfinite _ _) = rejected
  (fault [] invalidNumber "unresolved axis must have finite zero weight") (λ proof → proof)
checkZero (finite n) = check
  (fault [] invalidNumber "unresolved axis cannot contribute evidence") (value n ≟ 0ℚ)

record Axis : Set where
  constructor axis
  field estimate : Maybe Number; weight : Number

EstimateValid : ℚ → Maybe Number → Set
EstimateValid lower nothing = ⊤
EstimateValid lower (just n) = Between lower 1ℚ n

checkEstimate : ∀ lower estimate → Checked (EstimateValid lower estimate)
checkEstimate lower nothing = accepted tt
checkEstimate lower (just n) = checkBetween lower 1ℚ n

UnresolvedInert : Axis → Set
UnresolvedInert (axis nothing weight) = IsZero weight
UnresolvedInert (axis (just _) weight) = ⊤

checkInert : ∀ a → Checked (UnresolvedInert a)
checkInert (axis nothing weight) = checkZero weight
checkInert (axis (just _) weight) = accepted tt

AxisValid : ℚ → Axis → Set
AxisValid lower a = Between 0ℚ 1ℚ (Axis.weight a) ×
  (EstimateValid lower (Axis.estimate a) × UnresolvedInert a)

checkAxis : ∀ lower a → Checked (AxisValid lower a)
checkAxis lower a = combine
  (at (key "weight") (checkBetween 0ℚ 1ℚ (Axis.weight a)))
  (combine (at (key "value") (checkEstimate lower (Axis.estimate a)))
    (at (key "weight") (checkInert a)))

unresolvedZero : ∀ lower weight → AxisValid lower (axis nothing weight) → IsZero weight
unresolvedZero lower weight proof = proj₂ (proj₂ proof)

validAxisNeverRejected : ∀ lower a → AxisValid lower a → reported (checkAxis lower a) ≡ []
validAxisNeverRejected lower a proof = noFalseRejection (checkAxis lower a) proof

-- Optional prediction intervals have both endpoints or neither, and contain
-- the point estimate. Nonfinite endpoints cannot establish an interval.
Interval : Number → Maybe Number → Maybe Number → Set
Interval point nothing nothing = ⊤
Interval point nothing (just _) = ⊥
Interval point (just _) nothing = ⊥
Interval (finite p) (just (finite lo)) (just (finite hi)) =
  value lo ≤ value p × value p ≤ value hi
Interval _ _ _ = ⊥

checkInterval : ∀ point lower upper → Checked (Interval point lower upper)
checkInterval point nothing nothing = accepted tt
checkInterval (finite p) (just (finite lo)) (just (finite hi)) = combine
  (check (fault [] invalidInterval "lower bound exceeds prediction") (value lo ≤? value p))
  (check (fault [] invalidInterval "upper bound is below prediction") (value p ≤? value hi))
checkInterval (nonfinite _ _) (just _) (just _) = rejected
  (fault [] invalidNumber "prediction must be finite") (λ proof → proof)
checkInterval (finite _) (just (nonfinite _ _)) (just _) = rejected
  (fault [] invalidNumber "lower bound must be finite") (λ proof → proof)
checkInterval (finite _) (just (finite _)) (just (nonfinite _ _)) = rejected
  (fault [] invalidNumber "upper bound must be finite") (λ proof → proof)
checkInterval _ nothing (just _) = rejected
  (fault [] invalidInterval "interval requires both bounds") (λ proof → proof)
checkInterval _ (just _) nothing = rejected
  (fault [] invalidInterval "interval requires both bounds") (λ proof → proof)

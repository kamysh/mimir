{-# OPTIONS --safe #-}
-- Application score projection using Agda's standard floating operations.
-- No implementation of IEEE arithmetic or formatting belongs here. Native
-- arithmetic correspondence remains distinct from this behavioral definition.
module Mimir.AssessmentScores where

open import Data.Float.Base using (Float; _+_; _*_; _÷_; -_; _≤ᵇ_; _<ᵇ_; isNaN; isInfinite; sqrt)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Totals : Set where
  constructor totals
  field
    positive negative benefit usefulnessMass : Float
    incidents unresolvedCorrectness unresolvedUsefulness : ℤ
open Totals

data Failure : Set where nonfinite negativeMass excessiveBenefit : Failure

finite : Float → Bool
finite x = not (isNaN x ∨ isInfinite x)

absolute : Float → Float
absolute x with x <ᵇ 0.0
... | true = - x
... | false = x

allFinite : Totals → Bool
allFinite t = finite (positive t) ∧ finite (negative t) ∧
  finite (benefit t) ∧ finite (usefulnessMass t)

nonnegative : Totals → Bool
nonnegative t = (0.0 ≤ᵇ positive t) ∧ (0.0 ≤ᵇ negative t) ∧
  (0.0 ≤ᵇ usefulnessMass t)

boundedBenefit : Totals → Bool
boundedBenefit t = absolute (benefit t) ≤ᵇ (usefulnessMass t + 0.000000000001)

record Scores : Set where
  constructor scores
  field
    modelVersion : ℕ
    correctness usefulness alpha beta benefitSum correctnessMass usefulnessMass correctnessSpread : Float
    incidents unresolvedCorrectness unresolvedUsefulness : ℤ
    calibrated : Bool

-- The Beta(1,1) prior applies to correctness. Usefulness has a neutral
-- numerator and one unit of prior denominator. Spread is a standard
-- deviation, not a calibrated confidence interval.
project : Totals → Scores
project t = scores 1 (a ÷ (a + b)) (benefit t ÷ (1.0 + usefulnessMass t))
  a b (benefit t) (positive t + negative t) (usefulnessMass t)
  (sqrt ((a * b) ÷ (((a + b) * (a + b)) * ((a + b) + 1.0))))
  (incidents t) (unresolvedCorrectness t) (unresolvedUsefulness t) false
  where
  a = 1.0 + positive t
  b = 1.0 + negative t

data Result : Set where
  rejected : Failure → Result
  accepted : Scores → Result

calculate : Totals → Result
calculate t with allFinite t
... | false = rejected nonfinite
... | true with nonnegative t
...   | false = rejected negativeMass
...   | true with boundedBenefit t
...     | false = rejected excessiveBenefit
...     | true = accepted (project t)

-- Input validation intentionally does not promise finite derived outputs:
-- finite inputs can overflow intermediate sums/products. This is observable
-- behavior that the interface serialization/failure protocol must handle.
countsPreserved : ∀ t →
  Scores.incidents (project t) ≡ incidents t ×
  (Scores.unresolvedCorrectness (project t) ≡ unresolvedCorrectness t ×
   Scores.unresolvedUsefulness (project t) ≡ unresolvedUsefulness t)
countsPreserved t = refl , refl , refl

neverClaimsCalibration : ∀ t → Scores.calibrated (project t) ≡ false
neverClaimsCalibration t = refl

nonfiniteRejected : ∀ t → allFinite t ≡ false → calculate t ≡ rejected nonfinite
nonfiniteRejected t proof rewrite proof = refl

acceptedIsProjection : ∀ t s → calculate t ≡ accepted s → s ≡ project t
acceptedIsProjection t s proof with allFinite t
... | false with proof
...   | ()
acceptedIsProjection t s proof | true with nonnegative t
... | false with proof
...   | ()
acceptedIsProjection t s proof | true | true with boundedBenefit t
... | false with proof
...   | ()
acceptedIsProjection t s refl | true | true | true = refl

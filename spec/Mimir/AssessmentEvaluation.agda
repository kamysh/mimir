{-# OPTIONS --safe #-}
-- Evaluate the specified immutable write expressions with standard arithmetic,
-- then accumulate the exact application counters used by assessment queries.
module Mimir.AssessmentEvaluation where

open import Data.Float.Base using (Float; _+_; _-_; _*_; _≡ᵇ_)
open import Data.Bool using (true; false; Bool)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _+ℤ_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.AssessmentWrites as Writes
import Mimir.AssessmentScores as Scores
import Mimir.ApplicationFloat as Numeric

term : Writes.Term → Maybe Float
term (Writes.literal x) = Numeric.number x
term Writes.zero = just 0.0
term Writes.one = just 1.0
term (Writes.multiply a b) with term a | term b
... | just x | just y = just (x * y)
... | _ | _ = nothing
term (Writes.subtract a b) with term a | term b
... | just x | just y = just (x - y)
... | _ | _ = nothing

record Mass : Set where
  constructor mass
  field positive negative benefit weight : Float

evaluate : Writes.Values → Maybe Mass
evaluate v with term (Writes.Values.positive v) | term (Writes.Values.negative v)
  | term (Writes.Values.benefit v) | term (Writes.Values.weight v)
... | just p | just n | just b | just w = just (mass p n b w)
... | _ | _ | _ | _ = nothing

count : Bool → ℤ
count true = + 1
count false = + 0

empty : Scores.Totals
empty = Scores.totals 0.0 0.0 0.0 0.0 (+ 0) (+ 0) (+ 0)

add : Mass → Scores.Totals → Scores.Totals
add m t = Scores.totals
  (Scores.Totals.positive t + Mass.positive m)
  (Scores.Totals.negative t + Mass.negative m)
  (Scores.Totals.benefit t + Mass.benefit m)
  (Scores.Totals.usefulnessMass t + Mass.weight m)
  (Scores.Totals.incidents t +ℤ (+ 1))
  (Scores.Totals.unresolvedCorrectness t +ℤ count ((Mass.positive m + Mass.negative m) ≡ᵇ 0.0))
  (Scores.Totals.unresolvedUsefulness t +ℤ count (Mass.weight m ≡ᵇ 0.0))

-- Input order is explicit: floating aggregation is not asserted commutative.
-- SQL may supply any permitted aggregation order; callers cannot rely on a
-- canonical bitwise sum that the database does not promise.
accumulate : Scores.Totals → List Writes.Row → Maybe Scores.Totals
accumulate t [] = just t
accumulate t (entry ∷ rows) with evaluate (Writes.Row.calculated entry)
... | nothing = nothing
... | just m = accumulate (add m t) rows

data Result : Set where
  invalidStoredNumber : Result
  scored : Scores.Result → Result

assess : List Writes.Row → Result
assess rows with accumulate empty rows
... | nothing = invalidStoredNumber
... | just t = scored (Scores.calculate t)

eachRowCountsOnce : ∀ m t →
  Scores.Totals.incidents (add m t) ≡ Scores.Totals.incidents t +ℤ (+ 1)
eachRowCountsOnce m t = refl

emptyRetainsTotals : ∀ t → accumulate t [] ≡ just t
emptyRetainsTotals t = refl

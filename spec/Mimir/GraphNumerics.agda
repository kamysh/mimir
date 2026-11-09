{-# OPTIONS --safe #-}
-- Current public graph numerics. Legacy ideal-rational Beta laws remain in
-- Beta.agda; this module fixes the application's finite operation order.
module Mimir.GraphNumerics where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Float.Base using (Float; fromℤ; _+_; _-_; _*_; _÷_; _**_; _<ᵇ_; _≤ᵇ_)
open import Data.Integer using (ℤ)
import Data.Integer as Int
open import Data.Integer.DivMod using (_/ℕ_)
open import Data.List using (List; []; _∷_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Candidates
import Mimir.RetrievalRanking as Ranking
import Mimir.PosteriorComputation as P
import Mimir.AssessmentScores as Scores
import Mimir.ReviewSchema as Review
import Mimir.EvidenceValidity as Evidence
import Mimir.RetirementClock as Retirement

probability : Float → Bool
probability x = (0.0 ≤ᵇ x) ∧ (x ≤ᵇ 1.0)

activeContradictions : List Graph.BeliefValues → List (ℕ × ℕ) → List (ℕ × ℕ)
activeContradictions beliefs [] = []
activeContradictions beliefs ((a , b) ∷ pairs) with Ranking.lookup a beliefs | Ranking.lookup b beliefs
... | just first | just second with 1.0 <ᵇ
  (Graph.BeliefValues.probability first + Graph.BeliefValues.probability second)
...   | true = (a , b) ∷ activeContradictions beliefs pairs
...   | false = activeContradictions beliefs pairs
activeContradictions beliefs ((a , b) ∷ pairs) | nothing | _ = activeContradictions beliefs pairs
activeContradictions beliefs ((a , b) ∷ pairs) | just first | nothing = activeContradictions beliefs pairs

-- Charge only time not already represented by the current counts. Activation
-- remains independent. Full nanoseconds preserve fractional intervals; an
-- unchanged or earlier clock returns the exact stored pair before any pow.
decayed : ℤ → Float → Float → Graph.BeliefValues → P.Beta
decayed now factor mass belief with does (now Int.≤? baseline)
  where baseline = Graph.BeliefValues.activated belief Int.⊔ Graph.BeliefValues.decayAccountedAt belief
... | true = P.beta (Graph.BeliefValues.alpha belief) (Graph.BeliefValues.beta belief)
... | false = P.beta
  (1.0 + retention * (Graph.BeliefValues.alpha belief - 1.0))
  (1.0 + retention * (Graph.BeliefValues.beta belief - 1.0))
  where
  baseline = Graph.BeliefValues.activated belief Int.⊔ Graph.BeliefValues.decayAccountedAt belief
  days = fromℤ (now Int.- baseline) ÷ 86400000000000.0
  base = factor ** days
  retention = 1.0 - ((1.0 - base) ÷ (1.0 + mass))

noElapsedInterval : ∀ now factor mass belief →
  now Int.≤ (Graph.BeliefValues.activated belief Int.⊔ Graph.BeliefValues.decayAccountedAt belief) →
  decayed now factor mass belief ≡ P.beta (Graph.BeliefValues.alpha belief) (Graph.BeliefValues.beta belief)
noElapsedInterval now factor mass belief accounted
  with now Int.≤? (Graph.BeliefValues.activated belief Int.⊔ Graph.BeliefValues.decayAccountedAt belief)
... | yes _ = refl
... | no notAccounted = ⊥-elim (notAccounted accounted)

decayChanged : Graph.BeliefValues → P.Beta → Bool
decayChanged b value = not (does (P.betaEqual?
  (P.beta (Graph.BeliefValues.alpha b) (Graph.BeliefValues.beta b)) value))

massOf : ℕ → List (ℕ × Float) → Float
massOf id masses with P.lookup id masses
... | nothing = 0.0
... | just mass = mass

decayRows : ℤ → Float → List (ℕ × Float) → List Graph.BeliefValues → Maybe P.State
decayRows now factor masses [] = just []
decayRows now factor masses (b ∷ bs) with Graph.BeliefValues.memory b
... | Candidates.experiential = decayRows now factor masses bs
... | Candidates.working = decayRows now factor masses bs
... | Candidates.fact with Evidence.validBelief b ∧
  Scores.finite (massOf (Graph.BeliefValues.identity b) masses) ∧
  (0.0 ≤ᵇ massOf (Graph.BeliefValues.identity b) masses) ∧
  P.validCounts (decayed now factor (massOf (Graph.BeliefValues.identity b) masses) b)
...   | false = nothing
...   | true with decayRows now factor masses bs
...     | nothing = nothing
...     | just rest = just ((Graph.BeliefValues.identity b , decayed now factor (massOf (Graph.BeliefValues.identity b) masses) b) ∷ rest)

-- All selected fact rows advance their baseline, including unchanged counts.
-- The user-facing count still reports actual numerical changes only.
changedCount : List Graph.BeliefValues → P.State → ℕ
changedCount beliefs [] = 0
changedCount beliefs ((identity , value) ∷ rest) with Ranking.lookup identity beliefs
... | nothing = changedCount beliefs rest
... | just belief with decayChanged belief value
... | false = changedCount beliefs rest
... | true = suc (changedCount beliefs rest)

decay : ℤ → Float → List (ℕ × Float) → List Graph.BeliefValues → Maybe P.State
decay now factor masses beliefs with probability factor
... | false = nothing
... | true = decayRows now factor masses beliefs

-- Every visible edge carries its target's same durable first-defeat clock.
-- The read boundary refuses a missing clock instead of guessing a history.
record Defeat : Set where
  constructor defeat
  field source target : ℕ; clock : Retirement.Clock

targetClock : ℕ → List Defeat → Maybe Retirement.Clock
targetClock id [] = nothing
targetClock id (e ∷ es) with id ≟ Defeat.target e
... | no _ = targetClock id es
... | yes _ = just (Defeat.clock e)

expired : ℤ → ℤ → Float → List Graph.BeliefValues → List Defeat → ℕ → Bool
expired now grace threshold beliefs edges id with Ranking.lookup id beliefs | targetClock id edges
... | just belief | just clock = not (threshold ≤ᵇ Graph.BeliefValues.probability belief) ∧
  Retirement.waitingSatisfied now grace clock
... | _ | _ = false

expiredTargets : ℤ → ℤ → Float → List Graph.BeliefValues → List Defeat → List ℕ → List ℕ
expiredTargets now grace threshold beliefs edges enumeration =
  filterᵇ (expired now grace threshold beliefs edges) (Ranking.unique enumeration)

surgical : ℕ → P.Edge → Bool
surgical target incoming = not (does (target ≟ P.Edge.target incoming)) ∧ causes (P.Edge.relation incoming)
  where
  causes : Review.Relation → Bool
  causes Review.causes = true
  causes _ = false

project : P.State → List (ℕ × Float)
project = map (λ { (id , b) → id , P.mean b })

workingExempt : ∀ now factor masses b bs → Graph.BeliefValues.memory b ≡ Candidates.working →
  decayRows now factor masses (b ∷ bs) ≡ decayRows now factor masses bs
workingExempt now factor masses b bs same rewrite same = refl

experientialExempt : ∀ now factor masses b bs → Graph.BeliefValues.memory b ≡ Candidates.experiential →
  decayRows now factor masses (b ∷ bs) ≡ decayRows now factor masses bs
experientialExempt now factor masses b bs same rewrite same = refl

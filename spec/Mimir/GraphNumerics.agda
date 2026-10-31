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
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Candidates
import Mimir.RetrievalRanking as Ranking
import Mimir.PosteriorComputation as P
import Mimir.AssessmentScores as Scores
import Mimir.ReviewSchema as Review

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

-- Timestamps are signed UTC nanoseconds. Whole elapsed seconds are used,
-- matching chrono; negative elapsed durations are clamped to zero days.
decayed : ℤ → Float → Float → Graph.BeliefValues → P.Beta
decayed now factor mass belief = P.beta
  (1.0 + retention * (Graph.BeliefValues.alpha belief - 1.0))
  (1.0 + retention * (Graph.BeliefValues.beta belief - 1.0))
  where
  days = P.maximum (fromℤ ((now Int.- Graph.BeliefValues.activated belief) /ℕ 1000000000) ÷ 86400.0) 0.0
  base = factor ** days
  retention = 1.0 - ((1.0 - base) ÷ (1.0 + mass))

decayChanged : Graph.BeliefValues → P.Beta → Bool
decayChanged b value =
  (threshold <ᵇ Scores.absolute (P.Beta.alpha value - Graph.BeliefValues.alpha b)) ∨
  (threshold <ᵇ Scores.absolute (P.Beta.negative value - Graph.BeliefValues.beta b))
  where
  threshold = 0.0000000000000002220446049250313 *
    P.maximum (Graph.BeliefValues.alpha b + Graph.BeliefValues.beta b) 1.0

massOf : ℕ → List (ℕ × Float) → Float
massOf id masses with P.lookup id masses
... | nothing = 0.0
... | just mass = mass

decayRows : ℤ → Float → List (ℕ × Float) → List Graph.BeliefValues → P.State
decayRows now factor masses [] = []
decayRows now factor masses (b ∷ bs) with Graph.BeliefValues.memory b
... | Candidates.experiential = decayRows now factor masses bs
... | Candidates.working = decayRows now factor masses bs
... | Candidates.fact with decayChanged b (decayed now factor (massOf (Graph.BeliefValues.identity b) masses) b)
...   | false = decayRows now factor masses bs
...   | true = (Graph.BeliefValues.identity b , decayed now factor (massOf (Graph.BeliefValues.identity b) masses) b)
  ∷ decayRows now factor masses bs

decay : ℤ → Float → List (ℕ × Float) → List Graph.BeliefValues → Maybe P.State
decay now factor masses beliefs with probability factor
... | false = nothing
... | true = just (decayRows now factor masses beliefs)

-- Latest defeat is the source belief creation time, not an edge timestamp.
-- HashMap iteration order is intentionally not invented: callers provide the
-- enumeration order, and duplicate target identities are removed before use.
record Defeat : Set where
  constructor defeat
  field source target : ℕ; sourceCreated : ℤ

latest : ℕ → List Defeat → Maybe ℤ
latest id [] = nothing
latest id (e ∷ es) with id ≟ Defeat.target e
... | no _ = latest id es
... | yes _ with latest id es
...   | nothing = just (Defeat.sourceCreated e)
...   | just time = just (Defeat.sourceCreated e Int.⊔ time)

expired : ℤ → ℤ → Float → List Graph.BeliefValues → List Defeat → ℕ → Bool
expired now grace threshold beliefs edges id with Ranking.lookup id beliefs | latest id edges
... | just belief | just time = not (threshold ≤ᵇ Graph.BeliefValues.probability belief) ∧
  does (grace Int.≤? (now Int.- time))
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

intervene : ℕ → Float → List P.Node → List P.Edge → P.External → P.Result
intervene target value nodes edges external = P.run (just (target , value)) external
  (filterᵇ (surgical target) edges) nodes

project : P.State → List (ℕ × Float)
project = map (λ { (id , b) → id , P.mean b })

workingExempt : ∀ now factor masses b bs → Graph.BeliefValues.memory b ≡ Candidates.working →
  decayRows now factor masses (b ∷ bs) ≡ decayRows now factor masses bs
workingExempt now factor masses b bs same rewrite same = refl

experientialExempt : ∀ now factor masses b bs → Graph.BeliefValues.memory b ≡ Candidates.experiential →
  decayRows now factor masses (b ∷ bs) ≡ decayRows now factor masses bs
experientialExempt now factor masses b bs same rewrite same = refl

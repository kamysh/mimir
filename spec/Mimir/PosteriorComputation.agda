{-# OPTIONS --safe #-}
-- Ordered, bounded application inference. Standard Float supplies arithmetic;
-- this module specifies Mimir's iteration order, fixed priors, clamped seed,
-- external parents, convergence test and durable-update selection.
module Mimir.PosteriorComputation where

open import Data.Float.Base using (Float; _+_; _-_; _*_; _÷_; _<ᵇ_; isNaN)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.ReviewSchema as Review
import Mimir.AssessmentScores as Scores

record Beta : Set where
  constructor beta
  field alpha negative : Float

clamp : Float → Float
clamp x with x <ᵇ 0.0
... | true = 0.0
... | false with 1.0 <ᵇ x
...   | true = 1.0
...   | false = x

mean : Beta → Float
mean b with 0.0 <ᵇ (Beta.alpha b + Beta.negative b)
... | true = clamp (Beta.alpha b ÷ (Beta.alpha b + Beta.negative b))
... | false = 0.5

confidence : Beta → Float
confidence b = clamp (((Beta.alpha b + Beta.negative b) - 2.0) ÷ (200.0 - 2.0))

prior : Float → Float → Beta
prior probability certainty = beta (probability * strength) ((1.0 - probability) * strength)
  where strength = 2.0 + certainty * (200.0 - 2.0)

maximum : Float → Float → Float
maximum a b with isNaN a | isNaN b
... | true | _ = b
... | false | true = a
... | false | false with a <ᵇ b
...   | true = b
...   | false = a

record Node : Set where
  constructor node
  field identity : ℕ; fixed original : Beta

record Edge : Set where
  constructor edge
  field source target : ℕ; relation : Review.Relation; weight : Float

State = List (ℕ × Beta)
External = List (ℕ × Float)
Seed = Maybe (ℕ × Float)

lookup : ∀ {A : Set} → ℕ → List (ℕ × A) → Maybe A
lookup id [] = nothing
lookup id ((key , value) ∷ rest) with id ≟ key
... | yes same = just value
... | no different = lookup id rest

write : ℕ → Beta → State → State
write id value [] = []
write id value ((key , old) ∷ rest) with id ≟ key
... | yes same = (key , value) ∷ rest
... | no different = (key , old) ∷ write id value rest

unclamped : ℕ → State → External → Maybe Float
unclamped id state external with lookup id state
... | just b = just (mean b)
... | nothing = lookup id external

parent : Seed → ℕ → State → External → Maybe Float
parent nothing id state external = unclamped id state external
parent (just (seed , value)) id state external with id ≟ seed
... | yes same = just value
... | no different = unclamped id state external

contribute : Review.Relation → Float → Beta → Beta
contribute Review.supports delta b = beta (Beta.alpha b + delta) (Beta.negative b)
contribute Review.causes delta b = beta (Beta.alpha b + delta) (Beta.negative b)
contribute Review.defeats delta b = beta (Beta.alpha b) (Beta.negative b + delta)
contribute Review.contradicts delta b = b

incoming : Seed → ℕ → State → External → List Edge → Beta → Beta
incoming seed target state external [] b = b
incoming seed target state external (e ∷ es) b with target ≟ Edge.target e
... | no different = incoming seed target state external es b
... | yes same with parent seed (Edge.source e) state external
...   | nothing = incoming seed target state external es b
...   | just probability = incoming seed target state external es
  (contribute (Edge.relation e) ((Edge.weight e * probability) * 4.0) b)

isSeed : Seed → ℕ → Bool
isSeed nothing id = false
isSeed (just (seed , value)) id with id ≟ seed
... | yes same = true
... | no different = false

insert : Node → List Node → List Node
insert n [] = n ∷ []
insert n (m ∷ ms) with Node.identity n ≤? Node.identity m
... | yes before = n ∷ m ∷ ms
... | no after = m ∷ insert n ms

order : Seed → List Node → List Node
order seed [] = []
order seed (n ∷ ns) with isSeed seed (Node.identity n)
... | true = order seed ns
... | false = insert n (order seed ns)

record Sweep : Set where
  constructor sweepResult
  field state : State; delta : Float

sweep : Seed → External → List Edge → List Node → State → Float → Sweep
sweep seed external edges [] state delta = sweepResult state delta
sweep seed external edges (n ∷ ns) state delta with lookup (Node.identity n) state
... | nothing = sweep seed external edges ns state delta
... | just old = sweep seed external edges ns (write (Node.identity n) updated state)
  (maximum delta (Scores.absolute (mean updated - mean old)))
  where updated = incoming seed (Node.identity n) state external edges (Node.fixed n)

record Outcome : Set where
  constructor outcome
  field state : State; converged : Bool

iterate : ℕ → Seed → External → List Edge → List Node → State → Outcome
iterate zero seed external edges nodes state = outcome state false
iterate (suc fuel) seed external edges nodes state
  with sweep seed external edges nodes state 0.0
... | sweepResult after delta with delta <ᵇ 0.000000001
...   | true = outcome after true
...   | false = iterate fuel seed external edges nodes after

changed : Beta → Beta → Bool
changed old new =
  ((0.000000001 * scale) <ᵇ Scores.absolute (Beta.alpha new - Beta.alpha old)) ∨
  ((0.000000001 * scale) <ᵇ Scores.absolute (Beta.negative new - Beta.negative old))
  where scale = maximum (Beta.alpha old + Beta.negative old) 1.0

updates : List Node → State → State
updates [] state = []
updates (n ∷ ns) state with lookup (Node.identity n) state
... | nothing = updates ns state
... | just b with changed (Node.original n) b
...   | false = updates ns state
...   | true = (Node.identity n , b) ∷ updates ns state

record Result : Set where
  constructor result
  field writes : State; iterationLimitReached : Bool

run : Seed → External → List Edge → List Node → Result
run seed external edges nodes with iterate 50 seed external edges ordered initial
  where
  ordered = order seed nodes
  initial = map (λ n → Node.identity n , Node.fixed n) nodes
... | outcome final true = result (updates (order seed nodes) final) false
... | outcome final false = result (updates (order seed nodes) final) true

contradictionInert : ∀ delta b → contribute Review.contradicts delta b ≡ b
contradictionInert delta b = refl

exhaustionReturnsCurrent : ∀ seed external edges nodes state →
  iterate zero seed external edges nodes state ≡ outcome state false
exhaustionReturnsCurrent seed external edges nodes state = refl

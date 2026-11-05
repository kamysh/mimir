{-# OPTIONS --safe #-}
-- Ordered, bounded application inference. Standard Float supplies arithmetic;
-- this module specifies Mimir's iteration order, fixed priors, clamped seed,
-- external parents, convergence test and durable-update selection.
module Mimir.PosteriorComputation where

open import Data.Float.Base using (Float; _+_; _-_; _*_; _÷_; _<ᵇ_; _≤ᵇ_; isNaN)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Nullary.Decidable.Core using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
import Mimir.ReviewSchema as Review
import Mimir.AssessmentScores as Scores
open import Mimir.SourceReview using (boolTrue?)

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

unitInterval : Float → Bool
unitInterval value = (0.0 ≤ᵇ value) ∧ (value ≤ᵇ 1.0)

-- These are application admission rules over supplied Float operations.
-- Zero evidence is allowed; negative/nonfinite counts and an overflowing
-- total are not made valid by a clamped mean or confidence.
record ValidCounts (value : Beta) : Set where
  field
    finiteAlpha : Scores.finite (Beta.alpha value) ≡ true
    finiteBeta : Scores.finite (Beta.negative value) ≡ true
    finiteTotal : Scores.finite (Beta.alpha value + Beta.negative value) ≡ true
    nonnegativeAlpha : (0.0 ≤ᵇ Beta.alpha value) ≡ true
    nonnegativeBeta : (0.0 ≤ᵇ Beta.negative value) ≡ true
    validMean : unitInterval (mean value) ≡ true
    validConfidence : unitInterval (confidence value) ≡ true

validCounts? : ∀ value → Dec (ValidCounts value)
validCounts? value with boolTrue? (Scores.finite (Beta.alpha value)) ×-dec
  (boolTrue? (Scores.finite (Beta.negative value)) ×-dec
  (boolTrue? (Scores.finite (Beta.alpha value + Beta.negative value)) ×-dec
  (boolTrue? (0.0 ≤ᵇ Beta.alpha value) ×-dec
  (boolTrue? (0.0 ≤ᵇ Beta.negative value) ×-dec
  (boolTrue? (unitInterval (mean value)) ×-dec boolTrue? (unitInterval (confidence value)))))))
... | yes (a , b , total , nonnegativeA , nonnegativeB , shownMean , shownConfidence) = yes
  record { finiteAlpha = a ; finiteBeta = b ; finiteTotal = total
         ; nonnegativeAlpha = nonnegativeA ; nonnegativeBeta = nonnegativeB
         ; validMean = shownMean ; validConfidence = shownConfidence }
... | no invalid = no (λ proof → invalid
  (ValidCounts.finiteAlpha proof , ValidCounts.finiteBeta proof , ValidCounts.finiteTotal proof ,
   ValidCounts.nonnegativeAlpha proof , ValidCounts.nonnegativeBeta proof ,
   ValidCounts.validMean proof , ValidCounts.validConfidence proof))

validCounts : Beta → Bool
validCounts value = does (validCounts? value)

validCountsSound : ∀ value → validCounts value ≡ true → ValidCounts value
validCountsSound value = decisionSound (validCounts? value)
  where
  decisionSound : ∀ {A : Set} (decision : Dec A) → does decision ≡ true → A
  decisionSound (yes valid) observed = valid
  decisionSound (no invalid) ()

rejectedDecision : ∀ {A : Set} (decision : Dec A) → (A → ⊥) → does decision ≡ false
rejectedDecision (yes valid) invalid = ⊥-elim (invalid valid)
rejectedDecision (no invalid) rejected = refl

incompatible : ∀ {b} → b ≡ false → b ≡ true → ⊥
incompatible negative positive with trans (sym negative) positive
... | ()

nonfiniteAlphaRefused : ∀ value → Scores.finite (Beta.alpha value) ≡ false → validCounts value ≡ false
nonfiniteAlphaRefused value invalid = rejectedDecision (validCounts? value)
  (λ valid → incompatible invalid (ValidCounts.finiteAlpha valid))

nonfiniteBetaRefused : ∀ value → Scores.finite (Beta.negative value) ≡ false → validCounts value ≡ false
nonfiniteBetaRefused value invalid = rejectedDecision (validCounts? value)
  (λ valid → incompatible invalid (ValidCounts.finiteBeta valid))

overflowingTotalRefused : ∀ value → Scores.finite (Beta.alpha value + Beta.negative value) ≡ false → validCounts value ≡ false
overflowingTotalRefused value invalid = rejectedDecision (validCounts? value)
  (λ valid → incompatible invalid (ValidCounts.finiteTotal valid))

negativeAlphaRefused : ∀ value → (0.0 ≤ᵇ Beta.alpha value) ≡ false → validCounts value ≡ false
negativeAlphaRefused value invalid = rejectedDecision (validCounts? value)
  (λ valid → incompatible invalid (ValidCounts.nonnegativeAlpha valid))

negativeBetaRefused : ∀ value → (0.0 ≤ᵇ Beta.negative value) ≡ false → validCounts value ≡ false
negativeBetaRefused value invalid = rejectedDecision (validCounts? value)
  (λ valid → incompatible invalid (ValidCounts.nonnegativeBeta valid))

-- This includes empty evidence. It states the application's neutral branch
-- for arbitrary counts, without proving the external Float implementation.
nonpositiveTotalIsNeutral : ∀ value → (0.0 <ᵇ (Beta.alpha value + Beta.negative value)) ≡ false → mean value ≡ 0.5
nonpositiveTotalIsNeutral value nonpositive rewrite nonpositive = refl

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

validState : State → Bool
validState [] = true
validState ((_ , value) ∷ rest) = validCounts value ∧ validState rest

andLeft : ∀ a b → a ∧ b ≡ true → a ≡ true
andLeft false b ()
andLeft true b observed = refl

andRight : ∀ a b → a ∧ b ≡ true → b ≡ true
andRight false b ()
andRight true b observed = observed

ValidState : State → Set
ValidState = All (λ { (_ , value) → ValidCounts value })

validStateSound : ∀ values → validState values ≡ true → ValidState values
validStateSound [] observed = []
validStateSound ((_ , value) ∷ rest) observed =
  validCountsSound value (andLeft (validCounts value) (validState rest) observed) ∷
  validStateSound rest (andRight (validCounts value) (validState rest) observed)

validNodes : List Node → Bool
validNodes [] = true
validNodes (value ∷ rest) = validCounts (Node.fixed value) ∧
  validCounts (Node.original value) ∧ validNodes rest

validEdges : List Edge → Bool
validEdges [] = true
validEdges (value ∷ rest) = unitInterval (Edge.weight value) ∧ validEdges rest

referenced : ℕ → List Edge → Bool
referenced id [] = false
referenced id (edgeRow ∷ rest) with id ≟ Edge.source edgeRow
... | yes same = true
... | no different = referenced id rest

-- An unrelated row in another project is not an inference input merely
-- because it is present in the supplied lookup table.
validExternal : List Edge → External → Bool
validExternal edges [] = true
validExternal edges ((id , value) ∷ rest) with referenced id edges
... | false = validExternal edges rest
... | true = unitInterval value ∧ validExternal edges rest

validSeed : Seed → Bool
validSeed nothing = true
validSeed (just (_ , value)) = unitInterval value

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
  field state : State; delta : Float; numericFailure : Bool

sweep : Seed → External → List Edge → List Node → State → Float → Sweep
sweep seed external edges [] state delta = sweepResult state delta false
sweep seed external edges (n ∷ ns) state delta with lookup (Node.identity n) state
... | nothing = sweep seed external edges ns state delta
... | just old with validCounts updated
  where updated = incoming seed (Node.identity n) state external edges (Node.fixed n)
...   | false = sweepResult state delta true
...   | true = sweep seed external edges ns (write (Node.identity n) updated state)
  (maximum delta (Scores.absolute (mean updated - mean old)))
  where updated = incoming seed (Node.identity n) state external edges (Node.fixed n)

record Outcome : Set where
  constructor outcome
  field state : State; converged numericFailure : Bool

iterate : ℕ → Seed → External → List Edge → List Node → State → Outcome
iterate zero seed external edges nodes state = outcome state false false
iterate (suc fuel) seed external edges nodes state
  with sweep seed external edges nodes state 0.0
... | sweepResult after delta true = outcome after false true
... | sweepResult after delta false with delta <ᵇ 0.000000001
...   | true = outcome after true false
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
  field writes : State; iterationLimitReached numericFailure : Bool

finish : List Node → Outcome → Result
finish nodes (outcome final converged true) = result [] false true
finish nodes (outcome final converged false) with validState final
... | false = result [] false true
... | true = result (updates nodes final) (not converged) false

run : Seed → External → List Edge → List Node → Result
run seed external edges nodes with validSeed seed ∧ validExternal edges external ∧ validEdges edges ∧ validNodes nodes
... | false = result [] false true
... | true = finish (order seed nodes) (iterate 50 seed external edges ordered initial)
  where
  ordered = order seed nodes
  initial = map (λ n → Node.identity n , Node.fixed n) nodes

contradictionInert : ∀ delta b → contribute Review.contradicts delta b ≡ b
contradictionInert delta b = refl

exhaustionReturnsCurrent : ∀ seed external edges nodes state →
  iterate zero seed external edges nodes state ≡ outcome state false false
exhaustionReturnsCurrent seed external edges nodes state = refl

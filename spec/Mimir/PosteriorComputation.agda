{-# OPTIONS --safe #-}
-- Numerical data and validation at an external calculation boundary.
-- The calculation algorithm, iteration count and stopping threshold are
-- implementation details; they are not defined or proved here.
module Mimir.PosteriorComputation where

open import Data.Float.Base using (Float; _+_; _-_; _*_; _÷_; _<ᵇ_; _≤ᵇ_; isNaN)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
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
  field identity : UUID; fixed original : Beta

record Edge : Set where
  constructor edge
  field source target : UUID; relation : Review.Relation; weight : Float

State = List (UUID × Beta)
External = List (UUID × Float)
Seed = Maybe (UUID × Float)

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

referenced : UUID → List Edge → Bool
referenced id [] = false
referenced id (edgeRow ∷ rest) with id ≟UUID Edge.source edgeRow
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

lookup : ∀ {A : Set} → UUID → List (UUID × A) → Maybe A
lookup id [] = nothing
lookup id ((key , value) ∷ rest) with id ≟UUID key
... | yes same = just value
... | no different = lookup id rest

record Result : Set where
  constructor result
  field writes : State; numericFailure : Bool

-- Supplied by the external calculation component. Recovery obligations hold
-- for every supplied outcome; no solver or numerical convergence proof is
-- required to instantiate this interface.
record Calculation : Set where
  field
    calculate : Bool → Seed → External → List Edge → List Node → Result

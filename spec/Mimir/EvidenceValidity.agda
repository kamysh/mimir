{-# OPTIONS --safe #-}
-- Stored belief admission and framing laws for the current and original
-- evidence counts. Arithmetic itself remains a supplied Float operation.
module Mimir.EvidenceValidity where

open import Data.Bool using (Bool; true)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Nullary.Decidable.Core using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.CandidateGraph as G
import Mimir.PosteriorComputation as P
open import Mimir.SourceReview using (boolTrue?)

current original : G.BeliefValues → P.Beta
current value = P.beta (G.BeliefValues.alpha value) (G.BeliefValues.beta value)
original value = P.beta (G.BeliefValues.alpha0 value) (G.BeliefValues.beta0 value)

ValidBelief : G.BeliefValues → Set
ValidBelief value = P.ValidCounts (current value) ×
  (P.ValidCounts (original value) ×
  ((P.unitInterval (G.BeliefValues.probability value) ≡ true) ×
   (P.unitInterval (G.BeliefValues.confidence value) ≡ true)))

validBelief? : ∀ value → Dec (ValidBelief value)
validBelief? value = P.validCounts? (current value) ×-dec
  (P.validCounts? (original value) ×-dec
  (boolTrue? (P.unitInterval (G.BeliefValues.probability value)) ×-dec
   boolTrue? (P.unitInterval (G.BeliefValues.confidence value))))

validBelief : G.BeliefValues → Bool
validBelief value = does (validBelief? value)

decisionSound : ∀ {A : Set} (decision : Dec A) → does decision ≡ true → A
decisionSound (yes valid) observed = valid
decisionSound (no invalid) ()

validBeliefSound : ∀ value → validBelief value ≡ true → ValidBelief value
validBeliefSound value = decisionSound (validBelief? value)

admit : G.BeliefValues → Maybe G.BeliefValues
admit value with validBelief? value
... | yes valid = just value
... | no invalid = nothing

admitSound : ∀ before value → admit before ≡ just value → ValidBelief value
admitSound before value observed with validBelief? before
... | no invalid with observed
...   | ()
admitSound before .before refl | yes valid = valid

ValidNode : G.Node → Set
ValidNode (G.beliefNode value) = ValidBelief value
ValidNode (G.patternNode value) = ⊤

updated : G.BeliefValues → P.Beta → G.BeliefValues
updated before value = record before
  { alpha = P.Beta.alpha value ; beta = P.Beta.negative value
  ; probability = P.mean value ; confidence = P.confidence value }

updatedValid : ∀ before value → ValidBelief before → P.ValidCounts value → ValidBelief (updated before value)
updatedValid before value (_ , prior , _) valid =
  valid , prior , P.ValidCounts.validMean valid , P.ValidCounts.validConfidence valid

updatedPreservesOriginal : ∀ before value →
  G.BeliefValues.alpha0 (updated before value) ≡ G.BeliefValues.alpha0 before ×
  G.BeliefValues.beta0 (updated before value) ≡ G.BeliefValues.beta0 before
updatedPreservesOriginal before value = refl , refl

lookupValid : ∀ id values value → P.ValidState values →
  P.lookup id values ≡ just value → P.ValidCounts value
lookupValid id [] value [] ()
lookupValid id ((key , head) ∷ rest) value (valid ∷ tail) observed with id ≟ key
... | yes same with observed
...   | refl = valid
lookupValid id ((key , head) ∷ rest) value (valid ∷ tail) observed | no different =
  lookupValid id rest value tail observed

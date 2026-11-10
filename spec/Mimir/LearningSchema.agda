{-# OPTIONS --safe #-}
module Mimir.LearningSchema where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; -_)
open import Data.Rational.Properties using (_<?_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text
open import Mimir.Binary64
open import Mimir.NumericValidation
open import Mimir.Validation
open import Mimir.SourceSchema using (Source; Provenance; userFeedback; agentReport; toolResult;
  NamedText; checkNamed)
open import Mimir.SourceReview using (Item; item; Fresh; fresh?; idPresent; false?; boolTrue?)

data Kind : Set where estimate decision suggestion : Kind

record Prediction : Set where
  constructor prediction
  field
    quantity unit horizon recordedAt : Text
    point : Number
    probability lower upper : Maybe Number
    inferred : Bool

OptionalProbability : Maybe Number → Set
OptionalProbability nothing = ⊤
OptionalProbability (just value) = Between 0ℚ 1ℚ value

checkProbability : ∀ p → Checked (OptionalProbability p)
checkProbability nothing = accepted tt
checkProbability (just value) = checkBetween 0ℚ 1ℚ value

PredictionValid : Prediction → Set
PredictionValid p = NamedText (Prediction.quantity p) ×
  (NamedText (Prediction.unit p) ×
  (NamedText (Prediction.horizon p) ×
  (NamedText (Prediction.recordedAt p) ×
  (IsFinite (Prediction.point p) ×
  (OptionalProbability (Prediction.probability p) ×
    Interval (Prediction.point p) (Prediction.lower p) (Prediction.upper p))))))

validatePrediction : ∀ p → Checked (PredictionValid p)
validatePrediction p = combine
  (at (key "quantity") (checkNamed (Prediction.quantity p)))
  (combine (at (key "unit") (checkNamed (Prediction.unit p)))
  (combine (at (key "horizon") (checkNamed (Prediction.horizon p)))
  (combine (at (key "recorded_at") (checkNamed (Prediction.recordedAt p)))
  (combine (at (key "value") (checkFinite (Prediction.point p)))
  (combine (at (key "probability") (checkProbability (Prediction.probability p)))
    (checkInterval (Prediction.point p) (Prediction.lower p) (Prediction.upper p)))))))

record LearningItem : Set where
  constructor learningItem
  field
    identity : ℕ
    localKey : Maybe Text
    kind : Kind
    reference actor statement conditions : Text
    predictions : List Prediction

sourceProjection : LearningItem → Item
sourceProjection i = item (LearningItem.identity i) (LearningItem.reference i)
  (LearningItem.actor i) (LearningItem.statement i)

-- This contract does not depend on a database identity. Incoming items use
-- the same checks before PostgreSQL allocates their omitted identities.
ItemFieldsValid : Text → Text → Text → Text → List Prediction → Set
ItemFieldsValid reference actor statement conditions predictions = NamedText reference ×
  (NamedText actor × (NamedText statement ×
  (NamedText conditions × All PredictionValid predictions)))

validateItemFields : ∀ reference actor statement conditions predictions →
  Checked (ItemFieldsValid reference actor statement conditions predictions)
validateItemFields reference actor statement conditions predictions = combine
  (at (key "source_ref") (checkNamed reference))
  (combine (at (key "actor") (checkNamed actor))
  (combine (at (key "statement") (checkNamed statement))
  (combine (at (key "conditions") (checkNamed conditions))
    (at (key "predictions") (allChecked validatePrediction predictions)))))

ItemValid : LearningItem → Set
ItemValid i = ItemFieldsValid (LearningItem.reference i) (LearningItem.actor i)
  (LearningItem.statement i) (LearningItem.conditions i) (LearningItem.predictions i)

validateItem : ∀ i → Checked (ItemValid i)
validateItem i = validateItemFields (LearningItem.reference i) (LearningItem.actor i)
  (LearningItem.statement i) (LearningItem.conditions i) (LearningItem.predictions i)

ItemsValid : List LearningItem → Set
ItemsValid items = Fresh [] (map sourceProjection items) × All ItemValid items

validateItems : ∀ items → Checked (ItemsValid items)
validateItems items = combine
  (check (fault [] duplicate "learning item IDs must be distinct")
    (fresh? [] (map sourceProjection items))) (allChecked validateItem items)

-- Exact identity sets: repeated evidence/item references cannot multiply weight.
UniqueIDs : List ℕ → Set
UniqueIDs [] = ⊤
UniqueIDs (id ∷ rest) = idPresent id rest ≡ false × UniqueIDs rest

checkIDs : ∀ ids → Checked (UniqueIDs ids)
checkIDs [] = accepted tt
checkIDs (id ∷ rest) = combine
  (check (fault [] duplicate "references must be distinct") (false? (idPresent id rest)))
  (checkIDs rest)

data Target : Set where existing : ℕ → Target; candidate : Text → Target

record Assessment : Set where
  constructor assessment
  field
    target : Target
    scope rubric rationale : Text
    correctness usefulness : Axis
    evidenceIndices itemIDs : List ℕ

positiveWeight : Number → Bool
positiveWeight (nonfinite _ _) = false
positiveWeight (finite n) with 0ℚ <? value n
... | yes _ = true
... | no _ = false

weighted : Assessment → Bool
weighted a = positiveWeight (Axis.weight (Assessment.correctness a)) ∨
  positiveWeight (Axis.weight (Assessment.usefulness a))

data Some {A : Set} : List A → Set where present : ∀ a rest → Some (a ∷ rest)

checkSome : ∀ {A : Set} (xs : List A) → Checked (Some xs)
checkSome [] = rejected (fault [] missingEvidence "weighted assessment requires evidence") (λ ())
checkSome (x ∷ xs) = accepted (present x xs)

EvidenceRequired : Assessment → Set
EvidenceRequired a with weighted a
... | false = ⊤
... | true = Some (Assessment.evidenceIndices a)

checkRequired : ∀ a → Checked (EvidenceRequired a)
checkRequired a with weighted a
... | false = accepted tt
... | true = checkSome (Assessment.evidenceIndices a)

AssessmentValid : Assessment → Set
AssessmentValid a = NamedText (Assessment.scope a) ×
  (NamedText (Assessment.rubric a) ×
  (NamedText (Assessment.rationale a) ×
  (AxisValid 0ℚ (Assessment.correctness a) ×
  (AxisValid (- 1ℚ) (Assessment.usefulness a) ×
  (UniqueIDs (Assessment.evidenceIndices a) ×
  (UniqueIDs (Assessment.itemIDs a) × EvidenceRequired a))))))

validateAssessment : ∀ a → Checked (AssessmentValid a)
validateAssessment a = combine
  (at (key "scope") (checkNamed (Assessment.scope a)))
  (combine (at (key "rubric") (checkNamed (Assessment.rubric a)))
  (combine (at (key "rationale") (checkNamed (Assessment.rationale a)))
  (combine (at (key "correctness") (checkAxis 0ℚ (Assessment.correctness a)))
  (combine (at (key "usefulness") (checkAxis (- 1ℚ) (Assessment.usefulness a)))
  (combine (at (key "evidence_indices") (checkIDs (Assessment.evidenceIndices a)))
  (combine (at (key "item_ids") (checkIDs (Assessment.itemIDs a))) (checkRequired a)))))))

lookup : ∀ {A : Set} → ℕ → List A → Maybe A
lookup zero [] = nothing
lookup zero (x ∷ xs) = just x
lookup (suc n) [] = nothing
lookup (suc n) (x ∷ xs) = lookup n xs

EvidenceExists : List Text → ℕ → Set
EvidenceExists evidence id with lookup id evidence
... | nothing = ⊥
... | just text = Nonblank text

checkEvidence : ∀ evidence id → Checked (EvidenceExists evidence id)
checkEvidence evidence id with lookup id evidence
... | nothing = rejected (fault [] missingReference "assessment evidence index is out of range") (λ p → p)
... | just text = check (fault [] missingEvidence "assessment evidence is blank") (nonblank? text)

observed : Provenance → Bool
observed agentReport = false
observed userFeedback = true
observed toolResult = true

sourceObserved : List Source → ℕ → Bool
sourceObserved sources id with lookup id sources
... | nothing = false
... | just s = observed (Source.provenance s)

anyObserved : List Source → List ℕ → Bool
anyObserved sources [] = false
anyObserved sources (id ∷ ids) = sourceObserved sources id ∨ anyObserved sources ids

observedEvidence : Provenance → List Source → List ℕ → Bool
observedEvidence legacy [] ids = observed legacy
observedEvidence legacy sources@(_ ∷ _) ids = anyObserved sources ids

ZeroWeights : Assessment → Set
ZeroWeights a = IsZero (Axis.weight (Assessment.correctness a)) ×
  IsZero (Axis.weight (Assessment.usefulness a))

ObservationRequired : Bool → Assessment → Set
ObservationRequired true a = ⊤
ObservationRequired false a = ZeroWeights a

checkObserved : ∀ observed a → Checked (ObservationRequired observed a)
checkObserved true a = accepted tt
checkObserved false a = combine
  (at (key "correctness") (checkZero (Axis.weight (Assessment.correctness a))))
  (at (key "usefulness") (checkZero (Axis.weight (Assessment.usefulness a))))

SourceValid : Provenance → List Source → List Text → List ℕ → Assessment → Set
SourceValid legacy sources evidence itemIDs a = AssessmentValid a ×
  (All (EvidenceExists evidence) (Assessment.evidenceIndices a) ×
  (All (λ id → idPresent id itemIDs ≡ true) (Assessment.itemIDs a) ×
    ObservationRequired (observedEvidence legacy sources (Assessment.evidenceIndices a)) a))

validateSource : ∀ legacy sources evidence itemIDs a →
  Checked (SourceValid legacy sources evidence itemIDs a)
validateSource legacy sources evidence itemIDs a = combine (validateAssessment a)
  (combine (at (key "evidence_indices") (allChecked (checkEvidence evidence) (Assessment.evidenceIndices a)))
  (combine (at (key "item_ids") (allChecked
    (λ id → check (fault [] missingReference "assessment item ID is not in this experience revision")
      (boolTrue? (idPresent id itemIDs))) (Assessment.itemIDs a)))
    (checkObserved (observedEvidence legacy sources (Assessment.evidenceIndices a)) a)))

unobservedCannotContribute : ∀ a → ObservationRequired false a → ZeroWeights a
unobservedCannotContribute a proof = proof

validAssessmentNeverRejected : ∀ a → AssessmentValid a → reported (validateAssessment a) ≡ []
validAssessmentNeverRejected a proof = noFalseRejection (validateAssessment a) proof

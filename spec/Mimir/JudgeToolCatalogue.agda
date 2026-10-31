{-# OPTIONS --safe #-}
-- Required host/model tools and optional model tools have distinct admission
-- rules. Only checked, originally advertised definitions reach the provider.
module Mimir.JudgeToolCatalogue where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation using (Fault)
open import Mimir.RecordDecoding using (_>>=_)
import Mimir.StructuredValue as V
import Mimir.McpToolAdvertisement as A

data Demand : Set where
  requiredHost requiredModel optionalModel : A.Requirement → Demand

schema : Demand → A.Requirement
schema (requiredHost requirement) = requirement
schema (requiredModel requirement) = requirement
schema (optionalModel requirement) = requirement

data Covered (tools : List V.Value) : List Demand → List V.Value → Set where
  empty : Covered tools [] []
  host : ∀ {requirement rest after} → A.Selected requirement tools → Covered tools rest after →
    Covered tools (requiredHost requirement ∷ rest) after
  model : ∀ {requirement rest after} → (selection : A.Selected requirement tools) → Covered tools rest after →
    Covered tools (requiredModel requirement ∷ rest) (A.Selected.raw selection ∷ after)
  optionalPresent : ∀ {requirement rest after} → (selection : A.Selected requirement tools) → Covered tools rest after →
    Covered tools (optionalModel requirement ∷ rest) (A.Selected.raw selection ∷ after)
  optionalAbsent : ∀ {requirement rest after} → All (λ raw → ¬ A.Named (A.Requirement.name requirement) raw) tools →
    Covered tools rest after → Covered tools (optionalModel requirement ∷ rest) after

Result : List Demand → List V.Value → Set
Result demands tools = Σ (List V.Value) (Covered tools demands)

check : ∀ demands tools → Fault ⊎ Result demands tools
check [] tools = inj₂ ([] , empty)
check (requiredHost requirement ∷ rest) tools = A.required requirement tools >>= λ selected →
  check rest tools >>= λ where
    (after , proof) → inj₂ (after , host selected proof)
check (requiredModel requirement ∷ rest) tools = A.required requirement tools >>= λ selected →
  check rest tools >>= λ where
    (after , proof) → inj₂ (A.Selected.raw selected ∷ after , model selected proof)
check (optionalModel requirement ∷ rest) tools with A.find (A.Requirement.name requirement) tools
... | A.missing absent = check rest tools >>= λ where
  (after , proof) → inj₂ (after , optionalAbsent absent proof)
... | A.found raw first = A.validateFound requirement tools raw first >>= λ selected →
  check rest tools >>= λ where
    (after , proof) → inj₂ (A.Selected.raw selected ∷ after , optionalPresent selected proof)

Published : List V.Value → V.Value → Set
Published tools raw = Σ A.Requirement λ requirement → Σ (A.Selected requirement tools) λ selection → raw ≡ A.Selected.raw selection

everyPublishedDefinitionChecked : ∀ {tools demands after} → Covered tools demands after → All (Published tools) after
everyPublishedDefinitionChecked empty = []
everyPublishedDefinitionChecked (host selected rest) = everyPublishedDefinitionChecked rest
everyPublishedDefinitionChecked (model {requirement} selected rest) = (requirement , selected , refl) ∷ everyPublishedDefinitionChecked rest
everyPublishedDefinitionChecked (optionalPresent {requirement} selected rest) = (requirement , selected , refl) ∷ everyPublishedDefinitionChecked rest
everyPublishedDefinitionChecked (optionalAbsent absent rest) = everyPublishedDefinitionChecked rest

property : String → String → A.Property
property name kind = A.propertySpec
  (toList "inputSchema" ∷ toList "properties" ∷ toList name ∷ toList "type" ∷ []) (toList kind)

reviewProperty : String → String → A.Property
reviewProperty name kind = A.propertySpec
  (toList "inputSchema" ∷ toList "properties" ∷ toList "review" ∷ toList "properties" ∷ toList name ∷ toList "type" ∷ []) (toList kind)

requirement : String → List A.Property → A.Requirement
requirement name fields = A.requirementSpec (toList name) fields

-- The nested typed-learning properties supplement the original judge's three
-- identity fields; binary version equality cannot establish this support.
review : A.Requirement
review = requirement "review_experience"
  (property "review" "object" ∷ property "expected_review_revision" "integer" ∷
   reviewProperty "experience_id" "string" ∷ reviewProperty "experience_revision" "integer" ∷
   reviewProperty "reviewer" "string" ∷ reviewProperty "rationale" "string" ∷
   map (λ name → reviewProperty name "array")
     ("assessments" ∷ "extracted_items" ∷ "source_coverage" ∷ "feedback" ∷ "links" ∷
      "superseded_beliefs" ∷ "candidates" ∷ "candidate_feedback" ∷ "candidate_links" ∷ []))

assessment : String → Demand
assessment name = optionalModel (requirement name
  (map (λ key → property key "string") ("project" ∷ "belief_id" ∷ "scope" ∷ "rubric" ∷ [])))

demands : List Demand
demands =
  requiredHost (requirement "pending_experiences"
    (property "project" "string" ∷ property "limit" "integer" ∷ property "exclude_ids" "array" ∷ [])) ∷
  requiredHost (requirement "learning_capabilities"
    (A.propertySpec (toList "inputSchema" ∷ toList "type" ∷ []) (toList "object") ∷ [])) ∷
  requiredModel (requirement "get_experience" (property "id" "string" ∷ [])) ∷
  requiredModel review ∷
  requiredModel (requirement "experience_history" (property "id" "string" ∷ [])) ∷
  requiredModel (requirement "query_relevant" (property "context" "string" ∷ property "project" "string" ∷ property "limit" "integer" ∷ [])) ∷
  requiredModel (requirement "query_learning_context" (property "context" "string" ∷ property "project" "string" ∷ property "limit" "integer" ∷ [])) ∷
  requiredModel (requirement "explain_belief" (property "id" "string" ∷ property "limit" "integer" ∷ property "offset" "integer" ∷ [])) ∷
  requiredModel (requirement "get_belief" (property "id" "string" ∷ [])) ∷
  requiredModel (requirement "query_intervention" (property "id" "string" ∷ property "value" "number" ∷ [])) ∷
  requiredModel (requirement "get_contradictions" (property "project" "string" ∷ [])) ∷
  assessment "get_lesson_assessment" ∷ assessment "lesson_assessment_history" ∷
  optionalModel (requirement "get_learning_review" (property "id" "string" ∷ [])) ∷ []

admit : V.Value → Fault ⊎ Σ (List V.Value) (λ tools → Result demands tools)
admit raw = V.asArray (A.get (toList "tools") raw) >>= λ tools →
  check demands tools >>= λ selected → inj₂ (tools , selected)

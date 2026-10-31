{-# OPTIONS --safe #-}
-- The typed judge checks the learning contract independently of the binary's
-- user-controlled version string. Graph-only operations do not use this gate.
module Mimir.LearningCapabilities where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≟_; _≤_; _≤?_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Validation
open import Mimir.RecordDecoding using (_>>=_; mapResult; readRecord; validateDecoded)
import Mimir.StructuredValue as V
import Mimir.JsonObjects as Objects
import Mimir.Binary64 as Binary

record Capabilities : Set where
  constructor capabilities
  field
    contractVersion assessmentModelVersion : ℕ
    sourceCoverage typedItems revisionOwnedAssessments legacyProbabilityUnchanged : Bool

Compatible : ℕ → ℕ → Capabilities → Set
Compatible contract model actual = Capabilities.contractVersion actual ≡ contract ×
  (Capabilities.assessmentModelVersion actual ≡ model ×
  (Capabilities.sourceCoverage actual ≡ true ×
  (Capabilities.typedItems actual ≡ true ×
  (Capabilities.revisionOwnedAssessments actual ≡ true × Capabilities.legacyProbabilityUnchanged actual ≡ true))))

true? : ∀ value → Relation.Nullary.Dec (value ≡ true)
true? true = yes refl
true? false = no (λ ())

validate : ∀ contract model actual → Checked (Compatible contract model actual)
validate contract model actual = combine
  (at (key "contract_version") (check (fault [] unsupportedCombination "unsupported learning contract version")
    (Capabilities.contractVersion actual ≟ contract)))
  (combine (at (key "assessment_model_version") (check (fault [] unsupportedCombination "unsupported assessment model version")
    (Capabilities.assessmentModelVersion actual ≟ model)))
  (combine (at (key "source_coverage") (check (fault [] unsupportedCombination "source coverage is unavailable")
    (true? (Capabilities.sourceCoverage actual))))
  (combine (at (key "typed_learning_items") (check (fault [] unsupportedCombination "typed learning items are unavailable")
    (true? (Capabilities.typedItems actual))))
  (combine (at (key "revision_owned_assessments") (check (fault [] unsupportedCombination "revision-owned assessments are unavailable")
    (true? (Capabilities.revisionOwnedAssessments actual))))
    (at (key "legacy_graph_probability_unchanged") (check (fault [] unsupportedCombination "legacy graph probability compatibility is unavailable")
      (true? (Capabilities.legacyProbabilityUnchanged actual))))))))

uint : V.Value → Fault ⊎ ℕ
uint raw = result (V.uint (Binary.powerMinusOne 64) raw) >>= λ where
  (number , representation) → inj₂ number

uintRoundTrip : ∀ number → number ≤ Binary.powerMinusOne 64 → uint (V.unsigned number) ≡ inj₂ number
uintRoundTrip number bounded with number ≤? Binary.powerMinusOne 64
... | yes fits = refl
... | no outside = ⊥-elim (outside bounded)

fields : V.Object.View → Fault ⊎ Capabilities
fields view = V.required (toList "contract_version") uint view >>= λ contract →
  V.required (toList "assessment_model_version") uint view >>= λ model →
  V.required (toList "source_coverage") V.asBoolean view >>= λ coverage →
  V.required (toList "typed_learning_items") V.asBoolean view >>= λ typed →
  V.required (toList "revision_owned_assessments") V.asBoolean view >>= λ owned →
  V.required (toList "legacy_graph_probability_unchanged") V.asBoolean view >>= λ unchanged →
  inj₂ (capabilities contract model coverage typed owned unchanged)

names : List Text
names = toList "contract_version" ∷ toList "assessment_model_version" ∷ toList "source_coverage" ∷
  toList "typed_learning_items" ∷ toList "revision_owned_assessments" ∷ toList "legacy_graph_probability_unchanged" ∷ []

decode : V.Value → Fault ⊎ Capabilities
decode = readRecord Objects.ignore Objects.keepLast names fields

encode : Capabilities → V.Value
encode actual = V.object
  ((toList "contract_version" , V.unsigned (Capabilities.contractVersion actual)) ∷
   (toList "assessment_model_version" , V.unsigned (Capabilities.assessmentModelVersion actual)) ∷
   (toList "source_coverage" , V.boolean (Capabilities.sourceCoverage actual)) ∷
   (toList "typed_learning_items" , V.boolean (Capabilities.typedItems actual)) ∷
   (toList "revision_owned_assessments" , V.boolean (Capabilities.revisionOwnedAssessments actual)) ∷
   (toList "legacy_graph_probability_unchanged" , V.boolean (Capabilities.legacyProbabilityUnchanged actual)) ∷ [])

roundTrip : ∀ actual → Capabilities.contractVersion actual ≤ Binary.powerMinusOne 64 →
  Capabilities.assessmentModelVersion actual ≤ Binary.powerMinusOne 64 → decode (encode actual) ≡ inj₂ actual
roundTrip (capabilities contract model coverage typed owned unchanged) contractBound modelBound
  rewrite uintRoundTrip contract contractBound | uintRoundTrip model modelBound = refl

admit : ∀ contract model → V.Value → Fault ⊎ Σ Capabilities (Compatible contract model)
admit contract model raw = validateDecoded (validate contract model) (decode raw)

acceptedSupportsCoverage : ∀ contract model actual → Compatible contract model actual → Capabilities.sourceCoverage actual ≡ true
acceptedSupportsCoverage contract model actual (_ , _ , covered , _) = covered

acceptedPreservesLegacy : ∀ contract model actual → Compatible contract model actual → Capabilities.legacyProbabilityUnchanged actual ≡ true
acceptedPreservesLegacy contract model actual (_ , _ , _ , _ , _ , unchanged) = unchanged

matchingContractAccepted : ∀ contract model actual → Compatible contract model actual → reported (validate contract model actual) ≡ []
matchingContractAccepted contract model actual = noFalseRejection (validate contract model actual)

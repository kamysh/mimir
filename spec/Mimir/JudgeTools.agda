{-# OPTIONS --safe #-}
-- The judge's tool universe retains each concrete operation. The review
-- operation cannot be mislabeled as a read by a separately supplied flag.
module Mimir.JudgeTools where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation using (Fault; fault; key; unsupportedCombination)
import Mimir.ToolCatalog as Catalog

data Query : Set where
  lessonAssessment assessmentHistory experience experienceHistory learningReview
    relevant learningContext contradictions belief explanation intervention : Query

data Kind : Set where
  query : Query → Kind
  review : Kind

queryOperation : Query → Catalog.Tool
queryOperation lessonAssessment = Catalog.getLessonAssessment
queryOperation assessmentHistory = Catalog.lessonAssessmentHistory
queryOperation experience = Catalog.getExperience
queryOperation experienceHistory = Catalog.experienceHistory
queryOperation learningReview = Catalog.getLearningReview
queryOperation relevant = Catalog.queryRelevant
queryOperation learningContext = Catalog.queryLearningContext
queryOperation contradictions = Catalog.getContradictions
queryOperation belief = Catalog.getBelief
queryOperation explanation = Catalog.explainBelief
queryOperation intervention = Catalog.queryIntervention

operation : Kind → Catalog.Tool
operation (query q) = queryOperation q
operation review = Catalog.reviewExperience

name : Kind → Text
name kind = toList (Catalog.wireName (operation kind))

allowed : List Kind
allowed = review ∷ query lessonAssessment ∷ query assessmentHistory ∷ query experience ∷
  query experienceHistory ∷ query learningReview ∷ query relevant ∷ query learningContext ∷
  query contradictions ∷ query belief ∷ query explanation ∷ query intervention ∷ []

lookup : Text → List Kind → Maybe Kind
lookup text [] = nothing
lookup text (kind ∷ rest) with text ≟Text name kind
... | yes _ = just kind
... | no _ = lookup text rest

lookupSound : ∀ text kinds kind → lookup text kinds ≡ just kind → text ≡ name kind
lookupSound text [] kind ()
lookupSound text (head ∷ rest) kind equal with text ≟Text name head
... | yes same with equal
...   | refl = same
lookupSound text (head ∷ rest) kind equal | no different = lookupSound text rest kind equal

lookupComplete : ∀ kind → lookup (name kind) allowed ≡ just kind
lookupComplete review = refl
lookupComplete (query lessonAssessment) = refl
lookupComplete (query assessmentHistory) = refl
lookupComplete (query experience) = refl
lookupComplete (query experienceHistory) = refl
lookupComplete (query learningReview) = refl
lookupComplete (query relevant) = refl
lookupComplete (query learningContext) = refl
lookupComplete (query contradictions) = refl
lookupComplete (query belief) = refl
lookupComplete (query explanation) = refl
lookupComplete (query intervention) = refl

decode : Text → Fault ⊎ Kind
decode text with lookup text allowed
... | just kind = inj₂ kind
... | nothing = inj₁ (fault (key "name" ∷ []) unsupportedCombination "tool is not allowed for judge")

everyAllowedNameAccepted : ∀ kind → decode (name kind) ≡ inj₂ kind
everyAllowedNameAccepted kind rewrite lookupComplete kind = refl

decodedNamePreserved : ∀ text kind → decode text ≡ inj₂ kind → text ≡ name kind
decodedNamePreserved text kind success with lookup text allowed in found
... | nothing with success
...   | ()
decodedNamePreserved text kind success | just actual with success
... | refl = lookupSound text allowed actual found

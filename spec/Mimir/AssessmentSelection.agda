{-# OPTIONS --safe #-}
-- Meaning of the joins and WHERE clauses in lesson_assessment. These are
-- Mimir's query predicates, not a new SQL engine. The adapter must establish
-- that the relational rows represent the actual tables and their constraints.
module Mimir.AssessmentSelection where

open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List; []; _∷_; filter)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Properties as List
import Data.List.Relation.Unary.All.Properties as All
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.Assessment as Assessment

record Query : Set where
  constructor query
  field project : Text; belief : ℕ; scope rubric : Text

-- A candidate tuple from the three tables. Every join equality is checked;
-- no matching ownership or current-review condition is assumed by this type.
record Row : Set where
  constructor row
  field
    experienceID : ℕ
    project : Text
    sourceRevision activeReviewRevision : ℕ
    reviewExperienceID reviewRevision reviewSourceRevision : ℕ
    contributionExperienceID contributionReviewRevision belief : ℕ
    scope rubric : Text
    mass : Assessment.Mass

Matches : Query → Row → Set
Matches q r =
  (Row.experienceID r ≡ Row.contributionExperienceID r) ×
  ((Row.reviewExperienceID r ≡ Row.experienceID r) ×
  ((Row.reviewRevision r ≡ Row.contributionReviewRevision r) ×
  ((Row.activeReviewRevision r ≡ Row.reviewRevision r) ×
  ((Row.sourceRevision r ≡ Row.reviewSourceRevision r) ×
  ((Row.project r ≡ Query.project q) ×
  ((Row.belief r ≡ Query.belief q) ×
  ((Row.scope r ≡ Query.scope q) × (Row.rubric r ≡ Query.rubric q))))))))

matches? : ∀ q r → Dec (Matches q r)
matches? q r =
  (Row.experienceID r ≟ Row.contributionExperienceID r) ×-dec
  (Row.reviewExperienceID r ≟ Row.experienceID r) ×-dec
  (Row.reviewRevision r ≟ Row.contributionReviewRevision r) ×-dec
  (Row.activeReviewRevision r ≟ Row.reviewRevision r) ×-dec
  (Row.sourceRevision r ≟ Row.reviewSourceRevision r) ×-dec
  (Row.project r ≟Text Query.project q) ×-dec
  (Row.belief r ≟ Query.belief q) ×-dec
  (Row.scope r ≟Text Query.scope q) ×-dec
  (Row.rubric r ≟Text Query.rubric q)

select : Query → List Row → List Row
select q = filter (matches? q)

everySelectedRowMatches : ∀ q rows → All (Matches q) (select q rows)
everySelectedRowMatches q rows = All.all-filter (matches? q) rows

matchingRowRetained : ∀ q r rows → Matches q r →
  select q (r ∷ rows) ≡ r ∷ select q rows
matchingRowRetained q r rows matches = List.filter-accept (matches? q) {x = r} {xs = rows} matches

staleSourceExcluded : ∀ q r rows → Row.sourceRevision r ≢ Row.reviewSourceRevision r →
  select q (r ∷ rows) ≡ select q rows
staleSourceExcluded q r rows stale = List.filter-reject (matches? q) {x = r} {xs = rows}
  (λ { (_ , _ , _ , _ , current , _ , _ , _ , _) → stale current })

obsoleteReviewExcluded : ∀ q r rows → Row.activeReviewRevision r ≢ Row.reviewRevision r →
  select q (r ∷ rows) ≡ select q rows
obsoleteReviewExcluded q r rows obsolete = List.filter-reject (matches? q) {x = r} {xs = rows}
  (λ { (_ , _ , _ , current , _ , _ , _ , _ , _) → obsolete current
     })

foreignProjectExcluded : ∀ q r rows → Row.project r ≢ Query.project q →
  select q (r ∷ rows) ≡ select q rows
foreignProjectExcluded q r rows foreign = List.filter-reject (matches? q) {x = r} {xs = rows}
  (λ { (_ , _ , _ , _ , _ , same , _ , _ , _) → foreign same })

otherLessonExcluded : ∀ q r rows → Row.belief r ≢ Query.belief q →
  select q (r ∷ rows) ≡ select q rows
otherLessonExcluded q r rows other = List.filter-reject (matches? q) {x = r} {xs = rows}
  (λ { (_ , _ , _ , _ , _ , _ , same , _ , _) → other same })

otherScopeExcluded : ∀ q r rows → Row.scope r ≢ Query.scope q →
  select q (r ∷ rows) ≡ select q rows
otherScopeExcluded q r rows other = List.filter-reject (matches? q) {x = r} {xs = rows}
  (λ { (_ , _ , _ , _ , _ , _ , _ , same , _) → other same })

otherRubricExcluded : ∀ q r rows → Row.rubric r ≢ Query.rubric q →
  select q (r ∷ rows) ≡ select q rows
otherRubricExcluded q r rows other = List.filter-reject (matches? q) {x = r} {xs = rows}
  (λ { (_ , _ , _ , _ , _ , _ , _ , _ , same) → other same })

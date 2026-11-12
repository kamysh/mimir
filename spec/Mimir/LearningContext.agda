{-# OPTIONS --safe #-}
-- Assessment selection for learning context does not create evidence.
module Mimir.LearningContext where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; nonblank)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.RetrievalRanking as Ranking
import Mimir.LearningStore as Store
import Mimir.LearningAssessmentQueries as View
import Mimir.AssessmentRead as Read
import Mimir.AssessmentWrites as Writes
import Mimir.AssessmentSelection as Selection
import Mimir.AssessmentEvaluation as Evaluation
import Mimir.ReviewLedger as Ledger

record Key : Set where
  constructor key
  field belief : UUID; scope rubric : Text

sameKey : Key → Key → Bool
sameKey a b = does (Key.belief a ≟UUID Key.belief b) ∧
  does (Key.scope a ≟Text Key.scope b) ∧ does (Key.rubric a ≟Text Key.rubric b)

keyMember : Key → List Key → Bool
keyMember k [] = false
keyMember k (x ∷ xs) = sameKey k x ∨ keyMember k xs

keys : Text → List UUID → Read.World → List Writes.Row → List Key
keys project ids state [] = []
keys project ids state (r ∷ rs) with Read.join state r
... | nothing = keys project ids state rs
... | just joined with Read.Entry.active joined ∧ Ranking.member (Writes.Row.belief r) ids ∧
  does (project ≟Text Ledger.R.Cell.project (Ledger.World.cells (Read.World.ledger state) (Writes.Row.experience r)))
...   | false = keys project ids state rs
...   | true with keyMember k rest
  where
  k = key (Writes.Row.belief r) (Writes.scope r) (Writes.rubric r)
  rest = keys project ids state rs
...     | true = keys project ids state rs
...     | false = key (Writes.Row.belief r) (Writes.scope r) (Writes.rubric r) ∷ keys project ids state rs

-- Text ordering is the configured PostgreSQL collation boundary.
keyBefore : (Text → Text → Bool) → Key → Key → Bool
keyBefore textBefore a b with Key.scope a ≟Text Key.scope b
... | no _ = textBefore (Key.scope a) (Key.scope b)
... | yes _ = textBefore (Key.rubric a) (Key.rubric b)

record Assessments : Set where
  constructor assessments
  field values : List (Key × Evaluation.Result); truncated : Bool

assessmentPage : (Text → Text → Bool) → Text → List UUID → Store.World → Assessments
assessmentPage textBefore project ids state = assessments
  (map (λ k → k , Read.scores (Selection.query project (Key.belief k) (Key.scope k) (Key.rubric k)) view)
    ordered) false
  where
  view = View.view state
  ordered = Ranking.sort (keyBefore textBefore) (keys project ids view (Read.World.contributions view))

admitted : Text → Maybe ℕ → Bool
admitted project nothing = nonblank project
admitted project (just limit) = nonblank project ∧ does (1 ≤? limit)

readAssessmentPage : (Text → Text → Bool) → Text → List UUID → Store.World → Store.World × Assessments
readAssessmentPage order project ids state = state , assessmentPage order project ids state

assessmentRetrievalPreservesState : ∀ order project ids state →
  proj₁ (readAssessmentPage order project ids state) ≡ state
assessmentRetrievalPreservesState order project ids state = refl

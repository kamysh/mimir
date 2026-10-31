{-# OPTIONS --safe #-}
-- Learning context composes retrieval, current observed pattern outcomes and
-- active assessment groups. It never activates a pattern or creates evidence.
module Mimir.LearningContext where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Float.Base using (_<ᵇ_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; map; filterᵇ; length; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤?_; _<?_)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; nonblank)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.RetrievalRanking as Ranking
import Mimir.CandidateGraph as Graph
import Mimir.PatternOutcomes as Patterns
import Mimir.LearningStore as Store
import Mimir.LearningAssessmentQueries as View
import Mimir.AssessmentRead as Read
import Mimir.AssessmentWrites as Writes
import Mimir.AssessmentSelection as Selection
import Mimir.AssessmentEvaluation as Evaluation
import Mimir.ReviewLedger as Ledger

textMember : Text → List Text → Bool
textMember term [] = false
textMember term (x ∷ xs) = does (term ≟Text x) ∨ textMember term xs

distinct : List Text → List Text
distinct [] = []
distinct (x ∷ xs) with textMember x xs
... | true = distinct xs
... | false = x ∷ distinct xs

tokens : Ranking.Unicode → Text → List Text
tokens unicode text = distinct (map (Ranking.Unicode.lowercase unicode)
  (Ranking.split (λ c → not (Ranking.Unicode.alphanumeric unicode c)) text))

tokenOverlap : Ranking.Unicode → Text → Graph.PatternValues → ℕ
tokenOverlap unicode query p = length (filterᵇ (λ term → textMember term situation) (tokens unicode query))
  where situation = tokens unicode (Graph.PatternValues.situation p)

-- Observed probabilities are finite and in [0,1]; on that domain Rust
-- total_cmp agrees with this ordering. UUID order resolves equal probabilities.
before : (ℕ × Patterns.Result) → (ℕ × Patterns.Result) → Bool
before (hits , a) (other , b) with hits ≟ other
... | no _ = does (other ≤? hits)
... | yes _ with Patterns.Result.observedSuccessProbability a ≡ᵇ Patterns.Result.observedSuccessProbability b
...   | false = Patterns.Result.observedSuccessProbability b <ᵇ Patterns.Result.observedSuccessProbability a
...   | true = does (Graph.PatternValues.identity (Patterns.Result.patternValue a) ≤?
  Graph.PatternValues.identity (Patterns.Result.patternValue b))

rank : ℕ → List (ℕ × Patterns.Result) → List Patterns.Result
rank limit rows = map (λ { (_ , p) → p }) (take limit (Ranking.sort before rows))

record Key : Set where
  constructor key
  field belief : ℕ; scope rubric : Text

sameKey : Key → Key → Bool
sameKey a b = does (Key.belief a ≟ Key.belief b) ∧
  does (Key.scope a ≟Text Key.scope b) ∧ does (Key.rubric a ≟Text Key.rubric b)

keyMember : Key → List Key → Bool
keyMember k [] = false
keyMember k (x ∷ xs) = sameKey k x ∨ keyMember k xs

keys : Text → List ℕ → Read.World → List Writes.Row → List Key
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

-- Text ordering is the configured PostgreSQL collation boundary. Numeric UUID
-- ordering and grouping are Mimir behavior. Do not silently replace the
-- database collation with the host language's Unicode scalar ordering.
keyBefore : (Text → Text → Bool) → Key → Key → Bool
keyBefore textBefore a b with Key.belief a ≟ Key.belief b
... | no _ = does (Key.belief a ≤? Key.belief b)
... | yes _ with Key.scope a ≟Text Key.scope b
...   | no _ = textBefore (Key.scope a) (Key.scope b)
...   | yes _ = textBefore (Key.rubric a) (Key.rubric b)

record Assessments : Set where
  constructor assessments
  field values : List (Key × Evaluation.Result); truncated : Bool

assessmentPage : (Text → Text → Bool) → Text → List ℕ → Store.World → Assessments
assessmentPage textBefore project ids state = assessments
  (map (λ k → k , Read.scores (Selection.query project (Key.belief k) (Key.scope k) (Key.rubric k)) view)
    (take 100 ordered)) (does (100 <? length ordered))
  where
  view = View.view state
  ordered = Ranking.sort (keyBefore textBefore) (keys project ids view (Read.World.contributions view))

admitted : Text → ℕ → Bool
admitted project limit = nonblank project ∧ does (1 ≤? limit) ∧ does (limit ≤? 20)

readAssessmentPage : (Text → Text → Bool) → Text → List ℕ → Store.World → Store.World × Assessments
readAssessmentPage order project ids state = state , assessmentPage order project ids state

assessmentRetrievalPreservesState : ∀ order project ids state →
  proj₁ (readAssessmentPage order project ids state) ≡ state
assessmentRetrievalPreservesState order project ids state = refl

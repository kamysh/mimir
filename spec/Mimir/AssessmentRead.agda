{-# OPTIONS --safe #-}
-- Concrete assessment read projections over the immutable review ledger.
-- Current scores and historical pages deliberately use different selection.
module Mimir.AssessmentRead where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; map; take; drop; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤?_; _<?_; _+_)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_; proj₁)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; nonblank)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.AssessmentWrites as Writes
import Mimir.AssessmentSelection as Selection
import Mimir.AssessmentEvaluation as Evaluation
import Mimir.ReviewLedger as Ledger
import Mimir.LearningSchema as Schema
import Mimir.RevisionBounds as Bounds
import Mimir.LearningTargets as Targets
import Mimir.Validation as Validation

record World : Set where
  constructor world
  field
    ledger : Ledger.World
    contributions : List Writes.Row
    createdAt : ℕ → ℕ → Maybe ℤ

record Entry : Set where
  constructor entry
  field
    contribution : Writes.Row
    experienceRevision : ℕ
    timestamp : Maybe ℤ
    active : Bool

version : ℕ → List Ledger.Version → Maybe Ledger.Version
version revision [] = nothing
version revision (v ∷ vs) with revision ≟ Ledger.Version.revision v
... | yes same = just v
... | no different = version revision vs

join : World → Writes.Row → Maybe Entry
join w c with version (Writes.Row.revision c)
  (Ledger.World.histories (World.ledger w) (Writes.Row.experience c))
... | nothing = nothing
... | just v = just (entry c (Ledger.Version.source v)
    (World.createdAt w (Writes.Row.experience c) (Writes.Row.revision c))
    (does (Ledger.R.Cell.review state ≟ Writes.Row.revision c) ∧
     does (Ledger.R.Cell.current state ≟ Ledger.Version.source v)))
  where state = Ledger.World.cells (World.ledger w) (Writes.Row.experience c)

matches : Selection.Query → World → Writes.Row → Bool
matches q w c =
  does (Selection.Query.project q ≟Text Ledger.R.Cell.project
    (Ledger.World.cells (World.ledger w) (Writes.Row.experience c))) ∧
  does (Selection.Query.belief q ≟ Writes.Row.belief c) ∧
  does (Selection.Query.scope q ≟Text Writes.scope c) ∧
  does (Selection.Query.rubric q ≟Text Writes.rubric c)

select : Selection.Query → World → List Writes.Row → List Entry
select q w [] = []
select q w (c ∷ cs) with matches q w c | join w c
... | true | just e = e ∷ select q w cs
... | _ | _ = select q w cs

activeRows : List Entry → List Writes.Row
activeRows [] = []
activeRows (e ∷ es) with Entry.active e
... | true = Entry.contribution e ∷ activeRows es
... | false = activeRows es

scores : Selection.Query → World → Evaluation.Result
scores q w = Evaluation.assess (activeRows (select q w (World.contributions w)))

data ScoreResult : Set where
  missingScope : ScoreResult
  invalidTarget : Validation.Fault → ScoreResult
  assessed : Selection.Query → Evaluation.Result → ScoreResult

getAssessment : Selection.Query → List Targets.Belief → World → ScoreResult
getAssessment q beliefs w with nonblank (Selection.Query.project q) ∧
  nonblank (Selection.Query.scope q) ∧ nonblank (Selection.Query.rubric q)
... | false = missingScope
... | true with Targets.checkReference (Selection.Query.project q) beliefs
  (Targets.reference (Selection.Query.belief q) (Validation.key "belief_id" ∷ []))
...   | Validation.rejected failure invalid = invalidTarget failure
...   | Validation.accepted valid = assessed q (scores q w)

-- Ascending SQL order: creation time, experience UUID, review revision.
-- Natural identities here use the UUID numeric order at the wire boundary.
beforeAt : ℤ → ℤ → Entry → Entry → Bool
beforeAt first second a b with first Integer.<? second
... | yes earlier = true
... | no notEarlier with first Integer.≟ second
...   | no different = false
...   | yes same with Writes.Row.experience (Entry.contribution a) <? Writes.Row.experience (Entry.contribution b)
...     | yes earlier = true
...     | no notEarlier with Writes.Row.experience (Entry.contribution a) ≟ Writes.Row.experience (Entry.contribution b)
...       | no different = false
...       | yes same = does (Writes.Row.revision (Entry.contribution a) ≤? Writes.Row.revision (Entry.contribution b))

before : Entry → Entry → Bool
before a b with Entry.timestamp a | Entry.timestamp b
... | just first | just second = beforeAt first second a b
... | _ | _ = false

timestampsPresent : List Entry → Bool
timestampsPresent [] = true
timestampsPresent (e ∷ es) with Entry.timestamp e
... | nothing = false
... | just time = timestampsPresent es

insert : Entry → List Entry → List Entry
insert a [] = a ∷ []
insert a (b ∷ bs) with before a b
... | true = a ∷ b ∷ bs
... | false = b ∷ insert a bs

sort : List Entry → List Entry
sort [] = []
sort (e ∷ es) = insert e (sort es)

record Page : Set where
  constructor mkPage
  field entries : List Entry; nextOffset : Maybe ℕ

page : ℕ → ℕ → List Entry → Page
page offset limit entries with limit <? length (drop offset entries)
... | yes more = mkPage (take limit (drop offset entries)) (just (offset + limit))
... | no finished = mkPage (take limit (drop offset entries)) nothing

data HistoryResult : Set where
  invalidPage missingProject invalidStoredHistory : HistoryResult
  found : Page → HistoryResult

history : Selection.Query → World → ℕ → ℕ → HistoryResult
history q w offset limit with does (1 ≤? limit) ∧ does (offset ≤? Bounds.i64Maximum)
... | false = invalidPage
... | true with nonblank (Selection.Query.project q)
...   | false = missingProject
...   | true with timestampsPresent (select q w (World.contributions w))
...     | false = invalidStoredHistory
...     | true = found (page offset limit (sort (select q w (World.contributions w))))

-- History returns the original immutable payload, not a re-evaluated review.
payload : Entry → Schema.Assessment
payload e = Writes.Row.payload (Entry.contribution e)

inactiveCannotContribute : ∀ e es → Entry.active e ≡ false → activeRows (e ∷ es) ≡ activeRows es
inactiveCannotContribute e es proof rewrite proof = refl

-- Both read interfaces return values without a write transition.
readScores : Selection.Query → List Targets.Belief → World → World × ScoreResult
readScores q beliefs w = w , getAssessment q beliefs w

readPreservesState : ∀ q beliefs w → proj₁ (readScores q beliefs w) ≡ w
readPreservesState q beliefs w = refl

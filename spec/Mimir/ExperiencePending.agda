{-# OPTIONS --safe #-}
-- The actual pending query preserves eligibility while filtering, sorting,
-- limiting and projecting stored rows. No database or JSON engine is proved.
module Mimir.ExperiencePending where

open import Data.Bool using (true; false; _∧_; not)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat using (_≟_; _≤?_)
import Data.Integer.Properties as Integer
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (member)
import Mimir.ExperienceRead as Read
import Mimir.PendingSelection as Pending
import Mimir.ReviewObservation as Observation
import Mimir.LearningQueryProtocol as Query
import Mimir.LearningStore as Store

absent : ∀ identity excluded → member identity excluded ≡ false → Pending.IDs.Absent identity excluded
absent identity [] noMember = []
absent identity (x ∷ xs) noMember with identity ≟ x
... | yes same with noMember
...   | ()
absent identity (x ∷ xs) noMember | no different = different ∷ absent identity xs noMember

notExcluded : ∀ a b → a ∧ not b ≡ true → b ≡ false
notExcluded false b ()
notExcluded true false selected = refl
notExcluded true true ()

unfinished : ∀ storedRow → Read.pending storedRow ≡ true → Pending.Pending (Read.storedSnapshot storedRow)
unfinished storedRow selected with Observation.Snapshot.reviewedRevision (Read.Row.snapshot storedRow)
  Integer.<? Observation.Snapshot.revision (Read.Row.snapshot storedRow)
... | yes pending = pending
... | no reviewed with selected
...   | ()

selectedEligible : ∀ project excluded rows →
  All (λ storedRow → Pending.Eligible excluded (Read.storedSnapshot storedRow)) (Read.select project true excluded rows)
selectedEligible project excluded [] = []
selectedEligible project excluded (storedRow ∷ rows)
  with Read.scopeMatches project storedRow ∧ not (member (Read.identity storedRow) excluded) in admitted
... | false = selectedEligible project excluded rows
... | true with Read.pending storedRow in pending
...   | false = selectedEligible project excluded rows
...   | true = (unfinished storedRow pending , absent (Read.identity storedRow) excluded
  (notExcluded (Read.scopeMatches project storedRow) (member (Read.identity storedRow) excluded) admitted)) ∷
  selectedEligible project excluded rows

insertPreserves : ∀ (P : Read.Row → Set) storedRow rows → P storedRow → All P rows → All P (Read.insert storedRow rows)
insertPreserves P storedRow [] valid [] = valid ∷ []
insertPreserves P storedRow (next ∷ rows) valid (nextValid ∷ rest) with Read.before storedRow next
... | true = valid ∷ nextValid ∷ rest
... | false = nextValid ∷ insertPreserves P storedRow rows valid rest

sortPreserves : ∀ (P : Read.Row → Set) rows → All P rows → All P (Read.sort rows)
sortPreserves P [] [] = []
sortPreserves P (storedRow ∷ rows) (valid ∷ rest) = insertPreserves P storedRow (Read.sort rows) valid (sortPreserves P rows rest)

queryEligible : ∀ project limit excluded rows batch →
  Read.pendingExperiences project limit excluded rows ≡ Read.selected batch → All (Pending.Eligible excluded) batch
queryEligible project limit excluded rows batch returned with does (1 ≤? limit)
... | false with returned
...   | ()
queryEligible project limit excluded rows batch returned | true with returned
... | refl = All.map⁺ (All.take⁺ limit
  (sortPreserves _ _ (selectedEligible project excluded rows)))

doneAgrees : ∀ (actual : Query.Result) events result → Query.E.Runs (Query.E.done actual) events result → actual ≡ result
doneAgrees actual .[] .actual (Query.E.returned .actual) = refl

pendingResultAgrees : ∀ actual batch → Query.pendingResult actual ≡ Query.pendingResult (Read.selected batch) →
  actual ≡ Read.selected batch
pendingResultAgrees .(Read.selected batch) batch refl = refl

publicQueryEligible : ∀ project limit excluded events batch →
  Query.E.Runs (Query.start (Query.pending project limit excluded)) events (Query.pendingResult (Read.selected batch)) →
  All (Pending.Eligible excluded) batch
publicQueryEligible project limit excluded events batch execution with does (1 ≤? limit)
... | false with execution
...   | ()
publicQueryEligible project limit excluded events batch execution | true with execution
... | Query.E.replied _ _ (inj₁ failure) ()
... | Query.E.replied _ _ (inj₂ observed) remaining = queryEligible project limit excluded (Store.World.current observed) batch
  (pendingResultAgrees _ batch (doneAgrees _ _ _ remaining))

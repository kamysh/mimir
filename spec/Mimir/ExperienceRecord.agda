{-# OPTIONS --safe #-}
-- Concrete recording/correction plan. Exact retries return the current
-- snapshot; fresh changes retract active review effects and recompute before
-- exposing a proposed transaction state.
module Mimir.ExperienceRecord where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; z≤n)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Integer using (ℤ; +_; ∣_∣) renaming (_-_ to _-ℤ_)
import Data.Integer.Properties as Integer
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.ExperienceSchema using (Experience)
import Mimir.ExperienceSchema as Schema
import Mimir.ExperienceRead as Read
import Mimir.ReviewObservation as Observation
import Mimir.LearningStore as Store
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewEdges as Edges
import Mimir.CandidateGraph as Graph
import Mimir.LearningTargets as Targets
import Mimir.ItemOwnerBatch as Owners
import Mimir.LearningCorrections as Corrections
import Mimir.LearningKeys as Keys
import Mimir.SemanticKey as Key
import Mimir.LearningRecompute as Recompute
import Mimir.PosteriorComputation as Posterior
import Mimir.ReviewNumericalPublication as Numerical
import Mimir.RevisionBounds as Bounds
import Mimir.Validation as Validation

data Failure : Set where
  invalid : Validation.Fault → Failure
  invalidExpected staleRevision missingPattern foreignPattern incoherentSnapshot : Failure
  numericFailure : Failure

data Decision : Set where
  rejected : Failure → Decision
  replay : Observation.Snapshot → Decision
  fresh : Store.World → Observation.Snapshot → Bool → Decision

patternAllowed : Text → UUID → List Graph.Node → Maybe Bool
patternAllowed project id [] = nothing
patternAllowed project id (Graph.beliefNode b ∷ ns) = patternAllowed project id ns
patternAllowed project id (Graph.patternNode p ∷ ns) with id ≟UUID Graph.PatternValues.identity p
... | no different = patternAllowed project id ns
... | yes same with Graph.PatternValues.project p
...   | nothing = just true
...   | just actual = just (does (project ≟Text actual))

sourceLedger : Experience → Maybe Observation.Snapshot → Ledger.World → Ledger.World
sourceLedger e (just old) ledger = Ledger.correct (Experience.identity e) ledger
sourceLedger e nothing ledger = Ledger.world
  (Ledger.Cells.write (Experience.identity e)
    (Ledger.R.cell (Experience.project e) 1 0 0 nothing z≤n) (Ledger.World.cells ledger))
  (Ledger.Histories.write (Experience.identity e) [] (Ledger.World.histories ledger))

newSnapshot : Experience → ℕ → Maybe Observation.Snapshot → Observation.Snapshot
newSnapshot e revision nothing = Observation.snapshot e (+ revision) (+ 0) (+ 0) []
newSnapshot e revision (just old) = Observation.snapshot e (+ revision)
  (Observation.Snapshot.reviewRevision old) (Observation.Snapshot.reviewedRevision old)
  []

prepare : (calculation : Posterior.Calculation) → Store.World → Experience → ℕ → ℤ → Maybe Observation.Snapshot → Decision
prepare calculation before e expected now old with Owners.prepare (Experience.identity e)
  (Publication.World.owners (Store.World.publication before)) (Experience.items e)
... | inj₁ failure = rejected (invalid failure)
... | inj₂ (owners , ownership) with Recompute.run calculation (Experience.project e)
  (Numerical.oldTargets (Ledger.activeApplied
    (Ledger.World.cells priorLedger (Experience.identity e))
    (Ledger.World.histories priorLedger (Experience.identity e))))
  (Publication.World.nodes p) (Edges.replace (Experience.identity e) [] (Publication.World.edges p))
  (Recompute.activeReviews (Experience.project e) (Store.identities before) nextLedger)
  (Store.World.grounding before)
  where
  p = Store.World.publication before
  priorLedger = Publication.World.ledger p
  nextLedger = sourceLedger e old priorLedger
...   | Recompute.foreignTarget = rejected numericFailure
...   | Recompute.invalidNumericInput = rejected numericFailure
...   | Recompute.invalidNumericWrite = rejected numericFailure
...   | Recompute.recomputed nodes limit = fresh
  (record before
    { publication = record (Store.World.publication before)
      { ledger = sourceLedger e old (Publication.World.ledger (Store.World.publication before))
      ; owners = owners ; nodes = nodes
      ; edges = Edges.replace (Experience.identity e) [] (Publication.World.edges (Store.World.publication before)) }
    ; current = Store.put result now (Store.World.current before)
    ; sources = Store.sourceVersion e (suc expected) now ∷ Store.World.sources before }) result limit
  where result = newSnapshot e (suc expected) old

checkPattern : (calculation : Posterior.Calculation) → Store.World → Experience → ℕ → ℤ → Maybe Observation.Snapshot → Decision
checkPattern calculation before e expected now old with Experience.patternID e
... | nothing = prepare calculation before e expected now old
... | just id with patternAllowed (Experience.project e) id (Publication.World.nodes (Store.World.publication before))
...   | nothing = rejected missingPattern
...   | just false = rejected foreignPattern
...   | just true = prepare calculation before e expected now old

checkTargets : (calculation : Posterior.Calculation) → Store.World → Experience → ℕ → ℤ → Maybe Observation.Snapshot → Decision
checkTargets calculation before e expected now old with Targets.validate (Experience.project e)
  (map Recompute.target (Recompute.beliefs (Publication.World.nodes (Store.World.publication before)))) (Experience.beliefIDs e)
... | Validation.rejected failure refutation = rejected (invalid failure)
... | Validation.accepted valid = checkPattern calculation before e expected now old

coherent : Store.World → Observation.Snapshot → Bool
coherent before old =
  does (Ledger.R.Cell.project cell ≟Text Experience.project (Observation.Snapshot.experience old)) ∧
  does ((+ Ledger.R.Cell.current cell) Integer.≟ Observation.Snapshot.revision old) ∧
  does ((+ Ledger.R.Cell.review cell) Integer.≟ Observation.Snapshot.reviewRevision old) ∧
  does ((+ Ledger.R.Cell.acknowledged cell) Integer.≟ Observation.Snapshot.reviewedRevision old)
  where cell = Ledger.World.cells (Publication.World.ledger (Store.World.publication before))
          (Experience.identity (Observation.Snapshot.experience old))

existing : (calculation : Posterior.Calculation) → Store.World → Experience → ℤ → ℤ → Observation.Snapshot → Decision
existing calculation before e expected now old with Observation.checkSnapshot old
... | Validation.rejected failure refutation = rejected (invalid failure)
... | Validation.accepted valid with coherent before old
...   | false = rejected incoherentSnapshot
...   | true with Corrections.validateExperienceCorrection (Observation.Snapshot.experience old) e
...     | Validation.rejected failure refutation = rejected (invalid failure)
...     | Validation.accepted retained with
  does (Key.equal (Keys.experience (Observation.Snapshot.experience old)) (Keys.experience e)) ∧
  (does (expected Integer.≟ Observation.Snapshot.revision old) ∨
   does (expected Integer.≟ (Observation.Snapshot.revision old -ℤ (+ 1))))
...       | true = replay old
...       | false with expected Integer.≟ Observation.Snapshot.revision old
...         | no stale = rejected staleRevision
...         | yes same = checkTargets calculation before e ∣ expected ∣ now (just old)

plan : (calculation : Posterior.Calculation) → Store.World → Experience → ℤ → ℤ → Decision
plan calculation before e expected now with Schema.validate e
... | Validation.rejected failure refutation = rejected (invalid failure)
... | Validation.accepted valid with does ((+ 0) Integer.≤? expected) ∧ does (expected Integer.<? (+ Bounds.i64Maximum))
...   | false = rejected invalidExpected
...   | true with Read.get (Experience.identity e) (Store.World.current before)
...     | just old = existing calculation before e expected now old
...     | nothing with expected Integer.≟ (+ 0)
...       | no stale = rejected staleRevision
...       | yes initial = checkTargets calculation before e 0 now nothing

proposed : Store.World → Decision → Store.World
proposed before (rejected failure) = before
proposed before (replay receipt) = before
proposed before (fresh after receipt limit) = after

retryPreservesAllState : ∀ before receipt → proposed before (replay receipt) ≡ before
retryPreservesAllState before receipt = refl

rejectionPreservesAllState : ∀ before failure → proposed before (rejected failure) ≡ before
rejectionPreservesAllState before failure = refl

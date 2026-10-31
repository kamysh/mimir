{-# OPTIONS --safe #-}
-- Compose review classification, active evidence and immutable review history.
-- Histories are newest first. Native SQL must realize the complete write set.
module Mimir.ReviewJournal where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; subst)
import Mimir.LearningContracts as Contracts
import Mimir.LearningPublication as Publication
import Mimir.ReviewPlan as Plan
import Mimir.DatabaseTransaction as Database

module Over (Payload Contribution : Set) (equal : DecidableEquality Payload)
  (materialize : Payload → Contribution) where
  module L = Publication.Over Payload Contribution equal materialize
  module R = L.R
  module C = L.C
  module P = Plan.Over Payload equal

  record Entry : Set where
    constructor version
    field source revision : ℕ; submitted : Payload; effects : Contribution

  module Histories = Contracts.Ownership (List Entry)

  -- Every retained version occurs at its actual revision, without gaps or
  -- duplicates. This is stronger than equating the history length to a counter.
  data Ordered : ℕ → List Entry → Set where
    empty : Ordered 0 []
    newest : ∀ {revision entry rest} → Entry.revision entry ≡ suc revision →
      Ordered revision rest → Ordered (suc revision) (entry ∷ rest)

  orderedCount : ∀ {revision entries} → Ordered revision entries → length entries ≡ revision
  orderedCount empty = refl
  orderedCount (newest same prior) = cong suc (orderedCount prior)

  record World : Set where
    constructor world
    field active : L.World; histories : ℕ → List Entry
  open World

  Consistent : World → Set
  Consistent before = L.Consistent (active before) ×
    (∀ identity → Ordered (R.Cell.review (L.World.cells (active before) identity)) (histories before identity))

  SameAt : World → World → ℕ → Set
  SameAt first second identity = L.SameAt (active first) (active second) identity ×
    histories first identity ≡ histories second identity

  current : World → ℕ → R.Cell
  current before identity = L.World.cells (active before) identity

  next : ℕ → World → Payload → Entry
  next identity before payload = version (R.Cell.current (current before identity))
    (suc (R.Cell.review (current before identity))) payload (materialize payload)

  fresh : ℕ → World → Payload → World
  fresh identity before payload = world
    (L.install identity (R.commit (current before identity) payload) (active before))
    (Histories.write identity (next identity before payload ∷ histories before identity) (histories before))

  apply : ∀ identity before payload {after} → P.Plan (current before identity) payload after → World
  apply identity before payload P.refused = before
  apply identity before payload P.replayed = before
  apply identity before payload P.fresh = fresh identity before payload

  classify : ∀ identity before (submitted : C.Request) →
    P.Plan (current before identity) (C.Request.payload submitted) (C.planned (current before identity) submitted)
  classify identity before submitted = P.classify (current before identity)
    (C.Request.owner submitted) (C.Request.source submitted) (C.Request.expected submitted)
    (C.Request.payload submitted) (C.Request.validTargets submitted)

  proposed : ℕ → World → C.Request → World
  proposed identity before submitted = apply identity before (C.Request.payload submitted) (classify identity before submitted)

  historyInstalled : ∀ identity before payload → histories (fresh identity before payload) identity ≡
    next identity before payload ∷ histories before identity
  historyInstalled identity before payload = Histories.write-own identity
    (next identity before payload ∷ histories before identity)
    (histories before)

  historyRetained : ∀ identity before payload entry → entry ∈ histories before identity →
    entry ∈ histories (fresh identity before payload) identity
  historyRetained identity before payload entry member = subst (λ history → entry ∈ history)
    (Relation.Binary.PropositionalEquality.sym
     (historyInstalled identity before payload))
    (there member)

  freshConsistent : ∀ identity before payload → Consistent before → Consistent (fresh identity before payload)
  freshConsistent identity before payload (activeConsistent , historyConsistent) =
    L.installConsistent identity (R.commit (current before identity) payload) (active before) activeConsistent , counts
    where
    counts : ∀ queried → Ordered (R.Cell.review (current (fresh identity before payload) queried))
      (histories (fresh identity before payload) queried)
    counts queried with queried ≟ identity
    ... | yes refl = newest refl (historyConsistent queried)
    ... | no distinct = historyConsistent queried

  freshUnrelated : ∀ identity before payload other → other ≢ identity →
    SameAt (fresh identity before payload) before other
  freshUnrelated identity before payload other distinct = L.unrelatedPreserved identity
    (R.commit (current before identity) payload) (active before) other
    distinct
    ,
    Histories.write-other identity other
    (next identity before payload ∷ histories before identity)
    (histories before) distinct

  applyConsistent : ∀ identity before payload {after} (plan : P.Plan (current before identity) payload after) →
    Consistent before → Consistent (apply identity before payload plan)
  applyConsistent identity before payload P.refused consistent = consistent
  applyConsistent identity before payload P.replayed consistent = consistent
  applyConsistent identity before payload P.fresh consistent = freshConsistent identity before payload consistent

  replayUnchanged : ∀ identity before payload {after} (plan : P.Plan (current before identity) payload after) →
    P.IsReplay plan → apply identity before payload plan ≡ before
  replayUnchanged identity before payload P.replayed P.isReplay = refl

  exactRetryUnchanged : ∀ identity before original payload valid →
    current before identity ≡ R.commit original payload →
    proposed identity before (C.originalRequest original payload valid) ≡ before
  exactRetryUnchanged identity before original payload valid committed = replayUnchanged identity before payload
    (classify identity before
     (C.originalRequest original payload valid))
    (P.unchangedMeansReplay (current before identity) payload
     (classify identity before
      (C.originalRequest original payload valid))
     (L.exactRetryPlan identity (active before) original payload valid
      committed))

  correction : ℕ → World → World
  correction identity before = world (L.correction identity (active before)) (histories before)

  correctionPreservesHistory : ∀ identity before queried →
    histories (correction identity before) queried ≡ histories before queried
  correctionPreservesHistory identity before queried = refl

  correctionConsistent : ∀ identity before → Consistent before → Consistent (correction identity before)
  correctionConsistent identity before (activeConsistent , historyConsistent) =
    L.installConsistent identity (R.correct (current before identity)) (active before) activeConsistent , counts
    where
    counts : ∀ queried → Ordered (R.Cell.review (current (correction identity before) queried))
      (histories before queried)
    counts queried with queried ≟ identity
    ... | yes refl = historyConsistent queried
    ... | no distinct = historyConsistent queried

  -- Apply a completed native transaction only through its whole-write-set
  -- obligation. No partial publication of history versus active evidence is
  -- admitted by this boundary, including when the acknowledgement is lost.
  module Native (database : Database.Contract World) where
    module D = Database.Contract database

    publicationConsistent : ∀ (event : D.Completion) identity submitted →
      Consistent (D.before event) →
      D.proposed event ≡ proposed identity (D.before event) submitted →
      Consistent (D.published event)
    publicationConsistent event identity submitted consistent writes = Database.invariantPreserved Consistent (D.atomicity event)
      consistent
      (subst Consistent
       (Relation.Binary.PropositionalEquality.sym writes)
       (applyConsistent identity (D.before event)
        (C.Request.payload submitted)
        (classify identity (D.before event) submitted) consistent))

    exactRetryPreserves : ∀ (event : D.Completion) identity original payload valid →
      current (D.before event) identity ≡ R.commit original payload →
      D.proposed event ≡ proposed identity (D.before event) (C.originalRequest original payload valid) →
      D.published event ≡ D.before event
    exactRetryPreserves event identity original payload valid committed writes = Database.invariantPreserved (λ state → state ≡ D.before event)
      (D.atomicity event) refl
      (trans writes
       (exactRetryUnchanged identity (D.before event) original payload
        valid committed))

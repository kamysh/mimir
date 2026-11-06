{-# OPTIONS --safe #-}
-- The public review plan, not an independent journal-only example. A stale
-- request cannot enter candidate, assessment, edge or numeric publication.
module Mimir.ReviewCompetition where

open import Data.Bool using (true; false)
open import Data.List using (List; map)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Integer using (ℤ; +_; ∣_∣)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Mimir.ReviewSchema using (Review)
open import Mimir.LearningCandidates using (Candidate)
import Mimir.ExperienceSchema as Experience
import Mimir.ExperienceRead as Read
import Mimir.ExperienceRecord as Recording
import Mimir.ReviewRecord as Reviewing
import Mimir.ReviewObservation as Observation
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewLedger as Ledger
import Mimir.LearningStore as Store
import Mimir.LearningOperations as Operations
import Mimir.LearningTransactionDatabase as Database
import Mimir.CandidateGraph as Graph
import Mimir.CandidateRegistry as Registry
import Mimir.Validation as Validation
import Mimir.DatabaseReadCommitted as Committed
import Mimir.DatabaseAdvisoryLock as Lock
import Mimir.LearningKeys as Keys
import Mimir.LearningContracts as Contracts
import Mimir.NativeLockOrder as NativeOrder
open import Data.Sum using (_⊎_; inj₁; inj₂)

reviewRevision : Store.World → ℕ → ℕ
reviewRevision before identity = Ledger.R.Cell.review
  (Ledger.World.cells (Publication.World.ledger (Store.World.publication before)) identity)

module First (before : Store.World) (old : Observation.Snapshot) (requested : Review)
  (expected : ℕ) (clock : Candidate → ℤ) (now : ℤ)
  (unique : Registry.IDs.Unique (map Graph.nodeID (Publication.World.nodes (Store.World.publication before)))) where
  module V = Reviewing.For before old requested expected clock now unique
  module N = V.N

  after : (selected : N.F.Fresh expected) (nodes : Data.List.List Graph.Node) →
    map Graph.nodeID nodes ≡ map Graph.nodeID (Publication.World.nodes (N.F.publish selected)) → Data.Bool.Bool → Store.World
  after selected nodes same limit = Reviewing.proposed before (V.convert (N.fresh selected nodes same limit))

  abstract
    advancesExactlyOnce : ∀ selected nodes same limit →
      reviewRevision (after selected nodes same limit) (Experience.Experience.identity (Observation.Snapshot.experience old)) ≡ suc expected
    advancesExactlyOnce selected nodes same limit
      rewrite Ledger.Cells.write-own (Experience.Experience.identity (Observation.Snapshot.experience old))
        (Ledger.R.commit N.F.state (Keys.review requested))
        (Ledger.World.cells (Publication.World.ledger (Store.World.publication before))) =
      cong suc (sym (N.F.Fresh.expectedMatches selected))

module For (database : ℕ) (requested : Review) (expected : ℤ)
  (clock : Candidate → ℤ) (now : ℤ) (identities : Candidate → ℕ) where
  request = Operations.reviewExperience requested expected
  module P = Operations.Protocol database request clock now identities
  module D = Database.Over Store.World Observation.Snapshot Operations.Failure database 671942183

  module Bound (locks : Lock.Contract) (reads : Committed.Contract Store.World)
    (nativeDatabase : Lock.Contract.Database locks) (nativeKey : Lock.Contract.Key locks)
    (nativeTransaction : ℕ → Lock.Contract.Transaction locks) where
    module A = D.AfterPeer locks reads nativeDatabase nativeKey nativeTransaction
    module B = A.B

    module Against (before : Store.World) (old : Observation.Snapshot) (expectedNat : ℕ)
      (unique : Registry.IDs.Unique (map Graph.nodeID (Publication.World.nodes (Store.World.publication before)))) where
      module V = Reviewing.For before old requested expectedNat clock now unique
      module N = V.N

      abstract
        numericInert : expectedNat ≢ reviewRevision before (Experience.Experience.identity (Observation.Snapshot.experience old)) →
          ∀ decision → B.Inert (P.reviewed (V.convert decision))
        numericInert stale (N.refused failure) = B.reject _
        numericInert stale (N.numericFailure failure) = B.reject _
        numericInert stale (N.replay receipt) = B.replay _
        numericInert stale (N.fresh selected nodes same limit) = ⊥-elim (stale (N.F.Fresh.expectedMatches selected))

      abstract
        numericAdvanced : ∀ decision after resultSnapshot → P.reviewed (V.convert decision) ≡ P.T.replace after resultSnapshot →
          reviewRevision after (Experience.Experience.identity (Observation.Snapshot.experience old)) ≡ suc expectedNat
        numericAdvanced (N.refused failure) after resultSnapshot ()
        numericAdvanced (N.numericFailure failure) after resultSnapshot ()
        numericAdvanced (N.replay receipt) after resultSnapshot ()
        numericAdvanced (N.fresh selected nodes same limit) after resultSnapshot refl =
          First.advancesExactlyOnce before old requested expectedNat clock now unique selected nodes same limit

    abstract
      checkStateInert : ∀ before old expectedNat →
        expectedNat ≢ reviewRevision before (Experience.Experience.identity (Observation.Snapshot.experience old)) →
        B.Inert (P.reviewed (Reviewing.checkState before old requested expectedNat clock now identities))
      checkStateInert before old expectedNat stale with Observation.checkSnapshot old
      ... | Validation.rejected failure invalid = B.reject _
      ... | Validation.accepted valid with Recording.coherent before old
      ...   | false = B.reject _
      ...   | true with Registry.IDs.checkUnique (map Graph.nodeID (Publication.World.nodes (Store.World.publication before)))
      ...     | Validation.rejected failure invalid = B.reject _
      ...     | Validation.accepted unique = Against.numericInert before old expectedNat unique stale
        (Against.N.plan before old expectedNat unique identities)

    abstract
      checkStateAdvanced : ∀ before old expectedNat after resultSnapshot →
        P.reviewed (Reviewing.checkState before old requested expectedNat clock now identities) ≡ P.T.replace after resultSnapshot →
        reviewRevision after (Experience.Experience.identity (Observation.Snapshot.experience old)) ≡ suc expectedNat
      checkStateAdvanced before old expectedNat after resultSnapshot observed with Observation.checkSnapshot old
      ... | Validation.rejected failure invalid with observed
      ...   | ()
      checkStateAdvanced before old expectedNat after resultSnapshot observed | Validation.accepted valid with Recording.coherent before old
      ... | false with observed
      ...   | ()
      checkStateAdvanced before old expectedNat after resultSnapshot observed | Validation.accepted valid | true
        with Registry.IDs.checkUnique (map Graph.nodeID (Publication.World.nodes (Store.World.publication before)))
      ... | Validation.rejected failure invalid with observed
      ...   | ()
      checkStateAdvanced before old expectedNat after resultSnapshot observed | Validation.accepted valid | true | Validation.accepted unique =
        Against.numericAdvanced before old expectedNat unique (Against.N.plan before old expectedNat unique identities) after resultSnapshot observed

    abstract
      planInert : ∀ before → ∣ expected ∣ ≢ reviewRevision before (Review.experienceID requested) →
        B.Inert (P.decide request before)
      planInert before stale with Operations.expectedValid expected
      ... | false = B.reject _
      ... | true with Read.get (Review.experienceID requested) (Store.World.current before) in found
      ...   | nothing = B.reject _
      ...   | just old = checkStateInert before old ∣ expected ∣ (λ same → stale
        (trans same (cong (reviewRevision before)
          (Read.lookupIdentity (Review.experienceID requested) (Store.World.current before) old found))))

    abstract
      freshProposalAdvances : ∀ before after resultSnapshot → P.decide request before ≡ P.T.replace after resultSnapshot →
        reviewRevision after (Review.experienceID requested) ≡ suc ∣ expected ∣
      freshProposalAdvances before after resultSnapshot observed with Operations.expectedValid expected
      ... | false with observed
      ...   | ()
      freshProposalAdvances before after resultSnapshot observed | true
        with Read.get (Review.experienceID requested) (Store.World.current before) in found
      ... | nothing with observed
      ...   | ()
      freshProposalAdvances before after resultSnapshot observed | true | just old =
        trans (cong (reviewRevision after)
          (sym (Read.lookupIdentity (Review.experienceID requested) (Store.World.current before) old found)))
          (checkStateAdvanced before old ∣ expected ∣ after resultSnapshot observed)

    abstract
      publicTransactionCannotPublish : ∀ before events after result →
        ∣ expected ∣ ≢ reviewRevision before (Review.experienceID requested) →
        B.Runs P.Plan.start (B.beginning before) events after result → after ≡ B.finished before
      publicTransactionCannotPublish before events after result stale =
        A.startCannotPublish (P.decide request) before events after result (planInert before stale)

-- Both programs are the actual public review transaction, with arbitrary
-- payloads and the same requested old counter. Native lease order selects
-- which program is first; actual read replies are derived by the binding.
module Competing (database : ℕ) (first second : Review) (expected : ℕ)
  (firstClock secondClock : Candidate → ℤ) (firstNow secondNow : ℤ)
  (firstIDs secondIDs : Candidate → ℕ)
  (sameTarget : Review.experienceID first ≡ Review.experienceID second) where
  module F = For database first (+ expected) firstClock firstNow firstIDs
  module S = For database second (+ expected) secondClock secondNow secondIDs

  module Bound (locks : Lock.Contract) (reads : Committed.Contract Store.World)
    (nativeDatabase : Lock.Contract.Database locks) (nativeKey : Lock.Contract.Key locks)
    (nativeTransaction : ℕ → Lock.Contract.Transaction locks) where
    module A = F.Bound locks reads nativeDatabase nativeKey nativeTransaction
    module C = S.Bound locks reads nativeDatabase nativeKey nativeTransaction

    firstWrites secondWrites : Store.World → Store.World
    firstWrites before = F.D.writeSet before (F.P.decide F.request before)
    secondWrites before = S.D.writeSet before (S.P.decide S.request before)

    Final : Store.World → C.B.Session → Set
    Final before after = (after ≡ C.B.finished before) ⊎
      ((after ≡ C.B.finished (firstWrites before)) ⊎ (after ≡ C.B.finished (secondWrites before)))

    abstract
      withoutFirstPublication : ∀ before events after result →
        C.B.Runs S.P.Plan.start (C.B.beginning before) events after result → Final before after
      withoutFirstPublication before events after result execution
        with C.A.startPublication (S.P.decide S.request) before events after result execution
      ... | inj₁ sameBefore = inj₁ sameBefore
      ... | inj₂ saved = inj₂ (inj₂ saved)

    abstract
      afterFirstProposal : ∀ before events after result →
        C.B.Runs S.P.Plan.start (C.B.beginning (firstWrites before)) events after result → Final before after
      afterFirstProposal before events after result execution with F.P.decide F.request before in chosen
      ... | F.P.T.reject detail = Data.Sum.map (λ same → same) inj₂
        (C.A.startPublication (S.P.decide S.request) before events after result execution)
      ... | F.P.T.replay value = Data.Sum.map (λ same → same) inj₂
        (C.A.startPublication (S.P.decide S.request) before events after result execution)
      ... | F.P.T.replace proposed resultSnapshot = inj₂ (inj₁
        (C.publicTransactionCannotPublish proposed events after result
          (λ repeated → Contracts.not-successor expected (trans repeated
            (trans (cong (reviewRevision proposed) (sym sameTarget))
              (A.freshProposalAdvances before proposed resultSnapshot chosen)))) execution))

    -- This starts at begin for BOTH operations, rather than giving either
    -- classifier a caller-selected read state. Read, rollback, write, commit
    -- and lost-confirmation cases come from the actual bound executions.
    abstract
      completePrograms : ∀ before firstEvents actualFirst firstResult secondEvents after result →
        A.B.Runs F.P.Plan.start (A.B.beginning before) firstEvents (A.B.finished actualFirst) firstResult →
        C.B.Runs S.P.Plan.start (C.B.beginning actualFirst) secondEvents after result → Final before after
      completePrograms before firstEvents actualFirst firstResult secondEvents after result firstRun secondRun
        with A.A.startPublication (F.P.decide F.request) before firstEvents (A.B.finished actualFirst) firstResult firstRun
      ... | inj₁ sameBefore rewrite cong A.B.view sameBefore =
        withoutFirstPublication before secondEvents after result secondRun
      ... | inj₂ saved rewrite cong A.B.view saved =
        afterFirstProposal before secondEvents after result secondRun

    record Execution (firstTx secondTx : ℕ) (before : Store.World) (after : C.B.Session) : Set where
      field
        firstEvents : List F.P.T.E.Event
        firstActual : Store.World
        firstResult : F.P.T.Outcome
        firstRun : A.B.Runs F.P.Plan.start (A.B.beginning before) firstEvents (A.B.finished firstActual) firstResult
        firstOwned : A.B.HeldAt firstTx
        firstAcquired : A.A.acquisition (F.P.decide F.request) before firstEvents (A.B.finished firstActual) firstResult firstRun ≡ just (firstTx , firstOwned)
        secondEvents : List S.P.T.E.Event
        secondResult : S.P.T.Outcome
        secondRun : C.B.Runs S.P.Plan.start (C.B.beginning firstActual) secondEvents after secondResult
        secondOwned : C.B.HeldAt secondTx
        secondAcquired : C.A.acquisition (S.P.decide S.request) firstActual secondEvents after secondResult secondRun ≡ just (secondTx , secondOwned)

    abstract
      executionResult : ∀ firstTx secondTx before after → Execution firstTx secondTx before after → Final before after
      executionResult firstTx secondTx before after observed = completePrograms before
        (Execution.firstEvents observed) (Execution.firstActual observed) (Execution.firstResult observed)
        (Execution.secondEvents observed) after (Execution.secondResult observed) (Execution.firstRun observed) (Execution.secondRun observed)

-- A single statement for either actual lock order, rather than a selected
-- winning reviewer. Native observations must use the same two handles and
-- acquisition snapshots as the shared lease history.
module BothOrders (database : ℕ) (first second : Review) (expected : ℕ)
  (firstClock secondClock : Candidate → ℤ) (firstNow secondNow : ℤ)
  (firstIDs secondIDs : Candidate → ℕ)
  (sameTarget : Review.experienceID first ≡ Review.experienceID second) where
  module Forward = Competing database first second expected firstClock secondClock firstNow secondNow firstIDs secondIDs sameTarget
  module Reverse = Competing database second first expected secondClock firstClock secondNow firstNow secondIDs firstIDs (sym sameTarget)

  module Bound (locks : Lock.Contract) (reads : Committed.Contract Store.World)
    (nativeDatabase : Lock.Contract.Database locks) (nativeKey : Lock.Contract.Key locks)
    (nativeTransaction : ℕ → Lock.Contract.Transaction locks)
    (snapshotAt : ℕ → Lock.Contract.Snapshot locks) where
    module F = Forward.Bound locks reads nativeDatabase nativeKey nativeTransaction
    module R = Reverse.Bound locks reads nativeDatabase nativeKey nativeTransaction
    module Order = NativeOrder.Over locks snapshotAt nativeDatabase nativeKey

    abstract
      reverseResult : ∀ firstTx secondTx before after → R.Execution secondTx firstTx before after → F.Final before after
      reverseResult firstTx secondTx before after observed with R.executionResult secondTx firstTx before after observed
      ... | inj₁ sameBefore = inj₁ sameBefore
      ... | inj₂ (inj₁ secondSaved) = inj₂ (inj₂ secondSaved)
      ... | inj₂ (inj₂ firstSaved) = inj₂ (inj₁ firstSaved)

    ForwardEvidence : ∀ firstTx secondTx → Order.Span (nativeTransaction firstTx) → Order.Span (nativeTransaction secondTx) →
      Store.World → F.C.B.Session → Set
    ForwardEvidence firstTx secondTx a b before after = Σ (F.Execution firstTx secondTx before after) (λ observed →
      F.A.B.HeldAt.snapshot (F.Execution.firstOwned observed) ≡ snapshotAt (Order.Span.acquired a) ×
      F.C.B.HeldAt.snapshot (F.Execution.secondOwned observed) ≡ snapshotAt (Order.Span.acquired b))

    ReverseEvidence : ∀ firstTx secondTx → Order.Span (nativeTransaction firstTx) → Order.Span (nativeTransaction secondTx) →
      Store.World → F.C.B.Session → Set
    ReverseEvidence firstTx secondTx a b before after = Σ (R.Execution secondTx firstTx before after) (λ observed →
      R.A.B.HeldAt.snapshot (R.Execution.firstOwned observed) ≡ snapshotAt (Order.Span.acquired b) ×
      R.C.B.HeldAt.snapshot (R.Execution.secondOwned observed) ≡ snapshotAt (Order.Span.acquired a))

    abstract
      completeInNativeOrder : ∀ firstTx secondTx before after → nativeTransaction firstTx ≢ nativeTransaction secondTx →
        (a : Order.Span (nativeTransaction firstTx)) (b : Order.Span (nativeTransaction secondTx)) →
        (Order.Span.ended a Data.Nat.≤ Order.Span.acquired b → ForwardEvidence firstTx secondTx a b before after) →
        (Order.Span.ended b Data.Nat.≤ Order.Span.acquired a → ReverseEvidence firstTx secondTx a b before after) → F.Final before after
      completeInNativeOrder firstTx secondTx before after different a b forward reverse
        with Order.order (nativeTransaction firstTx) (nativeTransaction secondTx) different a b
      ... | inj₁ firstEnded with forward firstEnded
      ...   | observed , aligned = F.executionResult firstTx secondTx before after observed
      completeInNativeOrder firstTx secondTx before after different a b forward reverse | inj₂ secondEnded with reverse secondEnded
      ... | observed , aligned = reverseResult firstTx secondTx before after observed

{-# OPTIONS --safe #-}
-- Begin-trace effect order, including a distinct clock read for each old
-- running trace. UUID generation is input and carries no freshness axiom.
module Mimir.JudgeTraceStart where

open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_; suc)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.Effects as Effects
import Mimir.JudgeStateRecords as Records

module Over (Id : Set) (equal : (x y : Id) → Dec (x ≡ y)) where
  module R = Records.Over Id

  interruptTrace : Maybe ℕ → R.Trace → R.Trace
  interruptTrace observed before = record before
    { status = toList "interrupted" ; finishedAt = just (Records.clock observed) }

  data Interrupted : List R.Trace → List R.Trace → Set where
    empty : Interrupted [] []
    unchanged : ∀ before rest after → R.Trace.status before ≢ toList "running" → Interrupted rest after →
      Interrupted (before ∷ rest) (before ∷ after)
    marked : ∀ observed before rest after → R.Trace.status before ≡ toList "running" → Interrupted rest after →
      Interrupted (before ∷ rest) (interruptTrace observed before ∷ after)

  sameLength : ∀ {before after} → Interrupted before after → length after ≡ length before
  sameLength empty = refl
  sameLength (unchanged before rest after skipped later) = cong suc (sameLength later)
  sameLength (marked observed before rest after running later) = cong suc (sameLength later)

  sameIdentities : ∀ {before after} → Interrupted before after → map R.Trace.identity after ≡ map R.Trace.identity before
  sameIdentities empty = refl
  sameIdentities (unchanged before rest after skipped later) = cong (R.Trace.identity before ∷_) (sameIdentities later)
  sameIdentities (marked observed before rest after running later) = cong (R.Trace.identity before ∷_) (sameIdentities later)

  -- Only lifecycle status and finish time may change when an abandoned run
  -- is marked interrupted. Every other field of every old attempt survives.
  evidence : R.Trace → R.Trace
  evidence before = record before { status = [] ; finishedAt = nothing }

  sameEvidence : ∀ {before after} → Interrupted before after →
    map evidence after ≡ map evidence before
  sameEvidence empty = refl
  sameEvidence (unchanged before rest after skipped later) = cong (evidence before ∷_) (sameEvidence later)
  sameEvidence (marked observed before rest after running later) = cong (evidence before ∷_) (sameEvidence later)

  interruptedNotRunning : toList "interrupted" ≢ toList "running"
  interruptedNotRunning ()

  noStaleRunningTrace : ∀ {before after} → Interrupted before after → All (λ trace → R.Trace.status trace ≢ toList "running") after
  noStaleRunningTrace empty = []
  noStaleRunningTrace (unchanged before rest after skipped later) = skipped ∷ noStaleRunningTrace later
  noStaleRunningTrace (marked observed before rest after running later) = interruptedNotRunning ∷ noStaleRunningTrace later

  data Operation : Set where
    readDiagnostics clock newId : Operation
    writeDiagnostics : List R.Trace → Operation

  Reply : Operation → Set
  Reply readDiagnostics = Text ⊎ List R.Trace
  Reply clock = Maybe ℕ
  Reply newId = Id
  Reply (writeDiagnostics values) = Text ⊎ ⊤

  open Effects.Protocol Operation Reply public

  data Result : Set where started : Id → Result; failed : Text → Result

  interrupt : ∀ {A : Set} before → (∀ after → Interrupted before after → Script A) → Script A
  interrupt [] next = next [] empty
  interrupt (before ∷ rest) next with R.Trace.status before ≟Text toList "running"
  ... | no skipped = interrupt rest (λ after proof → next (before ∷ after) (unchanged before rest after skipped proof))
  ... | yes running = ask clock λ observed → interrupt rest
    (λ after proof → next (interruptTrace observed before ∷ after) (marked observed before rest after running proof))

  newTrace : Id → Maybe ℕ → R.Report → ℕ → R.Trace
  newTrace identity observed report budget = R.traceValue identity (Records.clock observed) nothing
    (toList "running") nothing (R.Report.selectedIds report) (just budget) (just budget) [] 0

  traceIdsAreComplete : ∀ identity observed report initial →
    R.Trace.selectedIds (newTrace identity observed report initial) ≡ R.Report.selectedIds report
  traceIdsAreComplete identity observed report initial = refl

  commit : Id → List R.Trace → Script Result
  commit identity values = ask (writeDiagnostics values) λ where
    (inj₁ problem) → done (failed problem)
    (inj₂ tt) → done (started identity)

  create : R.Report → ℕ → List R.Trace → Script Result
  create report budget previous = ask newId λ identity → ask clock λ observed →
    commit identity (previous ++ (newTrace identity observed report budget ∷ []))

  begin : R.Report → ℕ → Script Result
  begin report budget = ask readDiagnostics λ where
    (inj₁ problem) → done (failed problem)
    (inj₂ previous) → interrupt previous (λ after proof → create report budget after)

  -- This is a receipt for the named write operation, not a filesystem proof.
  -- The storage interpreter must still establish its durability semantics.
  data Acknowledged : List Event → Set where
    last : ∀ values → Acknowledged ((writeDiagnostics values , inj₂ tt) ∷ [])
    earlier : ∀ event {events} → Acknowledged events → Acknowledged (event ∷ events)

  Safe : Script Result → Set
  Safe program = ∀ events identity → Runs program events (started identity) → Acknowledged events

  commitSafe : ∀ identity values → Safe (commit identity values)
  commitSafe identity values events result (replied _ _ (inj₁ problem) ())
  commitSafe identity values events .identity (replied _ _ (inj₂ tt) (returned .(started identity))) = last values

  createSafe : ∀ report budget previous → Safe (create report budget previous)
  createSafe report budget previous events result (replied _ _ identity (replied _ _ observed later)) =
    earlier (newId , identity) (earlier (clock , observed) (commitSafe identity _ _ result later))

  interruptSafe : ∀ before next → (∀ after proof → Safe (next after proof)) → Safe (interrupt before next)
  interruptSafe [] next safe = safe [] empty
  interruptSafe (before ∷ rest) next safe events result run with R.Trace.status before ≟Text toList "running"
  ... | no skipped = interruptSafe rest _ (λ after proof → safe (before ∷ after) (unchanged before rest after skipped proof)) events result run
  ... | yes running with run
  ...   | replied _ _ observed later = earlier (clock , observed)
    (interruptSafe rest _ (λ after proof → safe (interruptTrace observed before ∷ after)
      (marked observed before rest after running proof)) _ result later)

  successRequiresWriteReceipt : ∀ report budget → Safe (begin report budget)
  successRequiresWriteReceipt report budget events result (replied _ _ (inj₁ problem) ())
  successRequiresWriteReceipt report budget events result (replied _ _ (inj₂ previous) later) = earlier (readDiagnostics , inj₂ previous)
    (interruptSafe previous _ (λ after proof → createSafe report budget after) _ result later)

{-# OPTIONS --safe #-}
-- Event and finish operations compose ordered selection with the verified
-- append/trim protocols. Success requires the final diagnostics write receipt.
module Mimir.JudgeTraceMutation where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.Effects as Effects
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeTraceSelection as Selection
import Mimir.JudgeTraceEvent as Append
import Mimir.JudgeTraceTrim as Trim
import Mimir.SignedMachine as Machine

module Over (Id : Set) (equal : (x y : Id) → Dec (x ≡ y))
  (maximum eventLimit byteLimit : ℕ) (checks : Machine.OverflowChecks) where
  module R = Records.Over Id
  module S = Selection.Over Id equal
  module A = Append.Over Id maximum eventLimit byteLimit checks
  module T = Trim.Over Id maximum eventLimit byteLimit checks

  data Operation : Set where
    readDiagnostics clock : Operation
    serialize : R.Trace → Operation
    writeDiagnostics : List R.Trace → Operation

  Reply : Operation → Set
  Reply readDiagnostics = Text ⊎ List R.Trace
  Reply clock = Maybe ℕ
  Reply (serialize value) = Text ⊎ List Byte
  Reply (writeDiagnostics values) = Text ⊎ ⊤

  open Effects.Protocol Operation Reply public
  data Result : Set where completed arithmeticPanic : Result; failed : Text → Result

  commit : List R.Trace → Script Result
  commit values = ask (writeDiagnostics values) λ where
    (inj₁ problem) → done (failed problem)
    (inj₂ tt) → done completed

  -- Both component protocols use this exact serializer operation/reply type.
  drive : ∀ {Value : Set} → A.Script Value → (Value → Script Result) → Script Result
  drive (A.done value) next = next value
  drive (A.ask (A.serialize value) receive) next = ask (serialize value) (λ reply → drive (receive reply) next)

  finishEvent : ∀ identity event {before} → (selected : S.Recording.Focus identity before) →
    A.Result event (S.Recording.Focus.value selected) → Script Result
  finishEvent identity event selected (A.ready after change) = commit (S.Recording.replace identity selected after)
  finishEvent identity event selected (A.serializationFailed problem) = done (failed problem)
  finishEvent identity event selected A.arithmeticPanic = done arithmeticPanic

  foundEvent : Id → R.Event → List R.Trace → Script Result
  foundEvent identity event before with S.Recording.find identity before
  ... | S.Recording.missing absent = done (failed (toList "active diagnostic trace is missing"))
  ... | S.Recording.found selected = drive (A.append event (S.Recording.Focus.value selected)) (finishEvent identity event selected)

  recordEvent : Id → R.Event → Script Result
  recordEvent identity event = ask readDiagnostics λ where
    (inj₁ problem) → done (failed problem)
    (inj₂ before) → foundEvent identity event before

  finishMetadata : Maybe ℕ → R.Report → R.Trace → R.Trace
  finishMetadata observed report before = record before
    { status = R.Report.status report ; blockReason = R.Report.blockReason report ; finishedAt = just (Records.clock observed) }

  finishTrim : ∀ identity {before} (selected : S.Finishing.Focus identity before) trace → T.Result trace → Script Result
  finishTrim identity selected trace (T.ready after trimmed bytes fits) = commit (S.Finishing.replace identity selected after)
  finishTrim identity selected trace (T.serializationFailed problem) = done (failed problem)
  finishTrim identity selected trace T.metadataTooLarge = done (failed (toList "diagnostic trace metadata is too large"))
  finishTrim identity selected trace T.arithmeticPanic = done arithmeticPanic

  trimSelected : ∀ identity {before} → S.Finishing.Focus identity before → Maybe ℕ → R.Report → Script Result
  trimSelected identity selected observed report = drive (T.trim (length (R.Trace.events updated)) updated ≤-refl)
    (finishTrim identity selected updated)
    where updated = finishMetadata observed report (S.Finishing.Focus.value selected)

  finishSelected : ∀ identity {before} → S.Finishing.Focus identity before → R.Report → Script Result
  finishSelected identity selected report with R.Report.status report ≟Text toList "complete"
  ... | yes complete = commit (S.Finishing.remove identity selected)
  ... | no other = ask clock (λ observed → trimSelected identity selected observed report)

  foundFinish : Id → R.Report → List R.Trace → Script Result
  foundFinish identity report before with S.Finishing.find identity before
  ... | S.Finishing.missing absent = done (failed (toList "diagnostic trace is missing"))
  ... | S.Finishing.found selected = finishSelected identity selected report

  finish : Id → R.Report → Script Result
  finish identity report = ask readDiagnostics λ where
    (inj₁ problem) → done (failed problem)
    (inj₂ before) → foundFinish identity report before

  data Acknowledged : List Event → Set where
    last : ∀ values → Acknowledged ((writeDiagnostics values , inj₂ tt) ∷ [])
    earlier : ∀ event {events} → Acknowledged events → Acknowledged (event ∷ events)

  Safe : Script Result → Set
  Safe program = ∀ events → Runs program events completed → Acknowledged events

  commitSafe : ∀ values → Safe (commit values)
  commitSafe values events (replied _ _ (inj₁ problem) ())
  commitSafe values events (replied _ _ (inj₂ tt) (returned .completed)) = last values

  driveSafe : ∀ {Value : Set} (program : A.Script Value) next → (∀ value → Safe (next value)) → Safe (drive program next)
  driveSafe (A.done value) next safe = safe value
  driveSafe (A.ask (A.serialize value) receive) next safe events (replied _ _ reply later) =
    earlier (serialize value , reply) (driveSafe (receive reply) next safe _ later)

  eventResultSafe : ∀ identity event {before} (selected : S.Recording.Focus identity before) result → Safe (finishEvent identity event selected result)
  eventResultSafe identity event selected (A.ready after change) = commitSafe (S.Recording.replace identity selected after)
  eventResultSafe identity event selected (A.serializationFailed problem) events ()
  eventResultSafe identity event selected A.arithmeticPanic events ()

  foundEventSafe : ∀ identity event before → Safe (foundEvent identity event before)
  foundEventSafe identity event before events run with S.Recording.find identity before
  ... | S.Recording.missing absent with run
  ...   | ()
  foundEventSafe identity event before events run | S.Recording.found selected =
    driveSafe (A.append event (S.Recording.Focus.value selected)) _ (eventResultSafe identity event selected) events run

  eventRequiresWriteReceipt : ∀ identity event → Safe (recordEvent identity event)
  eventRequiresWriteReceipt identity event events (replied _ _ (inj₁ problem) ())
  eventRequiresWriteReceipt identity event events (replied _ _ (inj₂ before) later) =
    earlier (readDiagnostics , inj₂ before) (foundEventSafe identity event before _ later)

  trimResultSafe : ∀ identity {before} (selected : S.Finishing.Focus identity before) trace result → Safe (finishTrim identity selected trace result)
  trimResultSafe identity selected trace (T.ready after trimmed bytes fits) = commitSafe (S.Finishing.replace identity selected after)
  trimResultSafe identity selected trace (T.serializationFailed problem) events ()
  trimResultSafe identity selected trace T.metadataTooLarge events ()
  trimResultSafe identity selected trace T.arithmeticPanic events ()

  trimSelectedSafe : ∀ identity {before} (selected : S.Finishing.Focus identity before) observed report → Safe (trimSelected identity selected observed report)
  trimSelectedSafe identity selected observed report = driveSafe
    (T.trim (length (R.Trace.events updated)) updated ≤-refl)
    (finishTrim identity selected updated) (trimResultSafe identity selected updated)
    where updated = finishMetadata observed report (S.Finishing.Focus.value selected)

  finishSelectedSafe : ∀ identity {before} (selected : S.Finishing.Focus identity before) report → Safe (finishSelected identity selected report)
  finishSelectedSafe identity selected report events run with R.Report.status report ≟Text toList "complete"
  ... | yes complete = commitSafe (S.Finishing.remove identity selected) events run
  ... | no other with run
  ...   | replied _ _ observed later = earlier (clock , observed) (trimSelectedSafe identity selected observed report _ later)

  foundFinishSafe : ∀ identity report before → Safe (foundFinish identity report before)
  foundFinishSafe identity report before events run with S.Finishing.find identity before
  ... | S.Finishing.missing absent with run
  ...   | ()
  foundFinishSafe identity report before events run | S.Finishing.found selected = finishSelectedSafe identity selected report events run

  finishRequiresWriteReceipt : ∀ identity report → Safe (finish identity report)
  finishRequiresWriteReceipt identity report events (replied _ _ (inj₁ problem) ())
  finishRequiresWriteReceipt identity report events (replied _ _ (inj₂ before) later) =
    earlier (readDiagnostics , inj₂ before) (foundFinishSafe identity report before _ later)

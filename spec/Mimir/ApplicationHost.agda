{-# OPTIONS --safe #-}
-- The public request host encloses the database protocol. Registration occurs
-- before the first application effect; an owned request cannot return a
-- successful payload until its body and provider children have been joined
-- and its exact durable execution has been acknowledged. Cancellation adds
-- the separate all-copy barrier, with no total progress claim for that wait.
module Mimir.ApplicationHost where

open import Data.Integer using (ℤ)
open import Data.Bool using (false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationStore as Store
import Mimir.OperationControls as Controls
import Mimir.PublicRequest as Public
import Mimir.RecoverableStoreStep as StoreStep
import Mimir.Recovery as Recovery
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
open import Mimir.Text using (Text)

module Run (environment : Application.Environment) where
  module A = Application.Run environment using
    (Result; State; running; Event; event; Step; Runs; returned; advanced; start; reached; resultState; module Checked)
  module D = Public.Decode (Application.Environment.library environment) using (readInvocation; module Invocation)
  module Ownership = Controls.ExecutionOwnership

  data Mode : Set where
    ordinary : Mode
    writer cancelling : ℕ → Mode

  controlMode : Public.Request → Mode
  controlMode (Public.cancelOperation token) = cancelling token
  controlMode _ = ordinary

  decodedMode : (kind : Tools.Kind) → Public.TokenForKind kind → Public.Request → Mode
  decodedMode Tools.businessWrite token requested = writer token
  decodedMode Tools.readOnly token requested = ordinary
  decodedMode Tools.operationControl token requested = controlMode requested

  mode : Tools.Tool → Wire.Value → Mode
  mode tool submitted with D.readInvocation tool submitted
  ... | inj₁ _ = ordinary
  ... | inj₂ admitted = decodedMode (Tools.kind tool)
    (D.Invocation.operationToken admitted) (D.Invocation.request admitted)

  -- Keeping the actual registration constructor also fixes which execution
  -- owns the children. Neither a token alone nor another copy's ACK suffices.
  data Entry : Mode → Store.World → Store.World → Set where
    ordinaryEntry : ∀ before → Entry ordinary before before
    cancelEntry : ∀ token before → Entry (cancelling token) before before
    started : ∀ token row before after →
      Store.ExecutionRow.token row ≡ token →
      Store.ExecutionRow.stoppedAt row ≡ nothing →
      Ownership.register row before ≡ (after , Ownership.registered row) →
      Entry (writer token) before after
    fenced : ∀ token before → Ownership.Fence token before →
      Entry (writer token) before before
    unknown : ∀ token before →
      Recovery.Cancellation.reserved token
        (Store.OperationTables.reservations (Store.World.operations before)) ≡ false →
      Entry (writer token) before before

  ownedRows : ∀ {selected before entered} → Entry selected before entered → List Store.ExecutionRow
  ownedRows (ordinaryEntry _) = []
  ownedRows (cancelEntry _ _) = []
  ownedRows (started _ row _ _ _ _ _) = row ∷ []
  ownedRows (fenced _ _ _) = []
  ownedRows (unknown _ _ _) = []

  -- A handler can be cancelled while it is still awaiting a database/provider
  -- reply. Its active ownership is therefore recorded before Handled returns.
  -- Each prefix transition is an actual application receipt, not a script
  -- supplied independently of the fixed dispatcher.
  data DatabasePrefix : A.State → List A.Event → A.State → Set where
    here : ∀ state → DatabasePrefix state [] state
    next : ∀ before middle after physical events → DatabasePrefix middle events after →
      DatabasePrefix before (A.event before middle physical ∷ events) after

  prefixFromRun : ∀ before events result → A.Runs before events result →
    DatabasePrefix before events (A.resultState result)
  prefixFromRun before events result (A.returned .result) = here (A.resultState result)
  prefixFromRun before events result (A.advanced .before middle physical rest .result later) =
    next before middle (A.resultState result) physical rest (prefixFromRun middle rest result later)

  appendRun : ∀ before prefix middle remaining result → DatabasePrefix before prefix middle →
    A.Runs middle remaining result → A.Runs before (prefix ++ remaining) result
  appendRun before .[] .before remaining result (here .before) tail = tail
  appendRun before .(A.event before middle physical ∷ events) after remaining result
    (next .before middle .after physical events prefix) tail =
      A.advanced before middle physical (events ++ remaining) result
        (appendRun middle events after remaining result prefix tail)

  stateWorld : A.State → Store.World
  stateWorld (A.running call initial (A.Checked.running active)) =
    A.Checked.History.current {call = call} (A.Checked.Active.evidence {call = call} active)
  stateWorld (A.running call initial (A.Checked.stopped finishedState)) =
    A.Checked.History.current {call = call} (A.Checked.Active.evidence {call = call}
      (A.Checked.Terminal.active {call = call} finishedState))

  record Active (tool : Tools.Tool) (submitted : Wire.Value) : Set where
    field
      initial entered : Store.World
      entry : Entry (mode tool submitted) initial entered
      events : List A.Event
      current : A.State
      observed : DatabasePrefix (A.start tool submitted entered) events current
    owned : List Store.ExecutionRow
    owned = ownedRows entry

  -- An unsuccessful cleanup is retained as a host diagnostic, never passed
  -- through the database success projector. The trace records whatever was
  -- actually observed, including disconnection without acknowledgement.
  data Pending (databaseTerminal : Store.World) : Mode → Store.World → Set where
    untrackedFailure : Text → Pending databaseTerminal ordinary databaseTerminal
    writerFailure : ∀ token final → Text →
      Ownership.HostRuns token (Ownership.waiting databaseTerminal) (Ownership.waiting final) →
      Pending databaseTerminal (writer token) final
    cancellationFailure : ∀ token final → Text →
      Ownership.HostRuns token (Ownership.waiting databaseTerminal) (Ownership.waiting final) →
      Pending databaseTerminal (cancelling token) final

  pendingReason : ∀ {databaseTerminal selected final} → Pending databaseTerminal selected final → Text
  pendingReason (untrackedFailure reason) = reason
  pendingReason (writerFailure token final reason observed) = reason
  pendingReason (cancellationFailure token final reason observed) = reason

  data CancelExit (token : ℕ) (databaseTerminal : Store.World) : Store.World → Set where
    unfenced : Store.lookupSaved databaseTerminal token StoreStep.resultKey ≡ nothing →
      Store.lookupCancellation databaseTerminal token ≡ nothing →
      CancelExit token databaseTerminal databaseTerminal
    allCopiesStopped : (receipt : Ownership.StoppedAfter token databaseTerminal) →
      CancelExit token databaseTerminal (Ownership.StoppedAfter.final receipt)

  data Exit : ∀ {selected before entered} → Entry selected before entered →
    Store.World → Store.World → Set where
    ordinaryExit : ∀ before databaseTerminal →
      Exit (ordinaryEntry before) databaseTerminal databaseTerminal
    cancelExit : ∀ token before databaseTerminal final → CancelExit token databaseTerminal final →
      Exit (cancelEntry token before) databaseTerminal final
    fencedExit : ∀ token before fence databaseTerminal →
      Exit (fenced token before fence) databaseTerminal databaseTerminal
    unknownExit : ∀ token before absent databaseTerminal →
      Exit (unknown token before absent) databaseTerminal databaseTerminal
    acknowledged : ∀ token row before entered same notStopped registered databaseTerminal
      ownedWorkers (receipt : Ownership.StopReceipt (Store.ExecutionRow.identity row) ownedWorkers)
      (timestamp : ℤ) →
      Exit (started token row before entered same notStopped registered) databaseTerminal
        (Ownership.acknowledge (Store.ExecutionRow.identity row) ownedWorkers
          (Ownership.stopped receipt) timestamp databaseTerminal)

  record Execution (tool : Tools.Tool) (submitted : Wire.Value) (events : List A.Event) : Set where
    field
      initial entered : Store.World
      entry : Entry (mode tool submitted) initial entered
      databaseResult : A.Result
      databaseRun : A.Runs (A.start tool submitted entered) events databaseResult
      final : Store.World
      exited : Exit entry (A.reached databaseResult) final

  data Result (tool : Tools.Tool) (submitted : Wire.Value) (events : List A.Event) : Set where
    returned : Execution tool submitted events → Result tool submitted events
    cleanupPending : ∀ initial entered (entry : Entry (mode tool submitted) initial entered)
      databaseResult → A.Runs (A.start tool submitted entered) events databaseResult →
      ∀ final → Pending (A.reached databaseResult) (mode tool submitted) final → Result tool submitted events

  -- A returning task continues its actual tracked prefix. It cannot exchange
  -- the registered owner for a new independent Execution at response time.
  finishActive : ∀ {tool submitted} (active : Active tool submitted) remaining result →
    A.Runs (Active.current active) remaining result → ∀ final →
    Exit (Active.entry active) (A.reached result) final →
    Execution tool submitted (Active.events active ++ remaining)
  finishActive active remaining result ran final exited = record
    { initial = Active.initial active; entered = Active.entered active
    ; entry = Active.entry active; databaseResult = result
    ; databaseRun = appendRun _ (Active.events active) (Active.current active) remaining result
        (Active.observed active) ran
    ; final = final; exited = exited }

  pendingActive : ∀ {tool submitted} (active : Active tool submitted) remaining result →
    A.Runs (Active.current active) remaining result → ∀ final →
    Pending (A.reached result) (mode tool submitted) final →
    Result tool submitted (Active.events active ++ remaining)
  pendingActive active remaining result ran final pending = cleanupPending
    (Active.initial active) (Active.entered active) (Active.entry active) result
    (appendRun _ (Active.events active) (Active.current active) remaining result
      (Active.observed active) ran) final pending

  -- This is an explicit execution witness, not an unused output projector.
  -- Every successful host result contains the actual entered application run.
  databaseExecution : ∀ tool submitted events (execution : Execution tool submitted events) →
    A.Runs (A.start tool submitted
      (Execution.entered execution)) events (Execution.databaseResult execution)
  databaseExecution tool submitted events execution = Execution.databaseRun execution

  entryPreservesBusiness : ∀ selected before entered → Entry selected before entered →
    Store.businessSnapshot entered ≡ Store.businessSnapshot before
  entryPreservesBusiness .ordinary before .before (ordinaryEntry .before) = refl
  entryPreservesBusiness .(cancelling token) before .before (cancelEntry token .before) = refl
  entryPreservesBusiness .(writer token) before entered
    (started token row .before .entered same pending registered) =
      Ownership.entryPreservesBusiness token before entered
        (Ownership.startedCopy row before entered same pending registered)
  entryPreservesBusiness .(writer token) before .before (fenced token .before fence) = refl
  entryPreservesBusiness .(writer token) before .before (unknown token .before missing) = refl

  -- If cancellation observed a durable fence, an unfenced return cannot
  -- discharge the barrier. Every successful such return has every real ACK.
  cancellationRequiresEveryCopy : ∀ token databaseTerminal final →
    Ownership.Fence token databaseTerminal → CancelExit token databaseTerminal final →
    Ownership.FullConfirmation token final
  cancellationRequiresEveryCopy token databaseTerminal .databaseTerminal
    (Ownership.cancelledFence row known) (unfenced noFinal noCancellation)
    with trans (sym noCancellation) known
  ... | ()
  cancellationRequiresEveryCopy token databaseTerminal .databaseTerminal
    (Ownership.finalAnswerFence value known) (unfenced noFinal noCancellation)
    with trans (sym noFinal) known
  ... | ()
  cancellationRequiresEveryCopy token databaseTerminal final fence (allCopiesStopped receipt) =
    Ownership.StoppedAfter.certifiedStop receipt

  -- EOF drops all of this host's request bodies. It does not cancel their
  -- tokens or wait for other hosts. The caller must supply exactly the owned
  -- rows obtained from its actual started entries, not a guessed empty list.
  data StoppedRequests : List Store.ExecutionRow → Store.World → Store.World → Set where
    noOwnedRequests : ∀ before → StoppedRequests Data.List.[] before before
    stoppedRequest : ∀ row rest before after ownedWorkers
      (receipt : Ownership.StopReceipt (Store.ExecutionRow.identity row) ownedWorkers)
      timestamp →
      StoppedRequests rest (Ownership.acknowledge (Store.ExecutionRow.identity row)
        ownedWorkers (Ownership.stopped receipt) timestamp before) after →
      StoppedRequests (row Data.List.∷ rest) before after

  localShutdownPreservesBusiness : ∀ owned before after → StoppedRequests owned before after →
    Store.businessSnapshot after ≡ Store.businessSnapshot before
  localShutdownPreservesBusiness .Data.List.[] before .before (noOwnedRequests .before) = refl
  localShutdownPreservesBusiness .(row Data.List.∷ rest) before after
    (stoppedRequest row rest .before .after ownedWorkers receipt timestamp remaining) =
      trans (localShutdownPreservesBusiness rest _ after remaining)
        (Ownership.acknowledgementPreservesBusiness (Store.ExecutionRow.identity row)
          ownedWorkers (Ownership.stopped receipt) timestamp before)

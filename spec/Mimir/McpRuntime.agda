{-# OPTIONS --safe #-}
-- Server control-state composition. Malformed UTF-8 and JSON receive a
-- correction and continue after its flush. Transport failures terminate.
-- Input is watched during execution; queued requests start in arrival order
-- only after the active exchange finishes. Disconnect drops the owned future
-- before exit. Drop includes the local worker's existing kill-and-wait cleanup;
-- it makes no claim that earlier business commits were rolled back.
import Mimir.StandardLibrary
module Mimir.McpRuntime (library : Mimir.StandardLibrary.Contract) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.McpInput as InputDependency
private
  module Input = InputDependency library
import Mimir.McpExchange as Exchange
import Mimir.StandardLibrary as Library
import Mimir.ReadLine as Lines
import Mimir.Effects as Effects

module Cleanup where
  -- This dependency action returns after the request future has been dropped,
  -- including synchronous termination and reaping of any owned local worker.
  data Effect : Set where dropOwnedRequest : Effect
  Reply : Effect → Set
  Reply dropOwnedRequest = ⊤
  module P = Effects.Protocol Effect Reply
  stop : P.Script ⊤
  stop = P.ask dropOwnedRequest (λ _ → P.done tt)

Frames = List (List Byte)

data Exit : Set where
  eof : Exit
  readFailure : Text → Exit
  arithmeticPanic : Exit
  exchangeFailure : Exchange.Failure → Exit

data State : Set where
  reading : Frames → State
  executing : Exchange.Script Exchange.Outcome → Frames → State
  stopping : Exit → Cleanup.P.Script ⊤ → State
  exited : Exit → State

bodyOutcome : ∀ {input} → Frames → Input.BodyOutcome input → State
bodyOutcome queued (Input.blank proof) = reading queued
bodyOutcome queued (Input.accepted value) = executing (Exchange.exchange (Input.request value)) queued
bodyOutcome queued (Input.rejected failure) = executing (Exchange.parseError (Library.JSONError.message failure)) queued
bodyOutcome queued (Input.panicked message) = exited arithmeticPanic

readOutcome : ∀ {input} → Frames → Input.Outcome input → State
readOutcome queued (Input.eof proof) = exited eof
readOutcome queued (Input.invalidUTF8 framed failure) = executing (Exchange.parseError failure) queued
readOutcome queued (Input.line framed textValue parsedBody) = bodyOutcome queued parsedBody

finish : Exchange.Outcome → Frames → State
finish Exchange.nextLine queued = reading queued
finish (Exchange.stopped failure) queued = exited (exchangeFailure failure)

queuedState : List Byte → Frames → State
queuedState input remaining = readOutcome remaining (Input.Parser.read input)

whileRunning : Exchange.Script Exchange.Outcome → Frames → List Byte → State
whileRunning script queued [] = stopping eof Cleanup.stop
whileRunning script queued frame@(_ ∷ _) = executing script (queued ++ (frame ∷ []))

data Event : Set where
  read : ∀ input → Lines.Scanned.remainder (Lines.scan input) ≡ [] → Event
  readError : Text → Event
  effect : Exchange.Event → Event
  cleanup : Cleanup.P.Event → Event
  queued returned cleaned : Event

data Step : State → Event → State → Set where
  received : ∀ input wholeLine → Step (reading []) (read input wholeLine)
    (readOutcome [] (Input.Parser.read input))
  nextQueued : ∀ input remaining → Step (reading (input ∷ remaining)) queued
    (queuedState input remaining)
  failedRead : ∀ message → Step (reading []) (readError message) (exited (readFailure message))
  buffered : ∀ script pending input wholeLine →
    Step (executing script pending) (read input wholeLine) (whileRunning script pending input)
  disconnectedRead : ∀ script pending message → Step (executing script pending) (readError message)
    (stopping (readFailure message) Cleanup.stop)
  replied : ∀ operation continuation reply pending →
    Step (executing (Exchange.ask operation continuation) pending) (effect (operation , reply))
      (executing (continuation reply) pending)
  returned : ∀ outcome pending → Step (executing (Exchange.done outcome) pending) returned (finish outcome pending)
  cleanupReply : ∀ reason operation continuation reply →
    Step (stopping reason (Cleanup.P.ask operation continuation)) (cleanup (operation , reply))
      (stopping reason (continuation reply))
  stopped : ∀ reason → Step (stopping reason (Cleanup.P.done tt)) cleaned (exited reason)

data Trace : State → List Event → State → Set where
  empty : ∀ state → Trace state [] state
  more : ∀ {before event middle events after} → Step before event middle →
    Trace middle events after → Trace before (event ∷ events) after

exitHasNoStep : ∀ reason event after → Step (exited reason) event after → ⊥
exitHasNoStep reason event after ()

exitHasNoLaterEffect : ∀ reason events after → Trace (exited reason) events after → events ≡ []
exitHasNoLaterEffect reason .[] .(exited reason) (empty _) = refl
exitHasNoLaterEffect reason .(_ ∷ _) after (more () tail)

-- EOF needs no reply from the currently blocked application or model.
disconnectStartsOwnedCleanup : ∀ script pending →
  Step (executing script pending) (read [] refl) (stopping eof Cleanup.stop)
disconnectStartsOwnedCleanup script pending = buffered script pending [] refl

bufferedReadKeepsCurrentExchange : ∀ script pending byte bytes wholeLine after →
  Step (executing script pending) (read (byte ∷ bytes) wholeLine) after →
  after ≡ executing script (pending ++ ((byte ∷ bytes) ∷ []))
bufferedReadKeepsCurrentExchange script pending byte bytes wholeLine after (buffered _ _ _ _) = refl

stoppingCannotExecuteApplication : ∀ reason cleanupScript event after →
  Step (stopping reason cleanupScript) (effect event) after → ⊥
stoppingCannotExecuteApplication reason cleanupScript event after ()

exitKeepsReason : ∀ reason events actual → Trace (exited reason) events (exited actual) →
  events ≡ [] × actual ≡ reason
exitKeepsReason reason .[] .reason (empty _) = refl , refl
exitKeepsReason reason .(_ ∷ _) actual (more () tail)

-- A closed session cannot report completion of shutdown without its actual
-- owned-future drop receipt. No application step or queued request can occur
-- between disconnect and that receipt, or after exit.
stopRequiresOwnedDrop : ∀ reason events actual →
  Trace (stopping reason Cleanup.stop) events (exited actual) →
  events ≡ (cleanup (Cleanup.dropOwnedRequest , tt) ∷ cleaned ∷ []) × actual ≡ reason
stopRequiresOwnedDrop reason events actual
  (more (cleanupReply .reason .Cleanup.dropOwnedRequest _ .tt) (more (stopped .reason) remaining))
  with exitKeepsReason reason _ actual remaining
... | refl , refl = refl , refl


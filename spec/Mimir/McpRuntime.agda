{-# OPTIONS --safe #-}
-- Concurrent request futures write private buffers. Completed responses enter
-- a FIFO; one frame retains stdout ownership through partial writes and flush.
-- Future destruction and physical host cleanup are separate observations.
import Mimir.StandardLibrary
module Mimir.McpRuntime (library : Mimir.StandardLibrary.Contract) where

open import Data.List using (List; []; _∷_; _++_)
import Data.List.Properties as List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.McpInput as InputDependency
private
  module Input = InputDependency library
import Mimir.McpExchange as Exchange
import Mimir.ReadLine as Lines
import Mimir.Effects as Effects

record Task : Set where
  constructor task
  field
    program : Exchange.Script Exchange.Outcome
    response : List Byte

module Cleanup where
  data Result : Set where joined : Result; failed : Text → Result
  data Effect : Set where
    dropOwnedRequests : List Task → Effect
    finishOperationHost : Effect
  Reply : Effect → Set
  Reply (dropOwnedRequests active) = ⊤
  Reply finishOperationHost = Result
  module P = Effects.Protocol Effect Reply
  stop : List Task → P.Script Result
  stop active = P.ask (dropOwnedRequests active) (λ _ →
    P.ask finishOperationHost (λ receipt → P.done receipt))

Frames = List (List Byte)

record Outgoing : Set where
  constructor outgoing
  field sent remaining : List Byte

record Live : Set where
  constructor live
  field
    active : List Task
    replies : Frames
    output : Maybe Outgoing

-- Native pop_front before select; an existing frame cannot be displaced.
normalize : Live → Live
normalize (live active replies (just output)) = live active replies (just output)
normalize (live active [] nothing) = live active [] nothing
normalize (live active (bytes ∷ rest) nothing) = live active rest (just (outgoing [] bytes))

data Exit : Set where
  eof : Exit
  readFailure arithmeticPanic writeFailure flushFailure : Text → Exit
  exchangeFailure : Exchange.Failure → Exit
  cleanupFailure : Exit → Text → Exit

data State : Set where
  serving : Live → State
  stopping : Exit → Cleanup.P.Script Cleanup.Result → State
  exited : Exit → State

serve : List Task → Frames → Maybe Outgoing → State
serve active replies output = serving (normalize (live active replies output))

reading : Frames → State
reading replies = serve [] replies nothing

spawn : Live → Exchange.Script Exchange.Outcome → State
spawn current program = serve
  (Live.active current ++ (task program [] ∷ []))
  (Live.replies current) (Live.output current)

bodyOutcome : ∀ {input} → Live → Input.BodyOutcome input → State
bodyOutcome current (Input.blank proof) = spawn current (Exchange.done Exchange.nextLine)
bodyOutcome current (Input.accepted value) = spawn current (Exchange.exchange (Input.request value))
bodyOutcome current (Input.rejected failure) = spawn current
  (Exchange.parseError (Mimir.StandardLibrary.JSONError.message failure))
bodyOutcome current (Input.panicked message) =
  stopping (arithmeticPanic message) (Cleanup.stop (Live.active current))

readOutcome : ∀ {input} → Live → Input.Outcome input → State
readOutcome current (Input.eof proof) = stopping eof (Cleanup.stop (Live.active current))
readOutcome current (Input.invalidUTF8 framed failure) = spawn current (Exchange.parseError failure)
readOutcome current (Input.line framed textValue parsedBody) = bodyOutcome current parsedBody

queueResponse : Frames → List Byte → Frames
queueResponse replies [] = replies
queueResponse replies bytes@(_ ∷ _) = replies ++ (bytes ∷ [])

finish : List Task → Frames → Maybe Outgoing → List Byte → Exchange.Outcome → State
finish active replies output bytes Exchange.nextLine = serve active (queueResponse replies bytes) output
finish active replies output bytes (Exchange.stopped failure) =
  stopping (exchangeFailure failure) (Cleanup.stop active)

cleanupExit : Exit → Cleanup.Result → Exit
cleanupExit original Cleanup.joined = original
cleanupExit original (Cleanup.failed message) = cleanupFailure original message

-- Vec writes/flushes are fixed local transitions. Only these three effects
-- consult the application's handler/formatter/serializer dependencies.
data Dependency : Exchange.Effect → Set where
  handle : ∀ name arguments → Dependency (Exchange.handleTool name arguments)
  format : ∀ value → Dependency (Exchange.formatTool value)
  serialize : ∀ response → Dependency (Exchange.serialize response)

data Event : Set where
  read : ∀ input → Lines.Scanned.remainder (Lines.scan input) ≡ [] → Event
  readError : Text → Event
  effect : (operation : Exchange.Effect) → Exchange.Reply operation → Event
  bufferWrite : List Byte → Event
  bufferFlush completedTask : Event
  wrote : List Byte → Event
  writeError flushError : Text → Event
  flushed : Event
  cleanup : Cleanup.P.Event → Event
  cleaned : Event

data Step : State → Event → State → Set where
  received : ∀ current input wholeLine →
    Step (serving (normalize current)) (read input wholeLine)
      (readOutcome (normalize current) (Input.Parser.read input))
  failedRead : ∀ current message →
    Step (serving (normalize current)) (readError message)
      (stopping (readFailure message) (Cleanup.stop (Live.active current)))
  replied : ∀ prefix suffix replies output buffer operation continuation reply →
    Dependency operation →
    Step (serve (prefix ++ (task (Exchange.ask operation continuation) buffer ∷ suffix)) replies output)
      (effect operation reply)
      (serve (prefix ++ (task (continuation reply) buffer ∷ suffix)) replies output)
  bufferedWrite : ∀ prefix suffix replies output buffer bytes continuation →
    Step (serve (prefix ++ (task (Exchange.ask (Exchange.write bytes) continuation) buffer ∷ suffix)) replies output)
      (bufferWrite bytes)
      (serve (prefix ++ (task (continuation Exchange.written) (buffer ++ bytes) ∷ suffix)) replies output)
  bufferedFlush : ∀ prefix suffix replies output buffer continuation →
    Step (serve (prefix ++ (task (Exchange.ask Exchange.flush continuation) buffer ∷ suffix)) replies output)
      bufferFlush
      (serve (prefix ++ (task (continuation Exchange.completed) buffer ∷ suffix)) replies output)
  returned : ∀ prefix suffix replies output buffer outcome →
    Step (serve (prefix ++ (task (Exchange.done outcome) buffer ∷ suffix)) replies output)
      completedTask (finish (prefix ++ suffix) replies output buffer outcome)
  written : ∀ active replies sent byte bytes remaining →
    Step (serve active replies (just (outgoing sent ((byte ∷ bytes) ++ remaining))))
      (wrote (byte ∷ bytes))
      (serve active replies (just (outgoing (sent ++ (byte ∷ bytes)) remaining)))
  failedWrite : ∀ active replies sent remaining message →
    Step (serve active replies (just (outgoing sent remaining))) (writeError message)
      (stopping (writeFailure message) (Cleanup.stop active))
  flushed : ∀ active replies sent →
    Step (serve active replies (just (outgoing sent []))) flushed
      (serve active replies nothing)
  failedFlush : ∀ active replies sent message →
    Step (serve active replies (just (outgoing sent []))) (flushError message)
      (stopping (flushFailure message) (Cleanup.stop active))
  cleanupReply : ∀ reason operation continuation reply →
    Step (stopping reason (Cleanup.P.ask operation continuation)) (cleanup (operation , reply))
      (stopping reason (continuation reply))
  stopped : ∀ reason receipt →
    Step (stopping reason (Cleanup.P.done receipt)) cleaned (exited (cleanupExit reason receipt))

data Trace : State → List Event → State → Set where
  empty : ∀ state → Trace state [] state
  more : ∀ {before event middle events after} → Step before event middle →
    Trace middle events after → Trace before (event ∷ events) after

exitHasNoStep : ∀ reason event after → Step (exited reason) event after → ⊥
exitHasNoStep reason event after ()

exitKeepsReason : ∀ reason events actual → Trace (exited reason) events (exited actual) →
  events ≡ [] × actual ≡ reason
exitKeepsReason reason .[] .reason (empty _) = refl , refl
exitKeepsReason reason .(_ ∷ _) actual (more () tail)

exitHasNoLaterEffect : ∀ reason events after → Trace (exited reason) events after → events ≡ []
exitHasNoLaterEffect reason .[] .(exited reason) (empty _) = refl
exitHasNoLaterEffect reason .(_ ∷ _) after (more () tail)

-- Positive partial writes preserve the full frame, including across new
-- input arrivals. A later completed response never resets this prefix.
writtenKeepsFrame : ∀ (sent prefix remaining : List Byte) →
  (sent ++ prefix) ++ remaining ≡ sent ++ (prefix ++ remaining)
writtenKeepsFrame = List.++-assoc

ownedFrame : State → Maybe (List Byte)
ownedFrame (serving (live active replies (just (outgoing sent remaining)))) = just (sent ++ remaining)
ownedFrame (serving (live active replies nothing)) = nothing
ownedFrame (stopping reason cleanupProgram) = nothing
ownedFrame (exited reason) = nothing

physicalWriteKeepsFrame : ∀ before bytes after → Step before (wrote bytes) after →
  ownedFrame after ≡ ownedFrame before
physicalWriteKeepsFrame before bytes after (written active replies sent byte prefix remaining) =
  cong just (writtenKeepsFrame sent (byte ∷ prefix) remaining)

completionKeepsExistingFrame : ∀ active replies output bytes →
  ownedFrame (finish active replies (just output) bytes Exchange.nextLine) ≡
    just (Outgoing.sent output ++ Outgoing.remaining output)
completionKeepsExistingFrame active replies (outgoing sent remaining) bytes = refl

existingOutputIsRetained : ∀ active replies output →
  Live.output (normalize (live active replies (just output))) ≡ just output
existingOutputIsRetained active replies output = refl

oldestReplyStartsFirst : ∀ active first rest →
  normalize (live active (first ∷ rest) nothing) ≡
    live active rest (just (outgoing [] first))
oldestReplyStartsFirst active first rest = refl

disconnectStartsOwnedCleanup : ∀ current →
  Step (serving (normalize current)) (read [] refl)
    (stopping eof (Cleanup.stop (Live.active (normalize current))))
disconnectStartsOwnedCleanup current = received current [] refl

stoppingCannotExecuteApplication : ∀ reason program operation reply after →
  Step (stopping reason program) (effect operation reply) after → ⊥
stoppingCannotExecuteApplication reason program operation reply after ()

-- An error exit records the real join reply too; failed cleanup cannot be
-- replaced with successful EOF merely because request futures were dropped.
stopRequiresDropAndJoin : ∀ reason active events actual →
  Trace (stopping reason (Cleanup.stop active)) events (exited actual) →
  Σ Cleanup.Result (λ receipt →
    events ≡ (cleanup (Cleanup.dropOwnedRequests active , tt) ∷
      cleanup (Cleanup.finishOperationHost , receipt) ∷ cleaned ∷ []) ×
    actual ≡ cleanupExit reason receipt)
stopRequiresDropAndJoin reason active events actual
  (more (cleanupReply .reason .(Cleanup.dropOwnedRequests active) _ .tt)
    (more (cleanupReply .reason .Cleanup.finishOperationHost _ receipt)
      (more (stopped .reason .receipt) tail)))
  with exitKeepsReason (cleanupExit reason receipt) _ actual tail
... | refl , refl = receipt , refl , refl

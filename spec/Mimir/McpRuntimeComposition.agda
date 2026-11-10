{-# OPTIONS --safe #-}
-- Concurrent transport with concrete in-flight host ownership. A handler's
-- owner is recorded before its reply, and remains the same owner on return.
-- Cleanup failures outlive their completed response tasks in the host registry.
module Mimir.McpRuntimeComposition where

open import Data.List using (List; []; _∷_; map; _++_)
import Data.List.Properties as List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationStore as Store
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
import Mimir.McpRuntime as Runtime
import Mimir.McpExchange as Exchange
import Mimir.McpApplicationComposition as Composition
import Mimir.McpEnvelope as Envelope
import Mimir.StructuredValue as Wire
import Mimir.ReadLine as Lines
import Mimir.McpInput as InputDependency
import Mimir.ToolCatalog as Tools

module Run (environment : Application.Environment) (format : Encoding.Formatting)
  (conversion : Conversion.Contract) where
  module R = Runtime conversion
  module C = Composition.Compose environment format conversion using (module H; module WithDiagnostic)
  private
    module Input = InputDependency conversion
    module H = C.H
    module Physical = H.Physical
    module A = Application.Run environment using (State; Step; Event; event; Runs; reached)

  -- These are the only two non-handler dependency effects in a task.
  data External : Exchange.Effect → Set where
    formatting : ∀ value → External (Exchange.formatTool value)
    serializing : ∀ response → External (Exchange.serialize response)

  data Work : Set where
    fresh : R.Task → Work
    handling : (name : Envelope.Text) (arguments : Wire.Value) →
      (continuation : Exchange.Reply (Exchange.handleTool name arguments) → Exchange.Script Exchange.Outcome) →
      List Byte → H.InFlight name arguments → Work

  rawTask : Work → R.Task
  rawTask (fresh requestTask) = requestTask
  rawTask (handling name arguments continuation buffer flight) =
    R.task (Exchange.ask (Exchange.handleTool name arguments) continuation) buffer

  owned : Work → List Store.ExecutionRow
  owned (fresh requestTask) = []
  owned (handling name arguments continuation buffer flight) = H.InFlight.owned flight

  ownedWork : List Work → List Store.ExecutionRow
  ownedWork [] = []
  ownedWork (work ∷ rest) = owned work ++ ownedWork rest

  -- Every retained value is an actual host result. Successful exits contribute
  -- no pending row; a failed physical cleanup retains its exact original entry.
  record Retained : Set where
    constructor keepHostResult
    field
      tool : Tools.Tool
      arguments : Wire.Value
      events : List A.Event
      result : Physical.Result tool arguments events

  pendingResult : ∀ {tool arguments events} → Physical.Result tool arguments events → List Store.ExecutionRow
  pendingResult (Physical.returned execution) = []
  pendingResult (Physical.cleanupPending initial entered entry result ran final pending) = Physical.ownedRows entry

  pendingRows : List Retained → List Store.ExecutionRow
  pendingRows [] = []
  pendingRows (item ∷ rest) = pendingResult (Retained.result item) ++ pendingRows rest

  appendPrefix : ∀ before middle after first second →
    Physical.DatabasePrefix before first middle → Physical.DatabasePrefix middle second after →
    Physical.DatabasePrefix before (first ++ second) after
  appendPrefix before .before after .[] second (Physical.here .before) following = following
  appendPrefix before middle after .(A.event before next physical ∷ rest) second
    (Physical.next .before next .middle physical rest previous) following =
    Physical.next before next after physical (rest ++ second)
      (appendPrefix next middle after rest second previous following)

  advanceFlight : ∀ {name arguments} (flight : H.InFlight name arguments) after →
    A.Step (Physical.Active.current (H.InFlight.active flight)) after → H.InFlight name arguments
  advanceFlight flight after physical = record
    { tool = H.InFlight.tool flight; named = H.InFlight.named flight
    ; active = record
      { initial = Physical.Active.initial active; entered = Physical.Active.entered active
      ; entry = Physical.Active.entry active
      ; events = Physical.Active.events active ++ (A.event (Physical.Active.current active) after physical ∷ [])
      ; current = after
      ; observed = appendPrefix _ _ _ (Physical.Active.events active) _
          (Physical.Active.observed active)
          (Physical.next _ after after physical [] (Physical.here after)) } }
    where active = H.InFlight.active flight

  module WithDiagnostic (render : C.H.Diagnostic → Text) where
    module Bound = C.WithDiagnostic render using (Materialized; error; value; correction; preparation; partial; boundReference)

    data State : Set where
      serving : List Work → R.Frames → Maybe R.Outgoing → List Retained → State
      stopping : R.Exit → List Work → List Retained → R.Cleanup.P.Script R.Cleanup.Result → State
      exited : R.Exit → State

    start : State
    start = serving [] [] nothing []

    raw : State → R.State
    raw (serving work replies output retained) = R.serve (map rawTask work) replies output
    raw (stopping reason work retained cleanupProgram) = R.stopping reason cleanupProgram
    raw (exited reason) = R.exited reason

    stop : R.Exit → List Work → List Retained → State
    stop reason work retained = stopping reason work retained (R.Cleanup.stop (map rawTask work))

    enqueue : List Work → R.Frames → Maybe R.Outgoing → List Retained → List Byte → Exchange.Outcome → State
    enqueue work replies output retained bytes Exchange.nextLine =
      serving work (R.queueResponse replies bytes) output retained
    enqueue work replies output retained bytes (Exchange.stopped failure) =
      stop (R.exchangeFailure failure) work retained

    fromBody : ∀ {input} → List Work → R.Frames → Maybe R.Outgoing → List Retained →
      Input.BodyOutcome input → State
    fromBody work replies output retained (Input.blank proof) =
      serving (work ++ (fresh (R.task (Exchange.done Exchange.nextLine) []) ∷ [])) replies output retained
    fromBody work replies output retained (Input.accepted value) =
      serving (work ++ (fresh (R.task (Exchange.exchange (Input.request value)) []) ∷ [])) replies output retained
    fromBody work replies output retained (Input.rejected failure) =
      serving (work ++ (fresh (R.task (Exchange.parseError (Conversion.JSONError.message failure)) []) ∷ [])) replies output retained
    fromBody work replies output retained (Input.panicked message) =
      stop (R.arithmeticPanic message) work retained

    fromRead : ∀ {input} → List Work → R.Frames → Maybe R.Outgoing → List Retained →
      Input.Outcome input → State
    fromRead work replies output retained (Input.eof proof) = stop R.eof work retained
    fromRead work replies output retained (Input.invalidUTF8 framed reason) =
      serving (work ++ (fresh (R.task (Exchange.parseError reason) []) ∷ [])) replies output retained
    fromRead work replies output retained (Input.line framed text parsed) =
      fromBody work replies output retained parsed

    data Event : Set where
      wire : R.Event → Event
      entered : ∀ name arguments → H.InFlight name arguments → Event
      database : A.Event → Event
      handled : Envelope.Text → Wire.Value → List A.Event → H.Result → Text ⊎ Wire.Value → Event
      joined : ∀ owned before after → Physical.StoppedRequests owned before after → Event

    data Step : State → Event → State → Set where
      received : ∀ work replies output retained input wholeLine →
        let current = R.normalize (R.live (map rawTask work) replies output) in
        Step (serving work replies output retained) (wire (R.read input wholeLine))
          (fromRead work (R.Live.replies current) (R.Live.output current) retained
            (Input.Parser.read input))
      failedRead : ∀ work replies output retained reason →
        Step (serving work replies output retained) (wire (R.readError reason)) (stop (R.readFailure reason) work retained)
      external : ∀ prefix suffix replies output retained buffer operation continuation reply → External operation →
        Step (serving (prefix ++ (fresh (R.task (Exchange.ask operation continuation) buffer) ∷ suffix)) replies output retained)
          (wire (R.effect operation reply))
          (serving (prefix ++ (fresh (R.task (continuation reply) buffer) ∷ suffix)) replies output retained)
      rejected : ∀ prefix suffix replies output retained name arguments continuation buffer report reply →
        H.Handled name arguments [] (H.inputCorrection report) →
        Bound.Materialized (H.inputCorrection report) reply →
        Step (serving (prefix ++ (fresh (R.task (Exchange.ask (Exchange.handleTool name arguments) continuation) buffer) ∷ suffix)) replies output retained)
          (handled name arguments [] (H.inputCorrection report) reply)
          (serving (prefix ++ (fresh (R.task (continuation reply) buffer) ∷ suffix)) replies output retained)
      started : ∀ prefix suffix replies output retained name arguments continuation buffer flight →
        Step (serving (prefix ++ (fresh (R.task (Exchange.ask (Exchange.handleTool name arguments) continuation) buffer) ∷ suffix)) replies output retained)
          (entered name arguments flight)
          (serving (prefix ++ (handling name arguments continuation buffer flight ∷ suffix)) replies output retained)
      progressed : ∀ prefix suffix replies output retained name arguments continuation buffer flight after physical →
        Step (serving (prefix ++ (handling name arguments continuation buffer flight ∷ suffix)) replies output retained)
          (database (A.event (Physical.Active.current (H.InFlight.active flight)) after physical))
          (serving (prefix ++ (handling name arguments continuation buffer (advanceFlight flight after physical) ∷ suffix)) replies output retained)
      completedHandler : ∀ prefix suffix replies output retained name arguments continuation buffer flight remaining result ran final hostExit reply →
        let execution = Physical.finishActive (H.InFlight.active flight) remaining result ran final hostExit in
        Bound.Materialized (H.finishHosted (Physical.returned execution)) reply →
        Step (serving (prefix ++ (handling name arguments continuation buffer flight ∷ suffix)) replies output retained)
          (handled name arguments (Physical.Active.events (H.InFlight.active flight) ++ remaining)
            (H.finishHosted (Physical.returned execution)) reply)
          (serving (prefix ++ (fresh (R.task (continuation reply) buffer) ∷ suffix)) replies output retained)
      pendingHandler : ∀ prefix suffix replies output retained name arguments continuation buffer flight remaining result ran final pending reply →
        let hosted = Physical.pendingActive (H.InFlight.active flight) remaining result ran final pending in
        Bound.Materialized (H.finishHosted hosted) reply →
        Step (serving (prefix ++ (handling name arguments continuation buffer flight ∷ suffix)) replies output retained)
          (handled name arguments (Physical.Active.events (H.InFlight.active flight) ++ remaining) (H.finishHosted hosted) reply)
          (serving (prefix ++ (fresh (R.task (continuation reply) buffer) ∷ suffix)) replies output
            (keepHostResult (H.InFlight.tool flight) arguments (Physical.Active.events (H.InFlight.active flight) ++ remaining) hosted ∷ retained))
      bufferWrite : ∀ prefix suffix replies output retained bytes buffer continuation →
        Step (serving (prefix ++ (fresh (R.task (Exchange.ask (Exchange.write bytes) continuation) buffer) ∷ suffix)) replies output retained)
          (wire (R.bufferWrite bytes))
          (serving (prefix ++ (fresh (R.task (continuation Exchange.written) (buffer ++ bytes)) ∷ suffix)) replies output retained)
      bufferFlush : ∀ prefix suffix replies output retained buffer continuation →
        Step (serving (prefix ++ (fresh (R.task (Exchange.ask Exchange.flush continuation) buffer) ∷ suffix)) replies output retained)
          (wire R.bufferFlush)
          (serving (prefix ++ (fresh (R.task (continuation Exchange.completed) buffer) ∷ suffix)) replies output retained)
      returned : ∀ prefix suffix replies output retained buffer outcome →
        Step (serving (prefix ++ (fresh (R.task (Exchange.done outcome) buffer) ∷ suffix)) replies output retained)
          (wire R.completedTask) (enqueue (prefix ++ suffix) replies output retained buffer outcome)
      written : ∀ work replies retained sent byte bytes rest →
        Step (serving work replies (just (R.outgoing sent ((byte ∷ bytes) ++ rest))) retained)
          (wire (R.wrote (byte ∷ bytes)))
          (serving work replies (just (R.outgoing (sent ++ (byte ∷ bytes)) rest)) retained)
      flushed : ∀ work replies retained sent →
        Step (serving work replies (just (R.outgoing sent [])) retained) (wire R.flushed)
          (serving work replies nothing retained)
      writeFailed : ∀ work replies retained sent remaining reason →
        Step (serving work replies (just (R.outgoing sent remaining)) retained) (wire (R.writeError reason))
          (stop (R.writeFailure reason) work retained)
      flushFailed : ∀ work replies retained sent reason →
        Step (serving work replies (just (R.outgoing sent [])) retained) (wire (R.flushError reason))
          (stop (R.flushFailure reason) work retained)
      dropped : ∀ reason work retained continuation →
        Step (stopping reason work retained (R.Cleanup.P.ask (R.Cleanup.dropOwnedRequests (map rawTask work)) continuation))
          (wire (R.cleanup (R.Cleanup.dropOwnedRequests (map rawTask work) , tt)))
          (stopping reason work retained (continuation tt))
      hostJoined : ∀ reason work retained continuation before after →
        (acknowledgement : Physical.StoppedRequests (ownedWork work ++ pendingRows retained) before after) →
        Step (stopping reason work retained (R.Cleanup.P.ask R.Cleanup.finishOperationHost continuation))
          (joined (ownedWork work ++ pendingRows retained) before after acknowledgement)
          (stopping reason work retained (continuation R.Cleanup.joined))
      hostFailed : ∀ reason work retained continuation message →
        Step (stopping reason work retained (R.Cleanup.P.ask R.Cleanup.finishOperationHost continuation))
          (wire (R.cleanup (R.Cleanup.finishOperationHost , R.Cleanup.failed message)))
          (stopping reason work retained (continuation (R.Cleanup.failed message)))
      stopped : ∀ reason work retained receipt →
        Step (stopping reason work retained (R.Cleanup.P.done receipt)) (wire R.cleaned)
          (exited (R.cleanupExit reason receipt))

    data Trace : State → List Event → State → Set where
      empty : ∀ state → Trace state [] state
      more : ∀ {before event middle events after} → Step before event middle → Trace middle events after →
        Trace before (event ∷ events) after

    outer : Event → List R.Event
    outer (wire receipt) = receipt ∷ []
    outer (entered name arguments flight) = []
    outer (database receipt) = []
    outer (handled name arguments events result reply) = R.effect (Exchange.handleTool name arguments) reply ∷ []
    outer (joined owned before after acknowledgement) = R.cleanup (R.Cleanup.finishOperationHost , R.Cleanup.joined) ∷ []

    bodyRaw : ∀ {input} work replies output retained (parsed : Input.BodyOutcome input) →
      raw (fromBody work replies output retained parsed) ≡
      R.bodyOutcome (R.live (map rawTask work) replies output) parsed
    bodyRaw work replies output retained (Input.blank proof)
      rewrite List.map-++ rawTask work (fresh (R.task (Exchange.done Exchange.nextLine) []) ∷ []) = refl
    bodyRaw work replies output retained (Input.accepted value)
      rewrite List.map-++ rawTask work (fresh (R.task (Exchange.exchange (Input.request value)) []) ∷ []) = refl
    bodyRaw work replies output retained (Input.rejected failure)
      rewrite List.map-++ rawTask work (fresh (R.task (Exchange.parseError (Conversion.JSONError.message failure)) []) ∷ []) = refl
    bodyRaw work replies output retained (Input.panicked message) = refl

    readRaw : ∀ {input} work replies output retained (parsed : Input.Outcome input) →
      raw (fromRead work replies output retained parsed) ≡
      R.readOutcome (R.live (map rawTask work) replies output) parsed
    readRaw work replies output retained (Input.eof proof) = refl
    readRaw work replies output retained (Input.invalidUTF8 framed reason)
      rewrite List.map-++ rawTask work (fresh (R.task (Exchange.parseError reason) []) ∷ []) = refl
    readRaw work replies output retained (Input.line framed text parsed) = bodyRaw work replies output retained parsed

    normalizedView : ∀ active replies output →
      R.normalize (R.live active replies output) ≡ R.live active
        (R.Live.replies (R.normalize (R.live active replies output)))
        (R.Live.output (R.normalize (R.live active replies output)))
    normalizedView active replies (just output) = refl
    normalizedView active [] nothing = refl
    normalizedView active (first ∷ rest) nothing = refl

    dependency : ∀ operation → External operation → R.Dependency operation
    dependency .(Exchange.formatTool value) (formatting value) = R.format value
    dependency .(Exchange.serialize response) (serializing response) = R.serialize response

    one : ∀ {before event after} → R.Step before event after → R.Trace before (event ∷ []) after
    one proof = R.more proof (R.empty _)

    -- The richer ownership states introduce only stuttering at host entry and
    -- database progress. Every byte/queue/dependency event is an actual native
    -- scheduler transition; no independent script interpreter is substituted.
    stepTransport : ∀ {before event after} → Step before event after →
      R.Trace (raw before) (outer event) (raw after)
    stepTransport (received work replies output retained input wholeLine) =
      subst (λ target → R.Trace (R.serve (map rawTask work) replies output) (R.read input wholeLine ∷ []) target)
        (trans
          (cong (λ current → R.readOutcome current (Input.Parser.read input))
            (normalizedView (map rawTask work) replies output))
          (sym (readRaw work _ _ retained (Input.Parser.read input))))
        (one (R.received (R.live (map rawTask work) replies output) input wholeLine))
    stepTransport (failedRead work replies output retained reason) =
      one (R.failedRead (R.live (map rawTask work) replies output) reason)
    stepTransport (external prefix suffix replies output retained buffer operation continuation reply permitted)
      rewrite List.map-++ rawTask prefix (fresh (R.task (Exchange.ask operation continuation) buffer) ∷ suffix)
            | List.map-++ rawTask prefix (fresh (R.task (continuation reply) buffer) ∷ suffix) =
      one (R.replied (map rawTask prefix) (map rawTask suffix) replies output buffer operation continuation reply (dependency operation permitted))
    stepTransport (rejected prefix suffix replies output retained name arguments continuation buffer report reply admitted materialized)
      rewrite List.map-++ rawTask prefix (fresh (R.task (Exchange.ask (Exchange.handleTool name arguments) continuation) buffer) ∷ suffix)
            | List.map-++ rawTask prefix (fresh (R.task (continuation reply) buffer) ∷ suffix) =
      one (R.replied (map rawTask prefix) (map rawTask suffix) replies output buffer _ continuation reply (R.handle name arguments))
    stepTransport (started prefix suffix replies output retained name arguments continuation buffer flight)
      rewrite List.map-++ rawTask prefix (fresh (R.task (Exchange.ask (Exchange.handleTool name arguments) continuation) buffer) ∷ suffix)
            | List.map-++ rawTask prefix (handling name arguments continuation buffer flight ∷ suffix) = R.empty _
    stepTransport (progressed prefix suffix replies output retained name arguments continuation buffer flight after physical)
      rewrite List.map-++ rawTask prefix (handling name arguments continuation buffer flight ∷ suffix)
            | List.map-++ rawTask prefix (handling name arguments continuation buffer (advanceFlight flight after physical) ∷ suffix) = R.empty _
    stepTransport (completedHandler prefix suffix replies output retained name arguments continuation buffer flight remaining result ran final hostExit reply materialized)
      rewrite List.map-++ rawTask prefix (handling name arguments continuation buffer flight ∷ suffix)
            | List.map-++ rawTask prefix (fresh (R.task (continuation reply) buffer) ∷ suffix) =
      one (R.replied (map rawTask prefix) (map rawTask suffix) replies output buffer _ continuation reply (R.handle name arguments))
    stepTransport (pendingHandler prefix suffix replies output retained name arguments continuation buffer flight remaining result ran final pending reply materialized)
      rewrite List.map-++ rawTask prefix (handling name arguments continuation buffer flight ∷ suffix)
            | List.map-++ rawTask prefix (fresh (R.task (continuation reply) buffer) ∷ suffix) =
      one (R.replied (map rawTask prefix) (map rawTask suffix) replies output buffer _ continuation reply (R.handle name arguments))
    stepTransport (bufferWrite prefix suffix replies output retained bytes buffer continuation)
      rewrite List.map-++ rawTask prefix (fresh (R.task (Exchange.ask (Exchange.write bytes) continuation) buffer) ∷ suffix)
            | List.map-++ rawTask prefix (fresh (R.task (continuation Exchange.written) (buffer ++ bytes)) ∷ suffix) =
      one (R.bufferedWrite (map rawTask prefix) (map rawTask suffix) replies output buffer bytes continuation)
    stepTransport (bufferFlush prefix suffix replies output retained buffer continuation)
      rewrite List.map-++ rawTask prefix (fresh (R.task (Exchange.ask Exchange.flush continuation) buffer) ∷ suffix)
            | List.map-++ rawTask prefix (fresh (R.task (continuation Exchange.completed) buffer) ∷ suffix) =
      one (R.bufferedFlush (map rawTask prefix) (map rawTask suffix) replies output buffer continuation)
    stepTransport (returned prefix suffix replies output retained buffer Exchange.nextLine)
      rewrite List.map-++ rawTask prefix (fresh (R.task (Exchange.done Exchange.nextLine) buffer) ∷ suffix)
            | List.map-++ rawTask prefix suffix =
      one (R.returned (map rawTask prefix) (map rawTask suffix) replies output buffer Exchange.nextLine)
    stepTransport (returned prefix suffix replies output retained buffer (Exchange.stopped failure))
      rewrite List.map-++ rawTask prefix (fresh (R.task (Exchange.done (Exchange.stopped failure)) buffer) ∷ suffix)
            | List.map-++ rawTask prefix suffix =
      one (R.returned (map rawTask prefix) (map rawTask suffix) replies output buffer (Exchange.stopped failure))
    stepTransport (written work replies retained sent byte bytes rest) = one (R.written (map rawTask work) replies sent byte bytes rest)
    stepTransport (flushed work replies retained sent) = one (R.flushed (map rawTask work) replies sent)
    stepTransport (writeFailed work replies retained sent remaining reason) = one (R.failedWrite (map rawTask work) replies sent remaining reason)
    stepTransport (flushFailed work replies retained sent reason) = one (R.failedFlush (map rawTask work) replies sent reason)
    stepTransport (dropped reason work retained continuation) = one (R.cleanupReply reason _ continuation tt)
    stepTransport (hostJoined reason work retained continuation before after acknowledgement) = one (R.cleanupReply reason _ continuation R.Cleanup.joined)
    stepTransport (hostFailed reason work retained continuation message) = one (R.cleanupReply reason _ continuation (R.Cleanup.failed message))
    stepTransport (stopped reason work retained receipt) = one (R.stopped reason receipt)

    outerEvents : List Event → List R.Event
    outerEvents [] = []
    outerEvents (event ∷ rest) = outer event ++ outerEvents rest

    appendTransport : ∀ before middle after first second →
      R.Trace before first middle → R.Trace middle second after → R.Trace before (first ++ second) after
    appendTransport before .before after .[] second (R.empty .before) following = following
    appendTransport before middle after .(event ∷ rest) second (R.more {event = event} {events = rest} step previous) following =
      R.more step (appendTransport _ middle after rest second previous following)

    traceTransport : ∀ before events after → Trace before events after →
      R.Trace (raw before) (outerEvents events) (raw after)
    traceTransport before .[] .before (empty .before) = R.empty (raw before)
    traceTransport before .(event ∷ events) after (more {event = event} {events = events} physical following) =
      appendTransport (raw before) _ (raw after) (outer event) (outerEvents events)
        (stepTransport physical) (traceTransport _ events after following)

    rawStart : raw start ≡ R.reading []
    rawStart = refl

    -- This scope is deliberately the registered request rows. Ordinary/read
    -- provider workers do not acquire a row here; this is not a theorem of
    -- their physical stop merely because the computed row list is empty.
    joinedUsesActualRows : ∀ reason work retained continuation claimed before after acknowledgement target →
      Step (stopping reason work retained (R.Cleanup.P.ask R.Cleanup.finishOperationHost continuation))
        (joined claimed before after acknowledgement) target →
      claimed ≡ ownedWork work ++ pendingRows retained
    joinedUsesActualRows reason work retained continuation claimed before after acknowledgement target
      (hostJoined .reason .work .retained .continuation .before .after .acknowledgement) = refl

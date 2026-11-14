{-# OPTIONS --safe #-}
-- Server control-state composition. Input failures terminate the loop; normal
-- JSON errors receive a parse-error response and the loop may continue.
-- Each exchange finishes before the next buffered request is processed; a
-- request pipelined while an exchange runs is held, never executed
-- concurrently. Transport EOF or failure during an exchange abandons it: no
-- reply is delivered for that request and the owned operation stops with its
-- recovery cleanup.
import Mimir.StandardLibrary
module Mimir.McpRuntime (library : Mimir.StandardLibrary.Contract) where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.McpInput as InputDependency
private
  module Input = InputDependency library
import Mimir.McpExchange as Exchange
import Mimir.StandardLibrary as Library
import Mimir.ReadLine as Lines

data Exit : Set where
  eof : Exit
  readFailure : Text → Exit
  invalidUTF8 : Text → Exit
  arithmeticPanic : Exit

-- A complete request line observed while an exchange is still running. At
-- most one is held: a stdio MCP client sends one request and waits for its
-- response, so a later pipelined line replaces the earlier held one.
HeldInput : Set
HeldInput = Σ (List Byte) (λ input → Lines.Scanned.remainder (Lines.scan input) ≡ [])

data State : Set where
  reading : State
  executing : Maybe HeldInput → Exchange.Script Exchange.Outcome → State
  exited : Exit → State

bodyOutcome : ∀ {input} → Input.BodyOutcome input → State
bodyOutcome (Input.blank proof) = reading
bodyOutcome (Input.accepted value) = executing nothing (Exchange.exchange (Input.request value))
bodyOutcome (Input.rejected failure) = executing nothing (Exchange.parseError (Library.JSONError.message failure))
bodyOutcome (Input.panicked message) = exited arithmeticPanic

readOutcome : ∀ {input} → Input.Outcome input → State
readOutcome (Input.eof proof) = exited eof
readOutcome (Input.invalidUTF8 framed failure) = exited (invalidUTF8 failure)
readOutcome (Input.line framed text parsedBody) = bodyOutcome parsedBody

finish : Maybe HeldInput → Exchange.Outcome → State
finish nothing Exchange.nextLine = reading
finish (just (input , wholeLine)) Exchange.nextLine = readOutcome (Input.Parser.read input)

-- A held pipelined request is processed exactly as if it had been read after
-- the exchange finished — same parser, same outcomes.
finishProcessesHeld : ∀ input wholeLine →
  finish (just (input , wholeLine)) Exchange.nextLine ≡ readOutcome (Input.Parser.read input)
finishProcessesHeld input wholeLine = refl

-- Without a held request the loop waits for new transport input.
finishWithoutHeldWaits : finish nothing Exchange.nextLine ≡ reading
finishWithoutHeldWaits = refl

data Event : Set where
  read : ∀ input → Lines.Scanned.remainder (Lines.scan input) ≡ [] → Event
  ended : Event
  readError : Text → Event
  effect : Exchange.Event → Event
  returned : Event

data Step : State → Event → State → Set where
  received : ∀ input wholeLine → Step reading (read input wholeLine)
    (readOutcome (Input.Parser.read input))
  failedRead : ∀ message → Step reading (readError message) (exited (readFailure message))

  -- A request pipelined while an exchange runs is held until the exchange
  -- finishes; the running exchange is neither restarted nor duplicated, and
  -- exchanges stay strictly sequential.
  held : ∀ held script input wholeLine →
    Step (executing held script) (read input wholeLine)
      (executing (just (input , wholeLine)) script)

  -- The client's transport reached EOF mid-exchange: it will send no more
  -- requests. Two conforming outcomes:
  --  · finish — the exchange runs to completion (its reply, and any held
  --    pipelined requests behind it, are still answered); or
  --  · abandon — the exchange is dropped without a reply: owned work stops
  --    with its recovery cleanup and the loop exits.
  -- The implementation bounds how long it waits for the finish outcome
  -- before choosing abandon, so blocked work cannot wait indefinitely.
  endedObserved : ∀ held script →
    Step (executing held script) ended (executing held script)
  disconnected : ∀ held script → Step (executing held script) ended (exited eof)
  failedReadDuring : ∀ held script message →
    Step (executing held script) (readError message) (exited (readFailure message))

  replied : ∀ held operation continuation reply →
    Step (executing held (Exchange.ask operation continuation)) (effect (operation , reply))
      (executing held (continuation reply))
  returned : ∀ held outcome → Step (executing held (Exchange.done outcome)) returned (finish held outcome)

data Trace : State → List Event → State → Set where
  empty : ∀ state → Trace state [] state
  more : ∀ {before event middle events after} → Step before event middle →
    Trace middle events after → Trace before (event ∷ events) after

exitHasNoStep : ∀ reason event after → Step (exited reason) event after → ⊥
exitHasNoStep reason event after ()

exitHasNoLaterEffect : ∀ reason events after → Trace (exited reason) events after → events ≡ []
exitHasNoLaterEffect reason .[] .(exited reason) (empty _) = refl
exitHasNoLaterEffect reason .(_ ∷ _) after (more () tail)

-- Disconnecting mid-exchange abandons the exchange without a reply; combined
-- with exitHasNoLaterEffect, the whole loop then terminates with no further
-- effects.
disconnectAbandonsExchange : ∀ held script → Step (executing held script) ended (exited eof)
disconnectAbandonsExchange = disconnected

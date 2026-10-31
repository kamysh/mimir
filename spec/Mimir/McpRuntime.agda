{-# OPTIONS --safe #-}
-- Server control-state composition. Input failures terminate the loop; normal
-- JSON errors write a parse-error response and may continue after its flush.
-- Each exchange finishes before the next read. Traces need not be infinite.
import Mimir.FloatConversion
module Mimir.McpRuntime (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.McpInput as InputDependency
private
  module Input = InputDependency floatConversion
import Mimir.McpExchange as Exchange
import Mimir.JsonErrorDisplay as Display
import Mimir.JsonFlow as Flow
import Mimir.UTF8Text as UTF8
import Mimir.UTF8Packet as Packet
import Mimir.ReadLine as Lines
import Mimir.SignedMachine as Machine

data Exit : Set where
  eof : Exit
  readFailure : Text → Exit
  invalidUTF8 : Packet.Error → Exit
  arithmeticPanic : Exit
  exchangeFailure : Exchange.Failure → Exit

data State : Set where
  reading : State
  executing : Exchange.Script Exchange.Outcome → State
  exited : Exit → State

bodyOutcome : ∀ {input} → Input.BodyOutcome input → State
bodyOutcome (Input.blank proof) = reading
bodyOutcome (Input.accepted value position complete) = executing (Exchange.exchange (Input.request value))
bodyOutcome (Input.rejected failure) with Display.renderRejected failure
... | nothing = exited arithmeticPanic
... | just message = executing (Exchange.parseError message)
bodyOutcome (Input.panicked position) = exited arithmeticPanic

readOutcome : ∀ {input} → Input.Outcome input → State
readOutcome (Input.eof proof) = exited eof
readOutcome (Input.invalidUTF8 framed failure) = exited (invalidUTF8 failure)
readOutcome (Input.line framed textValue parsedBody) = bodyOutcome parsedBody

finish : Exchange.Outcome → State
finish Exchange.nextLine = reading
finish (Exchange.stopped failure) = exited (exchangeFailure failure)

data Event : Set where
  read : ∀ input → Lines.Scanned.remainder (Lines.scan input) ≡ [] → Event
  readError : Text → Event
  effect : Exchange.Event → Event
  returned : Event

data Step (checks : Machine.OverflowChecks) : State → Event → State → Set where
  received : ∀ input wholeLine → Step checks reading (read input wholeLine)
    (readOutcome (Input.Parser.read checks input))
  failedRead : ∀ message → Step checks reading (readError message) (exited (readFailure message))
  replied : ∀ operation continuation reply →
    Step checks (executing (Exchange.ask operation continuation)) (effect (operation , reply))
      (executing (continuation reply))
  returned : ∀ outcome → Step checks (executing (Exchange.done outcome)) returned (finish outcome)

data Trace (checks : Machine.OverflowChecks) : State → List Event → State → Set where
  empty : ∀ state → Trace checks state [] state
  more : ∀ {before event middle events after} → Step checks before event middle →
    Trace checks middle events after → Trace checks before (event ∷ events) after

exitHasNoStep : ∀ checks reason event after → Step checks (exited reason) event after → ⊥
exitHasNoStep checks reason event after ()

exitHasNoLaterEffect : ∀ checks reason events after → Trace checks (exited reason) events after → events ≡ []
exitHasNoLaterEffect checks reason .[] .(exited reason) (empty _) = refl
exitHasNoLaterEffect checks reason .(_ ∷ _) after (more () tail)

noConcurrentRead : ∀ checks script input wholeLine after →
  Step checks (executing script) (read input wholeLine) after → ⊥
noConcurrentRead checks script input wholeLine after ()


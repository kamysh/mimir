{-# OPTIONS --safe #-}
-- Server control-state composition. Input failures terminate the loop; normal
-- JSON errors write a parse-error response and may continue after its flush.
-- Each exchange finishes before the next read. Traces need not be infinite.
import Mimir.StandardLibrary
module Mimir.McpRuntime (library : Mimir.StandardLibrary.Contract) where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
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
  exchangeFailure : Exchange.Failure → Exit

data State : Set where
  reading : State
  executing : Exchange.Script Exchange.Outcome → State
  exited : Exit → State

bodyOutcome : ∀ {input} → Input.BodyOutcome input → State
bodyOutcome (Input.blank proof) = reading
bodyOutcome (Input.accepted value) = executing (Exchange.exchange (Input.request value))
bodyOutcome (Input.rejected failure) = executing (Exchange.parseError (Library.JSONError.message failure))
bodyOutcome (Input.panicked message) = exited arithmeticPanic

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

data Step : State → Event → State → Set where
  received : ∀ input wholeLine → Step reading (read input wholeLine)
    (readOutcome (Input.Parser.read input))
  failedRead : ∀ message → Step reading (readError message) (exited (readFailure message))
  replied : ∀ operation continuation reply →
    Step (executing (Exchange.ask operation continuation)) (effect (operation , reply))
      (executing (continuation reply))
  returned : ∀ outcome → Step (executing (Exchange.done outcome)) returned (finish outcome)

data Trace : State → List Event → State → Set where
  empty : ∀ state → Trace state [] state
  more : ∀ {before event middle events after} → Step before event middle →
    Trace middle events after → Trace before (event ∷ events) after

exitHasNoStep : ∀ reason event after → Step (exited reason) event after → ⊥
exitHasNoStep reason event after ()

exitHasNoLaterEffect : ∀ reason events after → Trace (exited reason) events after → events ≡ []
exitHasNoLaterEffect reason .[] .(exited reason) (empty _) = refl
exitHasNoLaterEffect reason .(_ ∷ _) after (more () tail)

noConcurrentRead : ∀ script input wholeLine after →
  Step (executing script) (read input wholeLine) after → ⊥
noConcurrentRead script input wholeLine after ()


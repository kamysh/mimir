{-# OPTIONS --safe #-}
-- Request-loop composition: a complete exchange requires concrete application
-- executions, and no next read occurs before its response write/flush finishes.
module Mimir.McpRuntimeComposition where

open import Data.List using (List; []; _∷_; map; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationProtocol as Application
import Mimir.PublicEncoding as Encoding
import Mimir.FloatConversion as Conversion
import Mimir.McpRuntime as Runtime
import Mimir.McpExchange as Exchange
import Mimir.McpApplicationComposition as Composition
import Mimir.ReadLine as Lines
import Mimir.SignedMachine as Machine

module Run (environment : Application.Environment) (format : Encoding.Formatting)
  (conversion : Conversion.Contract) where
  module R = Runtime conversion
  module C = Composition.Compose environment format conversion

  module WithDiagnostic (render : C.H.Diagnostic → Text) where
    module Bound = C.WithDiagnostic render

    data Event : Set where
      read : ∀ input → Lines.Scanned.remainder (Lines.scan input) ≡ [] → Event
      readError : Text → Event
      exchange : List Bound.Event → Exchange.Outcome → Event

    data Step (checks : Machine.OverflowChecks) : R.State → Event → R.State → Set where
      received : ∀ input wholeLine after →
        R.Step checks R.reading (R.read input wholeLine) after →
        Step checks R.reading (read input wholeLine) after
      failedRead : ∀ message → Step checks R.reading (readError message) (R.exited (R.readFailure message))
      exchanged : ∀ program events result → Bound.Runs program events result →
        Step checks (R.executing program) (exchange events result) (R.finish result)

    data Trace (checks : Machine.OverflowChecks) : R.State → List Event → R.State → Set where
      empty : ∀ state → Trace checks state [] state
      more : ∀ before event middle events after → Step checks before event middle → Trace checks middle events after →
        Trace checks before (event ∷ events) after

    -- The underlying transport theorem applies to every admitted exchange;
    -- a fabricated successful tool response cannot satisfy Bound.Runs.
    exchangeTransport : ∀ program events result → Bound.Runs program events result →
      Exchange.Runs program (map Bound.outer events) result
    exchangeTransport = Bound.transportPreserved

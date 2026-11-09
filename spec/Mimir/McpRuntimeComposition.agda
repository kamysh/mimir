{-# OPTIONS --safe #-}
-- Request-loop composition: a complete exchange requires concrete application
-- executions. Input may be buffered during execution, but its queued requests
-- cannot execute before the active response write/flush finishes.
module Mimir.McpRuntimeComposition where

open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationProtocol as Application
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
import Mimir.McpRuntime as Runtime
import Mimir.McpExchange as Exchange
import Mimir.McpApplicationComposition as Composition
import Mimir.ReadLine as Lines

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
      queued : Event
      cleanup : R.Cleanup.P.Event → Event
      cleaned : Event

    data Step : R.State → Event → R.State → Set where
      received : ∀ input wholeLine after →
        R.Step (R.reading []) (R.read input wholeLine) after →
        Step (R.reading []) (read input wholeLine) after
      nextQueued : ∀ input remaining →
        Step (R.reading (input ∷ remaining)) queued (R.queuedState input remaining)
      failedRead : ∀ message → Step (R.reading []) (readError message) (R.exited (R.readFailure message))
      buffered : ∀ program pending input wholeLine →
        Step (R.executing program pending) (read input wholeLine) (R.whileRunning program pending input)
      disconnectedRead : ∀ program pending message → Step (R.executing program pending) (readError message)
        (R.stopping (R.readFailure message) R.Cleanup.stop)
      cleanupReply : ∀ reason operation continuation reply →
        Step (R.stopping reason (R.Cleanup.P.ask operation continuation)) (cleanup (operation , reply))
          (R.stopping reason (continuation reply))
      stopped : ∀ reason → Step (R.stopping reason (R.Cleanup.P.done tt)) cleaned (R.exited reason)
      exchanged : ∀ program pending events result → Bound.Runs program events result →
        Step (R.executing program pending) (exchange events result) (R.finish result pending)

    data Trace : R.State → List Event → R.State → Set where
      empty : ∀ state → Trace state [] state
      more : ∀ before event middle events after → Step before event middle → Trace middle events after →
        Trace before (event ∷ events) after

    -- The underlying transport theorem applies to every admitted exchange;
    -- a fabricated successful tool response cannot satisfy Bound.Runs.
    exchangeTransport : ∀ program events result → Bound.Runs program events result →
      Exchange.Runs program (map Bound.outer events) result
    exchangeTransport = Bound.transportPreserved

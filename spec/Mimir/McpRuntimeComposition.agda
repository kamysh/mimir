{-# OPTIONS --safe #-}
-- Request-loop composition: a complete exchange requires concrete application
-- executions, and no next read occurs before its response is delivered.
module Mimir.McpRuntimeComposition where

open import Data.List using (List; []; _∷_; map; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationStore as Store
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

    data Step : R.State → Store.World → Event → R.State → Store.World → Set where
      received : ∀ input wholeLine after store →
        R.Step R.reading (R.read input wholeLine) after →
        Step R.reading store (read input wholeLine) after store
      failedRead : ∀ message store → Step R.reading store (readError message) (R.exited (R.readFailure message)) store
      exchanged : ∀ program before events after result → Bound.Runs program before events after result →
        Step (R.executing program) before (exchange events result) (R.finish result) after

    data Trace : R.State → Store.World → List Event → R.State → Store.World → Set where
      empty : ∀ state store → Trace state store [] state store
      more : ∀ before store event middle nextStore events after finalStore →
        Step before store event middle nextStore → Trace middle nextStore events after finalStore →
        Trace before store (event ∷ events) after finalStore

    -- The underlying transport theorem applies to every admitted exchange;
    -- a fabricated successful tool response cannot satisfy Bound.Runs.
    exchangeTransport : ∀ program before events after result → Bound.Runs program before events after result →
      Exchange.Runs program (map Bound.outer events) result
    exchangeTransport = Bound.transportPreserved

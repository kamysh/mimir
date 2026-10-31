{-# OPTIONS --safe #-}
-- Spawn, handshake, and cleanup share one owned child. Failed initialization
-- drops that child before returning; success retains it for the whole batch.
module Mimir.JudgeClientStartup where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Mimir.Text using (Text)
import Mimir.FloatConversion as Conversion
import Mimir.McpClientTransport as Transport
import Mimir.JudgeMcpLifecycle as Client
import Mimir.JudgeHandshake as Handshake
import Mimir.JudgeHandshakeBinding as Binding
import Mimir.JudgeRevision as Revision
import Mimir.UnixPath as Path
import Mimir.Validation as Validation

module Run (conversion : Conversion.Contract) (diagnostics : Transport.Diagnostics conversion)
  (contract model : ℕ) (program : Text) (arguments : List Text) (config : Path.Path) (seconds : ℕ) where
  private
    module H = Handshake.Contract contract model
    module B = Binding.Bound conversion diagnostics contract model

  data Started : Revision.Error ⊎ H.Ready → Data.Maybe.Maybe Client.Client → Set where
    spawnFailed : ∀ events detail → Client.Runs (Client.start program arguments config seconds) events (inj₁ detail) →
      Started (inj₁ (Revision.error detail nothing)) nothing
    handshakeFailed : ∀ events owned calls after failure cleanup →
      Client.Runs (Client.start program arguments config seconds) events (inj₂ owned) →
      B.Runs owned H.start calls after (inj₁ failure) →
      Client.Runs (Client.dropClient after) cleanup tt →
      Started (inj₁ (Revision.error (Validation.Fault.explanation failure) nothing)) nothing
    ready : ∀ events owned calls after result →
      Client.Runs (Client.start program arguments config seconds) events (inj₂ owned) →
      B.Runs owned H.start calls after (inj₂ result) →
      Started (inj₂ result) (Data.Maybe.just after)

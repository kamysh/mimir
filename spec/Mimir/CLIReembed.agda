{-# OPTIONS --safe #-}
-- Reembedding loads configuration once, refuses missing embeddings before
-- startup, snapshots existing IDs once, and reports acknowledged backfill work.
module Mimir.CLIReembed where

import Data.Unit
open import Data.Bool using (Bool; true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
import Mimir.ConfigurationPath as Path
import Mimir.ConfigurationSchema as Config
import Mimir.ConfigurationValues as Values
import Mimir.ConfigurationProtocol as Configuration
import Mimir.ConnectionProtocol as Connection
import Mimir.ServiceStartup as Startup
import Mimir.MigrationRuntime as Migration
import Mimir.BeliefEmbedding as B

data Summary : Set where
  noBeliefs : Summary
  counts : ℕ → ℕ → Summary -- embedded, skipped; plural suffix iff embedded != 1

summary : B.Counts → Summary
summary (B.counts 0 0) = noBeliefs
summary (B.counts embedded skipped) = counts embedded skipped

module Run (sizeMaximum : ℕ) (path : Path.Path) (environment : Connection.Environment)
  (decimalPort : ℕ → Text) (certificateBlocks : Text → List Text) (unix : Bool) where
  private
    module C = Configuration.Run sizeMaximum
    module S config = Startup.Run (Config.Config.core config) environment decimalPort certificateBlocks unix
    module M = Migration.Runtime Text Text

  data Failure : Set where
    configurationFailure : Configuration.Failure → Failure
    disabled : Failure
    startupFailure : (config : Config.Config) → S.Failure config → Failure
    backfillFailure : B.Counts → B.Failure → Failure
    outputFailure : Text → Failure

  data State : Set where
    loading : Configuration.P.Script (Configuration.Failure Data.Sum.⊎ Config.Config) → State
    starting : (config : Config.Config) → S.State config → State
    embedding : (config : Config.Config) → S.Service config → B.E.Script B.Backfill → State
    printing : Summary → State
    finished : State
    failed : Failure → State

  configured : M.Inputs → Config.Config → State
  configured migrations config with Values.Config.embed (Config.Config.core config)
  ... | nothing = failed disabled
  ... | just _ = starting config (S.start config migrations)

  data Event : Set where
    configuration : Configuration.P.Event → Event
    service : (config : Config.Config) → S.Event config → Event
    backfill : B.E.Event → Event
    returned : Event
    output : Text Data.Sum.⊎ Data.Unit.⊤ → Event

  data Step (migrations : M.Inputs) : State → Event → State → Set where
    configReply : ∀ effect next reply → Step migrations (loading (Configuration.P.ask effect next))
      (configuration (effect , reply)) (loading (next reply))
    badConfig : ∀ error → Step migrations (loading (Configuration.P.done (inj₁ error))) returned (failed (configurationFailure error))
    configLoaded : ∀ config → Step migrations (loading (Configuration.P.done (inj₂ config))) returned (configured migrations config)
    startup : ∀ config before event after → S.Step config before event after →
      Step migrations (starting config before) (service config event) (starting config after)
    badService : ∀ config error → Step migrations (starting config (S.failed {config = config} error)) returned (failed (startupFailure config error))
    ready : ∀ config service → Step migrations (starting config (S.ready {config = config} service)) returned
      (embedding config service (B.reembed true))
    embedded : ∀ config service effect next reply → Step migrations (embedding config service (B.E.ask effect next))
      (backfill (effect , reply)) (embedding config service (next reply))
    completed : ∀ config service count → Step migrations (embedding config service (B.E.done (B.complete count))) returned (printing (summary count))
    interrupted : ∀ config service count error → Step migrations (embedding config service (B.E.done (B.interrupted count error))) returned
      (failed (backfillFailure count error))
    printed : ∀ value → Step migrations (printing value) (output (inj₂ Data.Unit.tt)) finished
    outputFailed : ∀ value error → Step migrations (printing value) (output (inj₁ error)) (failed (outputFailure error))

  start : State
  start = loading (C.load path)

  data Trace (migrations : M.Inputs) : State → List Event → State → Set where
    empty : ∀ state → Trace migrations state [] state
    more : ∀ before event middle events after → Step migrations before event middle → Trace migrations middle events after →
      Trace migrations before (event ∷ events) after

  exit : State → Data.Maybe.Maybe ℕ
  exit finished = just 0
  exit (failed _) = just 1
  exit _ = nothing


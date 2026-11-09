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
  needsBackend : Summary
  needsDecision : B.Counts → B.Failure → Summary

summary : B.Counts → Summary
summary (B.counts 0 0) = noBeliefs
summary (B.counts embedded skipped) = counts embedded skipped

module Run (sizeMaximum : ℕ) (path : Path.Path) (environment : Connection.Environment)
  (decimalPort : ℕ → Text) (certificateBlocks : Text → List Text) (unix : Bool) where
  private
    module C = Configuration.Run sizeMaximum
    module S configurationValue = Startup.Run (Config.Config.core configurationValue) environment decimalPort certificateBlocks unix
    module M = Migration.Runtime Text Text

  data Failure : Set where
    configurationFailure : Configuration.Failure → Failure
    startupFailure : (configurationValue : Config.Config) → S.Failure configurationValue → Failure
    outputFailure : Text → Failure

  data State : Set where
    loading : Configuration.P.Script (Configuration.Failure Data.Sum.⊎ Config.Config) → State
    starting : (configurationValue : Config.Config) → S.State configurationValue → State
    embedding : (configurationValue : Config.Config) → S.Service configurationValue → B.E.Script B.Backfill → State
    printing : Summary → State
    finished : State
    failed : Failure → State

  configured : M.Inputs → Config.Config → State
  configured migrations configurationValue with Values.Config.embed (Config.Config.core configurationValue)
  ... | nothing = printing needsBackend
  ... | just _ = starting configurationValue (S.start configurationValue migrations)

  data Event : Set where
    configuration : Configuration.P.Event → Event
    service : (configurationValue : Config.Config) → S.Event configurationValue → Event
    backfill : B.E.Event → Event
    returned : Event
    output : Text Data.Sum.⊎ Data.Unit.⊤ → Event

  data Step (migrations : M.Inputs) : State → Event → State → Set where
    configReply : ∀ effect next reply → Step migrations (loading (Configuration.P.ask effect next))
      (configuration (effect , reply)) (loading (next reply))
    badConfig : ∀ error → Step migrations (loading (Configuration.P.done (inj₁ error))) returned (failed (configurationFailure error))
    configLoaded : ∀ configurationValue → Step migrations (loading (Configuration.P.done (inj₂ configurationValue))) returned (configured migrations configurationValue)
    startup : ∀ configurationValue before event after → S.Step configurationValue before event after →
      Step migrations (starting configurationValue before) (service configurationValue event) (starting configurationValue after)
    badService : ∀ configurationValue error → Step migrations (starting configurationValue (S.failed {configurationValue = configurationValue} error)) returned (failed (startupFailure configurationValue error))
    ready : ∀ configurationValue service → Step migrations (starting configurationValue (S.ready {configurationValue = configurationValue} service)) returned
      (embedding configurationValue service (B.reembed true))
    embedded : ∀ configurationValue service effect next reply → Step migrations (embedding configurationValue service (B.E.ask effect next))
      (backfill (effect , reply)) (embedding configurationValue service (next reply))
    completed : ∀ configurationValue service count → Step migrations (embedding configurationValue service (B.E.done (B.complete count))) returned (printing (summary count))
    interrupted : ∀ configurationValue service count error → Step migrations (embedding configurationValue service (B.E.done (B.interrupted count error))) returned
      (printing (needsDecision count error))
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


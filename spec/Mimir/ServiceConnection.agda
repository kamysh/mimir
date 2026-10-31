{-# OPTIONS --safe #-}
-- Shared core connection entry point. It loads core configuration, migrates,
-- establishes the database connection, validates the graph name and constructs
-- the lazy embedding backend. Judge/model settings are not prerequisites.
module Mimir.ServiceConnection where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
import Mimir.ConfigurationSchema as Config
import Mimir.ConfigurationValues as Values
import Mimir.ConfigurationPath as Path
import Mimir.ConfigurationProtocol as Configuration
import Mimir.ConnectionProtocol as Connection
import Mimir.ServiceStartup as Startup
import Mimir.MigrationRuntime as Migration
import Mimir.ApplicationProtocol as Application

enabled : Values.Config → Bool
enabled config with Values.Config.embed config
... | nothing = false
... | just _ = true

Compatible : Values.Config → Application.Environment → Set
Compatible config environment = Application.Environment.embeddingsEnabled environment ≡ enabled config ×
  Application.Environment.dimension environment ≡ 768

module Bound (sizeMaximum : ℕ) (path : Path.Path) (environment : Connection.Environment)
  (decimalPort : ℕ → Text) (certificateBlocks : Text → List Text) (unix : Bool) where
  private
    module C = Configuration.Run sizeMaximum
    module M = Migration.Runtime Text Text
    module S config = Startup.Run (Config.Config.core config) environment decimalPort certificateBlocks unix

  data Result : Set where
    configurationFailure : Configuration.Failure → Result
    startupFailure : (config : Config.Config) → S.Failure config → Result
    connected : (config : Config.Config) → S.Service config → Result

  data Receipt (migrations : M.Inputs) : Result → Set where
    badConfig : ∀ events failure → Configuration.P.Runs (C.load path) events (inj₁ failure) →
      Receipt migrations (configurationFailure failure)
    badService : ∀ configurationEvents config startupEvents failure →
      Configuration.P.Runs (C.load path) configurationEvents (inj₂ config) →
      S.Trace config (S.start config migrations) startupEvents (S.failed {config = config} failure) →
      Receipt migrations (startupFailure config failure)
    ready : ∀ configurationEvents config startupEvents service →
      Configuration.P.Runs (C.load path) configurationEvents (inj₂ config) →
      S.Trace config (S.start config migrations) startupEvents (S.ready {config = config} service) →
      Receipt migrations (connected config service)

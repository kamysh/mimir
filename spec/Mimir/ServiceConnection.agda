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
import Mimir.StandardLibrary as Library

enabled : Values.Config → Bool
enabled configurationValue with Values.Config.embed configurationValue
... | nothing = false
... | just _ = true

-- The actual loaded core configuration fixes execution settings. Backend
-- dimensions are observed by the concrete operations; there is no global
-- 768-dimensional precondition or independently chosen parser instance.
Compatible : Config.Config → Application.Environment → Set
Compatible configurationValue environment =
  Application.Environment.configuration environment ≡ Config.Config.core configurationValue ×
  Application.Environment.embeddingsEnabled environment ≡ enabled (Config.Config.core configurationValue) ×
  Application.Environment.retirementPolicy environment ≡
    Config.Retirement.resolve (Application.Environment.library environment) (Config.Config.retirement configurationValue)

module Bound (sizeMaximum : ℕ) (path : Path.Path) (environment : Connection.Environment)
  (decimalPort : ℕ → Text) (certificateBlocks : Text → List Text) (unix : Bool) where
  private
    module C = Configuration.Run
    module M = Migration.Runtime Text Text
    module S configurationValue = Startup.Run (Config.Config.core configurationValue) environment decimalPort certificateBlocks unix

  data Result : Set where
    configurationFailure : Configuration.Failure → Result
    startupFailure : (configurationValue : Config.Config) → S.Failure configurationValue → Result
    connected : (configurationValue : Config.Config) → S.Service configurationValue → Result

  data Receipt (migrations : M.Inputs) : Result → Set where
    badConfig : ∀ events failure → Configuration.P.Runs (C.load path) events (inj₁ failure) →
      Receipt migrations (configurationFailure failure)
    badService : ∀ configurationEvents configurationValue startupEvents failure →
      Configuration.P.Runs (C.load path) configurationEvents (inj₂ configurationValue) →
      S.Trace configurationValue (S.start configurationValue migrations) startupEvents (S.failed {configurationValue = configurationValue} failure) →
      Receipt migrations (startupFailure configurationValue failure)
    ready : ∀ configurationEvents configurationValue startupEvents service →
      Configuration.P.Runs (C.load path) configurationEvents (inj₂ configurationValue) →
      S.Trace configurationValue (S.start configurationValue migrations) startupEvents (S.ready {configurationValue = configurationValue} service) →
      Receipt migrations (connected configurationValue service)

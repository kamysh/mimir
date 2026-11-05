{-# OPTIONS --safe #-}
-- Executable process ordering: arguments, core configuration, migrations and
-- database connection, then the sequential MCP application loop. Judge/LLM
-- configuration is deliberately absent from this startup path.
module Mimir.McpServiceProcess where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.Startup as Arguments
import Mimir.ConfigurationPath as Path
import Mimir.ConfigurationSchema as Config
import Mimir.ConfigurationProtocol as Configuration
import Mimir.ConnectionProtocol as Connection
import Mimir.ServiceStartup as Startup
import Mimir.MigrationRuntime as Migration
import Mimir.ApplicationProtocol as Application
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
import Mimir.McpRuntimeComposition as Runtime
import Mimir.ServiceConnection as CoreConnection

module Process (sizeMaximum : ℕ) (configurationPath : Path.Path)
  (connectionEnvironment : Connection.Environment) (decimalPort : ℕ → Text)
  (certificateBlocks : Text → List Text) (unix : Bool)
  (environment : Application.Environment) (format : Encoding.Formatting) (conversion : Conversion.Contract)
  where
  module C = Configuration.Run sizeMaximum
  module S config = Startup.Run (Config.Config.core config) connectionEnvironment decimalPort certificateBlocks unix
  module M = Migration.Runtime Text Text
  module R = Runtime.Run environment format conversion

  module WithDiagnostic (render : R.C.H.Diagnostic → Text) where
    module Loop = R.WithDiagnostic render

    data Exit : Set where
      help version usage : Exit
      configurationFailure : Configuration.Failure → Exit
      serviceFailure : (config : Config.Config) → S.Failure config → Exit
      runtimeExit : R.R.Exit → Exit

    data State : Set where
      unstarted : List Arguments.Argument → State
      loading : Configuration.P.Script (Configuration.Failure Data.Sum.⊎ Config.Config) → State
      starting : (config : Config.Config) → S.State config → State
      serving : (config : Config.Config) → S.Service config → R.R.State → State
      exited : Exit → State

    data Event : Set where
      arguments configurationReturned serviceReturned : Event
      configuration : Configuration.P.Event → Event
      service : (config : Config.Config) → S.Event config → Event
      exchange : Loop.Event → Event

    begin : List Arguments.Argument → State
    begin args with Arguments.classify args
    ... | Arguments.showHelp = exited help
    ... | Arguments.showVersion = exited version
    ... | Arguments.reject = exited usage
    ... | Arguments.serve = loading (C.load configurationPath)

    data Step (migrations : M.Inputs) : State → Event → State → Set where
      classified : ∀ args → Step migrations (unstarted args) arguments (begin args)
      configured : ∀ effect continuation reply →
        Step migrations (loading (Configuration.P.ask effect continuation)) (configuration (effect , reply)) (loading (continuation reply))
      invalid : ∀ failure → Step migrations (loading (Configuration.P.done (inj₁ failure))) configurationReturned (exited (configurationFailure failure))
      loaded : ∀ config → Step migrations (loading (Configuration.P.done (inj₂ config))) configurationReturned (starting config (S.start config migrations))
      startup : ∀ config before event after → S.Step config before event after →
        Step migrations (starting config before) (service config event) (starting config after)
      failed : ∀ config failure → Step migrations (starting config (S.failed {config = config} failure)) serviceReturned (exited (serviceFailure config failure))
      ready : ∀ config service → CoreConnection.Compatible (Config.Config.core config) environment →
        Step migrations (starting config (S.ready {config = config} service)) serviceReturned (serving config service R.R.reading)
      request : ∀ config service before event after → Loop.Step before event after →
        Step migrations (serving config service before) (exchange event) (serving config service after)
      finished : ∀ config service reason → Step migrations (serving config service (R.R.exited reason)) serviceReturned (exited (runtimeExit reason))

    data Trace (migrations : M.Inputs) : State → List Event → State → Set where
      empty : ∀ state → Trace migrations state [] state
      more : ∀ {before event middle events after} → Step migrations before event middle →
        Trace migrations middle events after → Trace migrations before (event ∷ events) after

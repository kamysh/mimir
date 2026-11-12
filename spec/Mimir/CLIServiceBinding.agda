{-# OPTIONS --safe #-}
-- CLI and optional hooks use the same core startup and application operations
-- as MCP. Formatting/terminal I/O are dependency operations, not DB queries.
module Mimir.CLIServiceBinding where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Mimir.Text using (Text)
import Mimir.CLI as CLI
import Mimir.HookProtocol as Hook
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationStore as Store
import Mimir.PublicEncoding as Encoding
import Mimir.ConfigurationSchema as Config
import Mimir.ConfigurationPath as Path
import Mimir.ConnectionProtocol as Connection
import Mimir.ServiceConnection as Service
import Mimir.MigrationRuntime as Migration
import Mimir.StandardLibrary as Library

module Bound (conversion : Library.Contract) (environment : Application.Environment) (format : Encoding.Formatting)
  (sizeMaximum : ℕ) (path : Path.Path) (connectionEnvironment : Connection.Environment)
  (decimalPort : ℕ → Text) (certificateBlocks : Text → List Text) (unix : Bool) where
  module C = CLI.Run conversion environment format
  private
    module S = Service.Bound sizeMaximum path connectionEnvironment decimalPort certificateBlocks unix
    module M = Migration.Runtime Text Text
    module H = Hook.Run environment
      using (Effect; module P; Reply; connect; currentDirectory; execute; gitTopLevel; parseJSON;
             readSessionFile; sessionEnvironment; stderr; stdinUTF8; stdout; writeSessionFile)
    module A = Application.Run environment using (GuardedRuns; start)

  -- Error display is an ordinary anyhow/terminal boundary. It does not turn
  -- a configuration or startup failure into a successful connection receipt.
  data Connected (migrations : M.Inputs) : C.Reply C.connect → Set where
    configFailed : ∀ failure detail → S.Receipt migrations (S.configurationFailure failure) → Connected migrations (inj₁ detail)
    serviceFailed : ∀ config failure detail → S.Receipt migrations (S.startupFailure config failure) → Connected migrations (inj₁ detail)
    ready : ∀ config service → S.Receipt migrations (S.connected config service) →
      Service.Compatible (Config.Config.core config) environment → Connected migrations (inj₂ tt)

  data Receipt (migrations : M.Inputs) : (effect : C.Effect) → C.Reply effect → Store.World → Store.World → Set where
    connected : ∀ reply world → Connected migrations reply → Receipt migrations C.connect reply world world
    executed : ∀ request before after events reply → A.GuardedRuns (A.start request) before events after reply →
      Receipt migrations (C.execute request) reply before after
    printed : ∀ line reply world → Receipt migrations (C.print line) reply world world

  data Runs (migrations : M.Inputs) : C.P.Script (C.Failure Data.Sum.⊎ Data.Unit.⊤) →
    Store.World → List C.P.Event → Store.World → C.Failure Data.Sum.⊎ Data.Unit.⊤ → Set where
    returned : ∀ value world → Runs migrations (C.P.done value) world [] world value
    replied : ∀ effect next reply before middle events after value → Receipt migrations effect reply before middle →
      Runs migrations (next reply) middle events after value →
      Runs migrations (C.P.ask effect next) before ((effect , reply) ∷ events) after value

  -- HookProtocol already models all error suppression and Stop's explicit
  -- exit 2. Its connect effect has the same startup obligation.
  data HookReceipt (migrations : M.Inputs) : (effect : H.Effect) → H.Reply effect → Store.World → Store.World → Set where
    connected : ∀ reply world → Connected migrations reply → HookReceipt migrations H.connect reply world world
    executed : ∀ request before after events reply → A.GuardedRuns (A.start request) before events after reply →
      HookReceipt migrations (H.execute request) reply before after
    stdin : ∀ reply world → HookReceipt migrations H.stdinUTF8 reply world world
    json : ∀ input reply world → HookReceipt migrations (H.parseJSON input) reply world world
    sessionEnvironment : ∀ reply world → HookReceipt migrations H.sessionEnvironment reply world world
    read : ∀ path reply world → HookReceipt migrations (H.readSessionFile path) reply world world
    write : ∀ path value reply world → HookReceipt migrations (H.writeSessionFile path value) reply world world
    git : ∀ reply world → HookReceipt migrations H.gitTopLevel reply world world
    cwd : ∀ reply world → HookReceipt migrations H.currentDirectory reply world world
    stdout : ∀ message reply world → HookReceipt migrations (H.stdout message) reply world world
    stderr : ∀ message reply world → HookReceipt migrations (H.stderr message) reply world world

  data HookRuns (migrations : M.Inputs) : H.P.Script ℕ → Store.World → List H.P.Event → Store.World → ℕ → Set where
    returned : ∀ value world → HookRuns migrations (H.P.done value) world [] world value
    replied : ∀ effect next reply before middle events after value → HookReceipt migrations effect reply before middle →
      HookRuns migrations (next reply) middle events after value →
      HookRuns migrations (H.P.ask effect next) before ((effect , reply) ∷ events) after value

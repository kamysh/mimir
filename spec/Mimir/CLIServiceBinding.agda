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
    module A = Application.Run environment

  -- Error display is an ordinary anyhow/terminal boundary. It does not turn
  -- a configuration or startup failure into a successful connection receipt.
  data Connected (migrations : M.Inputs) : C.Reply C.connect → Set where
    configFailed : ∀ failure detail → S.Receipt migrations (S.configurationFailure failure) → Connected migrations (inj₁ detail)
    serviceFailed : ∀ config failure detail → S.Receipt migrations (S.startupFailure config failure) → Connected migrations (inj₁ detail)
    ready : ∀ config service → S.Receipt migrations (S.connected config service) →
      Service.Compatible (Config.Config.core config) environment → Connected migrations (inj₂ tt)

  data Receipt (migrations : M.Inputs) : (effect : C.Effect) → C.Reply effect → Set where
    connected : ∀ reply → Connected migrations reply → Receipt migrations C.connect reply
    executed : ∀ request events reply → A.Runs (A.start request) events reply → Receipt migrations (C.execute request) reply
    printed : ∀ line reply → Receipt migrations (C.print line) reply

  data Runs (migrations : M.Inputs) : C.P.Script (C.Failure Data.Sum.⊎ Data.Unit.⊤) →
    List C.P.Event → C.Failure Data.Sum.⊎ Data.Unit.⊤ → Set where
    returned : ∀ value → Runs migrations (C.P.done value) [] value
    replied : ∀ effect next reply events value → Receipt migrations effect reply →
      Runs migrations (next reply) events value → Runs migrations (C.P.ask effect next) ((effect , reply) ∷ events) value

  -- HookProtocol already models all error suppression and Stop's explicit
  -- exit 2. Its connect effect has the same startup obligation.
  data HookReceipt (migrations : M.Inputs) : (effect : H.Effect) → H.Reply effect → Set where
    connected : ∀ reply → Connected migrations reply → HookReceipt migrations H.connect reply
    executed : ∀ request events reply → A.Runs (A.start request) events reply → HookReceipt migrations (H.execute request) reply
    stdin : ∀ reply → HookReceipt migrations H.stdinUTF8 reply
    json : ∀ input reply → HookReceipt migrations (H.parseJSON input) reply
    sessionEnvironment : ∀ reply → HookReceipt migrations H.sessionEnvironment reply
    read : ∀ path reply → HookReceipt migrations (H.readSessionFile path) reply
    write : ∀ path value reply → HookReceipt migrations (H.writeSessionFile path value) reply
    git : ∀ reply → HookReceipt migrations H.gitTopLevel reply
    cwd : ∀ reply → HookReceipt migrations H.currentDirectory reply
    stdout : ∀ message reply → HookReceipt migrations (H.stdout message) reply
    stderr : ∀ message reply → HookReceipt migrations (H.stderr message) reply

  data HookRuns (migrations : M.Inputs) : H.P.Script ℕ → List H.P.Event → ℕ → Set where
    returned : ∀ value → HookRuns migrations (H.P.done value) [] value
    replied : ∀ effect next reply events value → HookReceipt migrations effect reply →
      HookRuns migrations (next reply) events value →
      HookRuns migrations (H.P.ask effect next) ((effect , reply) ∷ events) value

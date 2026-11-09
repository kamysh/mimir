{-# OPTIONS --safe #-}
-- Dedicated CLI run/watch execution. Normal completion uses the existing
-- host/watcher composition; signal completion requires owned-work cleanup.
module Mimir.JudgeCommandExecution where

open import Data.Bool using (Bool; false)
open import Data.List using (List; _∷_)
open import Data.Maybe using (Maybe; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
import Mimir.CLI as CLI
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.ApplicationProtocol as Application
import Mimir.JudgeConfiguration as Config
import Mimir.JudgeHarnessAdapter as Harness
import Mimir.JudgeServiceBinding as Service
import Mimir.JudgeHostProtocol as HostProtocol
import Mimir.JudgeHost as Host
import Mimir.JudgeDigest as Digest
import Mimir.JudgeDigestComposition as Watch
import Mimir.JudgeOwnedWork as Owned
import Mimir.JudgeSignal as Signal
import Mimir.JudgeSignalBinding as SignalBinding
import Mimir.UUIDV4 as UUID
import Mimir.UnixPath as Path
import Mimir.UnixMetadata as Metadata
import Mimir.NotificationCodec as Codec
import Mimir.NotificationDelivery as Delivery
import Mimir.SMTPProtocol as SMTP
import Mimir.ConnectionProtocol as Connection
import Mimir.ConfigurationPath as Arguments

nativePath : Conversion.Contract → Arguments.Path → Path.Path
nativePath conversion (Arguments.native bytes) = bytes
nativePath conversion (Arguments.utf8 text) = Conversion.Contract.encodeUTF8 conversion text
nativePath conversion (Arguments.join base suffix) = Path.join (nativePath conversion base)
  (Conversion.Contract.encodeUTF8 conversion suffix)

module Bound (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (libraries : Harness.Libraries) (configLibraries : Config.Libraries)
  (environment : Application.Environment) (errors : Service.Display)
  (sizeMaximum contract model : ℕ) (unix : Bool) (owner : Metadata.UserId)
  (explicitConfig : Maybe Arguments.Path) (defaultConfig : Path.Path) (explicitState : Maybe Arguments.Path)
  (localTime : ℕ → Text) (clockMaximum : ℕ) (endian : UUID.Endian)
  (json : Codec.JSONLibrary) (buildMessage : SMTP.Message → Delivery.BuildReceipt)
  (connectionEnvironment : Connection.Environment) (decimalPort : ℕ → Text)
  (certificateBlocks : Text → List Text) (calendar : Digest.Calendar) where
  private
    module O = Owned.Bound conversion format libraries
    module H = HostProtocol.Run conversion format libraries configLibraries environment errors sizeMaximum contract model
      unix owner (map (nativePath conversion) explicitConfig) defaultConfig (map (nativePath conversion) explicitState)
      localTime clockMaximum endian json buildMessage
    module W = Watch.Bound conversion format libraries configLibraries environment errors sizeMaximum contract model
      unix owner (map (nativePath conversion) explicitConfig) defaultConfig (map (nativePath conversion) explicitState)
      localTime clockMaximum endian json buildMessage
      connectionEnvironment decimalPort certificateBlocks calendar

  data Completion : CLI.JudgeCommand → O.Work → ℕ → Set where
    once : ∀ initial events result → H.Runs (H.once false) events result →
      Completion (CLI.run explicitConfig explicitState) initial (Host.code (Host.Outcome.exit result))
    watched : ∀ initial migrations exit →
      W.Trace migrations Host.startWatch (Host.exited exit) →
      Completion (CLI.watch explicitConfig explicitState) initial (Host.code exit)

  module Stop command = SignalBinding.Bound conversion format libraries (Completion command)

  data Cancellable : CLI.JudgeCommand → Set where
    run : Cancellable (CLI.run explicitConfig explicitState)
    watch : Cancellable (CLI.watch explicitConfig explicitState)

  program : ∀ command → Cancellable command → (initial : O.Work) → Stop.Initial command initial → Stop.S.Script command ℕ
  program command admitted initial unpolled = Stop.run command initial unpolled

  stopRequiresCleanup : ∀ command admitted initial unpolled current signal rest code →
    Stop.Runs command (program command admitted initial unpolled)
      ((Stop.S.installListeners {command = command} , inj₂ tt) ∷
       (Stop.S.awaitRace {command = command} initial , Signal.stopped signal current) ∷ rest) code →
    O.Work.future initial ≡ O.Work.future current × (Stop.Cleaned command current × code ≡ 0)
  stopRequiresCleanup command admitted initial unpolled current signal rest code =
    Stop.fullStopCleansCurrent command initial unpolled current signal rest code

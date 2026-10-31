{-# OPTIONS --safe #-}
-- Daily/watch integration: actual validated configuration, notifier cursor,
-- core database startup, one read-only snapshot, delivery, and loop control.
module Mimir.JudgeDigestComposition where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
import Mimir.JudgeHost as Host
import Mimir.JudgeHostProtocol as HostProtocol
import Mimir.JudgeDigest as Digest
import Mimir.JudgeDigestSnapshot as Snapshot
import Mimir.JudgeConfiguration as Config
import Mimir.JudgeStatePath as StatePath
import Mimir.JudgeHarnessAdapter as Harness
import Mimir.JudgeServiceBinding as Service
import Mimir.ApplicationProtocol as Application
import Mimir.PublicEncoding as Encoding
import Mimir.FloatConversion as Conversion
import Mimir.NotificationConfig as Email
import Mimir.NotificationComposition as Notification
import Mimir.NotificationRuntime as N
import Mimir.NotificationIncident as Incident
import Mimir.NotificationDelivery as Delivery
import Mimir.NotificationCodec as Codec
import Mimir.DigestDelivery as Daily
import Mimir.SMTPProtocol as SMTP
import Mimir.ServiceStartup as Startup
import Mimir.ConnectionProtocol as Connection
import Mimir.ConfigurationSchema as Core
import Mimir.MigrationRuntime as Migration
import Mimir.UnixPath as Path
import Mimir.UnixMetadata as Metadata
import Mimir.UUIDV4 as UUID
import Mimir.Effects as Effects

digestResult : Daily.Result → Text ⊎ Incident.Outcome
digestResult Daily.disabled = inj₂ Incident.disabled
digestResult Daily.notNeeded = inj₂ Incident.notNeeded
digestResult Daily.retryPending = inj₂ Incident.retryPending
digestResult Daily.sent = inj₂ Incident.sent
digestResult Daily.invalidDigest = inj₁ (toList "invalid digest")
digestResult Daily.invalidMessage = inj₁ (toList "invalid digest message")
digestResult Daily.storageFailed = inj₁ (toList "digest storage failure")

module Bound (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (libraries : Harness.Libraries) (configLibraries : Config.Libraries)
  (environment : Application.Environment) (errors : Service.Display)
  (sizeMaximum contract model : ℕ) (unix : Bool) (owner : Metadata.UserId)
  (explicitConfig : Maybe Path.Path) (defaultConfig : Path.Path) (explicitState : Maybe Path.Path)
  (localTime : ℕ → Text) (clockMaximum : ℕ) (endian : UUID.Endian)
  (json : Codec.JSONLibrary) (buildMessage : SMTP.Message → Delivery.BuildReceipt)
  (connectionEnvironment : Connection.Environment) (decimalPort : ℕ → Text)
  (certificateBlocks : Text → List Text) (calendar : Digest.Calendar) where
  private
    module H = HostProtocol.Run conversion format libraries configLibraries environment errors sizeMaximum contract model
      unix owner explicitConfig defaultConfig explicitState localTime clockMaximum endian json buildMessage
    module C = Config.Load conversion sizeMaximum configLibraries unix owner
    module S settings = Startup.Run (Core.Config.core (Config.Runtime.core settings)) connectionEnvironment decimalPort certificateBlocks unix
    module M = Migration.Runtime Text Text
    module Notify service = Notification.Bound conversion json buildMessage sizeMaximum clockMaximum endian service

  configResult : C.Result → Text ⊎ Config.Runtime
  configResult (inj₁ detail) = inj₁ detail
  configResult (inj₂ loaded) = inj₂ (Config.Validate.Admitted.settings (C.Loaded.configuration loaded))
  pathResult : H.SP.Result → Text ⊎ Path.Path
  pathResult (inj₁ error) = inj₁ (toList "invalid notification state path")
  pathResult (inj₂ path) = inj₂ (StatePath.Resolved.path path)
  cursorResult : N.Error ⊎ Daily.Cursor → Text ⊎ Daily.Cursor
  cursorResult (inj₁ error) = inj₁ (toList "notification cursor unavailable")
  cursorResult (inj₂ cursor) = inj₂ cursor

  data State : Set where idle : State; connected : ℕ → Snapshot.State → State

  data Receipt (migrations : M.Inputs) : State → (effect : Digest.Effect) → Digest.Reply effect → State → Set where
    -- The read uses the existing bounded status-file decoder; unavailable
    -- or absent state yields no report and an explicit diagnostic action.
    reportRead : ∀ state path report → Receipt migrations state (Digest.readReport path) report state
    clock : ∀ state now → Receipt migrations state Digest.localNow now state
    configured : ∀ state reply → H.Receipt H.loadConfig reply → Receipt migrations state Digest.loadConfig (configResult reply) state
    path : ∀ state reply → H.Receipt H.resolveState reply → Receipt migrations state Digest.resolveState (pathResult reply) state
    cursorConstructorFailed : ∀ state cfg path detail → Notification.new cfg path ≡ inj₁ detail →
      Receipt migrations state (Digest.readCursor cfg path) (inj₁ detail) state
    cursorRead : ∀ state cfg path service events reply → Notification.new cfg path ≡ inj₂ service →
      Notify.Runs service (Notify.unlocked {service = service}) (Notification.API.cursor service clockMaximum)
        events (Notify.unlocked {service = service}) reply →
      Receipt migrations state (Digest.readCursor cfg path) (cursorResult reply) state
    connectionFailed : ∀ settings events failure detail →
      S.Trace settings (S.start settings migrations) events (S.failed {settings = settings} failure) →
      Receipt migrations idle (Digest.connect settings) (inj₁ detail) idle
    connectionReady : ∀ settings events service id →
      S.Trace settings (S.start settings migrations) events (S.ready {settings = settings} service) →
      Receipt migrations idle (Digest.connect settings) (inj₂ id) (connected id Snapshot.idle)
    database : ∀ id before effect reply after → Snapshot.Step id before (effect , reply) after →
      Receipt migrations (connected id before) effect reply (connected id after)
    closed : ∀ id before → Receipt migrations (connected id before) (Digest.close id) tt idle
    sendConstructorFailed : ∀ state settings path value detail →
      Notification.new (Config.Runtime.email settings) path ≡ inj₁ detail →
      Receipt migrations state (Digest.send settings path value) (inj₁ detail) state
    sent : ∀ state settings path value service events result →
      Notification.new (Config.Runtime.email settings) path ≡ inj₂ service →
      Notify.Runs service (Notify.unlocked {service = service}) (Notification.API.sendDigest service clockMaximum value)
        events (Notify.unlocked {service = service}) result →
      Receipt migrations state (Digest.send settings path value) (digestResult result) state

  data Runs (migrations : M.Inputs) : State → Digest.Script (Text ⊎ Bool) → List Digest.Event → State → Text ⊎ Bool → Set where
    returned : ∀ state value → Runs migrations state (Digest.done value) [] state value
    replied : ∀ before effect next reply middle events after value → Receipt migrations before effect reply middle →
      Runs migrations middle (next reply) events after value →
      Runs migrations before (Digest.ask effect next) ((effect , reply) ∷ events) after value

  -- Standard stderr writes and Tokio's timer/signal selection are external.
  -- Completion of ctrl_c(), including its registration error, takes the signal
  -- branch in the native select. SIGINT is polled at this waiting phase.
  data Waited (seconds : ℕ) (messages : List Host.Transition) : Bool → Set where
    timer : Waited seconds messages false
    signal : Waited seconds messages true

  data Step (migrations : M.Inputs) (interval threshold : ℕ) : Host.Phase → Host.Phase → Set where
    batch : ∀ state events result → H.Runs (H.once true) events result →
      Step migrations interval threshold (Host.running state) (Host.digest state result)
    digest : ∀ state outcome events result → Runs migrations idle (Digest.Run.tick calendar outcome) events idle result →
      Step migrations interval threshold (Host.digest state outcome)
        (Host.step sizeMaximum interval threshold (Host.digest state outcome) result)
    waited : ∀ state seconds messages result → Waited seconds messages result →
      Step migrations interval threshold (Host.waiting state seconds messages)
        (Host.step sizeMaximum interval threshold (Host.waiting state seconds messages) result)

  data Trace (migrations : M.Inputs) (interval threshold : ℕ) : Host.Phase → Host.Phase → Set where
    empty : ∀ phase → Trace migrations interval threshold phase phase
    more : ∀ before middle after → Step migrations interval threshold before middle →
      Trace migrations interval threshold middle after → Trace migrations interval threshold before after

{-# OPTIONS --safe #-}
-- Run/check-config host control. Configuration, path resolution and lock
-- outcomes are distinct. Invalid configuration persistence is best effort;
-- ordinary runs retain the lock through finalization and output.
module Mimir.JudgeHostProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Mimir.Text using (Text)
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.ApplicationProtocol as Application
import Mimir.JudgeConfiguration as Config
import Mimir.JudgeConfigurationComposition as ConfigComposition
import Mimir.JudgeHarnessAdapter as Harness
import Mimir.JudgeAPIAdapter as API
import Mimir.JudgeBackendComposition as Backend
import Mimir.JudgeServiceBinding as Service
import Mimir.JudgeWorkflowComposition as Workflow
import Mimir.JudgeFinalization as Finalization
import Mimir.JudgeFinalizationComposition as FinalizationComposition
import Mimir.JudgeStateOperations as StateOperations
import Mimir.UUIDV4 as UUID
import Mimir.JudgeHost as Host
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeStatePath as StatePath
import Mimir.JudgePersistence as Persistence
import Mimir.JudgeLock as Lock
import Mimir.UnixPath as Path
import Mimir.UnixMetadata as Metadata
import Mimir.Effects as Effects
import Mimir.JudgeMcpLifecycle as Client
import Mimir.NotificationCodec as Codec
import Mimir.NotificationDelivery as Delivery
import Mimir.SMTPProtocol as SMTP
import Mimir.OperationalLifecycle as Operational
import Mimir.OperationalLogProtocol as OperationalLog
import Mimir.ConfigurationSchema as Core
import Mimir.ConfigurationValues as Values

module R = Records.Over ℕ

data Output : Set where
  valid invalidStatePath alreadyRunning stateUnavailable : Output
  invalidConfig : Text → Output
  logUnavailable : Text → Output
  reportOutput : R.Report → Output

module Run (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (libraries : Harness.Libraries) (configLibraries : Config.Libraries)
  (environment : Application.Environment) (errors : Service.Display)
  (sizeMaximum contract model : ℕ) (unix : Bool) (owner : Metadata.UserId)
  (explicitConfig : Maybe Path.Path) (defaultConfig : Path.Path) (explicitState : Maybe Path.Path)
  (localTime : ℕ → Text) (clockMaximum : ℕ) (endian : UUID.Endian)
  (json : Codec.JSONLibrary) (buildMessage : SMTP.Message → Delivery.BuildReceipt) where
  module C = Config.Load conversion sizeMaximum configLibraries unix owner
  module CC = ConfigComposition.Compose conversion sizeMaximum configLibraries unix owner
  module SP = StatePath.With Text
  module FS = Persistence.With ℕ Text
  module L = Lock.With Path.Path ℕ Text
  notificationMode : Bool → Finalization.NotificationMode
  notificationMode true = Finalization.queuedDelivery
  notificationMode false = Finalization.inlineDelivery

  module W (watch : Bool) (settings : Config.Runtime) program path configPath = Workflow.Compose conversion format libraries environment errors
    (Config.Runtime.llm settings) program contract model (Config.Judge.batchSize (Config.Runtime.judge settings))
    (Config.Judge.project (Config.Runtime.judge settings))
    (Config.Judge.mcpCommand (Config.Runtime.judge settings)) (Config.Judge.mcpArgs (Config.Runtime.judge settings)) configPath
    (Config.Runtime.email settings) localTime sizeMaximum clockMaximum endian path json buildMessage (notificationMode watch)
  module S path = StateOperations.Bound conversion sizeMaximum endian path
  module F (settings : Config.Runtime) path = FinalizationComposition.Bound conversion format localTime
    sizeMaximum clockMaximum endian path (Config.Runtime.email settings)
    (Config.Judge.project (Config.Runtime.judge settings)) json buildMessage

  data Built (config : Config.Llm) : Text → Backend.BackendState → Set where
    harness : ∀ program → Harness.construct config ≡ inj₂ program → Built config program (Backend.harness Harness.initial)
    api : ∀ events ready → Config.Llm.backend config ≡ Config.api →
      API.Construction.P.Runs config (API.Construction.start config) events (inj₂ (just ready)) →
      Built config [] (Backend.api (API.Construction.Ready.provider ready) API.initial)
    unavailable : ∀ events → Config.Llm.backend config ≡ Config.api →
      API.Construction.P.Runs config (API.Construction.start config) events (inj₂ nothing) →
      Built config [] Backend.unavailable

  data BuildFailed (config : Config.Llm) (detail : Text) : Set where
    harness : Config.Llm.backend config ≢ Config.api → Harness.construct config ≡ inj₁ detail → BuildFailed config detail
    api : ∀ events → Config.Llm.backend config ≡ Config.api →
      API.Construction.P.Runs config (API.Construction.start config) events (inj₁ detail) → BuildFailed config detail

  setupReport : Maybe ℕ → Text → R.Report
  setupReport now detail = record (R.newReport now (toList "blocked") 0 0 0 0 0)
    { blockReason = just (toList "backend_configuration") ; failureDetail = just detail }

  data Dropped : Maybe Client.Client → Set where
    absent : Dropped nothing
    released : ∀ client events → Client.Runs (Client.dropClient client) events tt → Dropped (just client)

  coreOf : C.Loaded → Core.Config
  coreOf loadedConfiguration = Config.Runtime.core
    (Config.Validate.Admitted.settings (C.Loaded.configuration loadedConfiguration))

  -- A connected child uses a private configuration read back through the
  -- existing loader. A mutable filename alone cannot provide this receipt.
  record PreparedMcpConfig (settings : Config.Runtime) (original : Path.Path) : Set where
    field path : Path.Path
          separate : path ≢ original
          observed : C.Loaded
          events : List C.P.Event
          readback : CC.Runs (C.start (just path) defaultConfig) events (inj₂ observed)
          selected : coreOf observed ≡ Config.Runtime.core settings

  snapshotDatabaseMatches : ∀ settings original (snapshot : PreparedMcpConfig settings original) →
    Values.Config.db (Core.Config.core (coreOf (PreparedMcpConfig.observed snapshot))) ≡
    Values.Config.db (Core.Config.core (Config.Runtime.core settings))
  snapshotDatabaseMatches settings original snapshot = cong (λ core → Values.Config.db (Core.Config.core core))
    (PreparedMcpConfig.selected snapshot)

  module Preparation (settings : Config.Runtime) (original directory : Path.Path) where
    data Effect : Set where preparePrivateConfig : Effect
    Reply : Effect → Set
    Reply preparePrivateConfig = Text ⊎ PreparedMcpConfig settings original
    module P = Effects.Protocol Effect Reply
    open P public
    start : Script (Text ⊎ PreparedMcpConfig settings original)
    start = ask preparePrivateConfig done

  preparationReport : Maybe ℕ → Text → R.Report
  preparationReport now detail = record (setupReport now detail)
    { blockReason = just (toList "mcp_or_configuration_error") }

  data Executed (watch : Bool) (settings : Config.Runtime) (held : L.Locked) (configPath : Path.Path) : R.Report → Set where
    completed : ∀ program before after events client report (snapshot : PreparedMcpConfig settings configPath)
      preparationEvents →
      Preparation.Runs settings configPath (L.Locked.path held)
        (Preparation.start settings configPath (L.Locked.path held)) preparationEvents (inj₂ snapshot) →
      Built (Config.Runtime.llm settings) program before →
      W.Runs watch settings program (L.Locked.path held) (PreparedMcpConfig.path snapshot) before nothing
        (W.W.start watch settings program (L.Locked.path held) (PreparedMcpConfig.path snapshot)) events after client report →
      Dropped client → Executed watch settings held configPath report
    -- No MCP execution is admitted on this branch. The existing watcher/caller
    -- owns retry after the private state/configuration problem is corrected.
    preparationFailure : ∀ detail observed preparationEvents events report →
      Preparation.Runs settings configPath (L.Locked.path held)
        (Preparation.start settings configPath (L.Locked.path held)) preparationEvents (inj₁ detail) →
      F.Runs settings (L.Locked.path held) (Finalization.finishWith (notificationMode watch) (preparationReport observed detail)) events report →
      Executed watch settings held configPath report
    setupFailure : ∀ detail observed events report → BuildFailed (Config.Runtime.llm settings) detail →
      F.Runs settings (L.Locked.path held) (Finalization.finishWith (notificationMode watch) (setupReport observed detail)) events report → Executed watch settings held configPath report

  data Effect : Set where
    loadConfig resolveState clock : Effect
    prepareLog : C.Loaded → Effect
    acquire : Path.Path → Effect
    release : L.Locked → Effect
    execute : Bool → Config.Runtime → L.Locked → Path.Path → Effect
    incident status : L.Locked → R.Report → Effect
    stdout : Output → Effect
    configurationDiagnostic : Text → Effect

  Reply : Effect → Set
  Reply loadConfig = C.Result
  Reply (prepareLog loadedConfiguration) = Operational.LogAttempt (coreOf loadedConfiguration)
  Reply resolveState = SP.Result
  Reply clock = Maybe ℕ
  Reply (acquire _) = L.FS.Result (Maybe L.Locked)
  Reply (release _) = ⊤
  Reply (execute watch settings held configPath) = R.Report
  Reply (incident held report) = Text ⊎ ⊤
  Reply (status held report) = Text ⊎ ⊤
  Reply (stdout _) = ⊤
  Reply (configurationDiagnostic _) = ⊤
  module P = Effects.Protocol Effect Reply
  open P using (Script; done; ask; _>>=_)

  invalidReport : Maybe ℕ → Text → R.Report
  invalidReport observed detail = record (R.newReport observed (toList "blocked") 0 0 0 0 0)
    { blockReason = just (toList "invalid_config") ; failureDetail = just detail }

  persistInvalid : Text → Script ⊤
  persistInvalid detail = ask resolveState λ where
    (inj₁ _) → done tt
    (inj₂ resolvedPaths) → ask (acquire (StatePath.Resolved.path resolvedPaths)) λ where
      (inj₁ _) → done tt
      (inj₂ nothing) → done tt
      (inj₂ (just held)) → ask clock (λ observed →
        ask (incident held (invalidReport observed detail)) (λ _ →
          ask (status held (invalidReport observed detail)) (λ _ → ask (release held) done)))

  emit : Bool → Output → Script ⊤
  emit true output = done tt
  emit false output = ask (stdout output) done

  failed : Bool → Output → Host.Exit → Script Host.Outcome
  failed watch output code = emit watch output >>= λ _ → done (Host.outcome code true false)

  afterLock : Bool → C.Loaded → Reply (acquire []) → Script Host.Outcome
  afterLock watch loadedConfiguration (inj₁ _) = failed watch stateUnavailable Host.unavailable
  afterLock watch loadedConfiguration (inj₂ nothing) = failed watch alreadyRunning Host.alreadyRunning
  afterLock watch loadedConfiguration (inj₂ (just held)) = ask (execute watch settings held (C.Loaded.path loadedConfiguration)) (λ result →
    emit watch (reportOutput result) >>= λ _ → ask (release held) (λ _ → done (Host.outcomeOf watch result)))
    where settings = Config.Validate.Admitted.settings (C.Loaded.configuration loadedConfiguration)

  afterLog : Bool → (loadedConfiguration : C.Loaded) → Reply (prepareLog loadedConfiguration) → Script Host.Outcome
  afterLog watch loadedConfiguration observed with Operational.LogAttempt.outcome observed
  ... | OperationalLog.For.failed detail files = failed watch (logUnavailable detail) Host.unavailable
  ... | OperationalLog.For.written files = ask resolveState λ where
    (inj₁ _) → failed watch invalidStatePath Host.invalidConfig
    (inj₂ resolvedPaths) → ask (acquire (StatePath.Resolved.path resolvedPaths)) (afterLock watch loadedConfiguration)

  logFailureStops : ∀ watch loadedConfiguration observed detail files →
    Operational.LogAttempt.outcome observed ≡ Operational.LogAt.failed
      {coreOf loadedConfiguration} detail files →
    afterLog watch loadedConfiguration observed ≡ failed watch (logUnavailable detail) Host.unavailable
  logFailureStops watch loadedConfiguration observed detail files failure rewrite failure = refl

  logFailureEvents : ∀ watch loadedConfiguration observed detail files events result →
    Operational.LogAttempt.outcome observed ≡ Operational.LogAt.failed
      {coreOf loadedConfiguration} detail files →
    P.Runs (afterLog watch loadedConfiguration observed) events result →
    (events ≡ []) ⊎ (events ≡ ((stdout (logUnavailable detail) , tt) ∷ []))
  logFailureEvents true loadedConfiguration observed detail files events result failure execution
    rewrite logFailureStops true loadedConfiguration observed detail files failure with execution
  ... | P.returned _ = inj₁ refl
  logFailureEvents false loadedConfiguration observed detail files events result failure execution
    rewrite logFailureStops false loadedConfiguration observed detail files failure with execution
  ... | P.replied _ _ tt (P.returned _) = inj₂ refl

  afterConfig : Bool → C.Result → Script Host.Outcome
  afterConfig watch (inj₁ detail) = persistInvalid detail >>= λ _ → announce watch
    where
    announce : Bool → Script Host.Outcome
    announce true = done (Host.outcome Host.invalidConfig true false)
    announce false = ask (configurationDiagnostic detail) (λ _ → failed false (invalidConfig detail) Host.invalidConfig)
  afterConfig watch (inj₂ loadedConfiguration) = ask (prepareLog loadedConfiguration) (afterLog watch loadedConfiguration)

  once : Bool → Script Host.Outcome
  once watch = ask loadConfig (afterConfig watch)

  checkConfig : Script ℕ
  checkConfig = ask loadConfig λ where
    (inj₂ _) → ask (stdout valid) (λ _ → done 0)
    (inj₁ detail) → ask (configurationDiagnostic detail) (λ _ → ask (stdout (invalidConfig detail)) (λ _ → done 2))

  data Receipt : (effect : Effect) → Reply effect → Set where
    configuration : ∀ events result → CC.Runs (C.start explicitConfig defaultConfig) events result → Receipt loadConfig result
    logging : ∀ loadedConfiguration observed → Receipt (prepareLog loadedConfiguration) observed
    path : ∀ events result → SP.Runs (SP.resolve explicitState) events result → Receipt resolveState result
    locked : ∀ path events result → L.FS.Runs (FS.acquire path) events result → Receipt (acquire path) result
    unlocked : ∀ held events → L.FS.Runs (L.release held) events tt → Receipt (release held) tt
    ran : ∀ watch settings held configPath report → Executed watch settings held configPath report → Receipt (execute watch settings held configPath) report
    observed : ∀ reply → Receipt clock reply
    recorded : ∀ held report reply → S.IncidentExecution (L.Locked.path held) report reply → Receipt (incident held report) reply
    written : ∀ held report reply → S.Written (L.Locked.path held) Persistence.status report reply → Receipt (status held report) reply
    printed : ∀ output → Receipt (stdout output) tt
    diagnostic : ∀ detail → Receipt (configurationDiagnostic detail) tt

  data Runs {A : Set} : Script A → List P.Event → A → Set where
    returned : ∀ result → Runs (done result) [] result
    replied : ∀ effect continuation reply events result → Receipt effect reply → Runs (continuation reply) events result →
      Runs (ask effect continuation) ((effect , reply) ∷ events) result

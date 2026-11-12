{-# OPTIONS --safe #-}
-- Run/check-config host control. Configuration, path resolution and lock
-- outcomes are distinct. Invalid configuration persistence is best effort;
-- ordinary runs retain the lock through finalization and output.
module Mimir.JudgeHostProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationStore as Store
import Mimir.JudgeConfiguration as Config
import Mimir.JudgeConfigurationComposition as ConfigComposition
import Mimir.JudgeRevision as Revision
import Mimir.JudgeBackendComposition as Backend
import Mimir.JudgeServiceBinding as Service
import Mimir.JudgeWorkflowComposition as Workflow
import Mimir.JudgeFinalization as Finalization
import Mimir.JudgeFinalizationComposition as FinalizationComposition
import Mimir.JudgeStateOperations as StateOperations
import Mimir.UUIDGroups as UUIDValue
import Mimir.JudgeHost as Host
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeStatePath as StatePath
import Mimir.JudgePersistence as Persistence
import Mimir.JudgeLock as Lock
import Mimir.UnixPath as Path
import Mimir.UnixMetadata as Metadata
import Mimir.Effects as Effects
import Mimir.JudgeMcpLifecycle as Client
import Mimir.OperationalLifecycle as Operational
import Mimir.OperationalLogProtocol as OperationalLog
import Mimir.ConfigurationSchema as Core

module R = Records.Over UUIDValue.UUID

data Output : Set where
  valid invalidStatePath alreadyRunning stateUnavailable : Output
  invalidConfig : Text → Output
  reportOutput : R.Report → Output

-- Work notifications wake an idle watcher. A blocked watcher resumes on a
-- configuration edit or the already agreed explicit SIGHUP retry signal.
data WorkWake : Set where workAvailable configurationChanged explicitRetry : WorkWake
data RepairWake : Set where configurationChanged explicitRetry : RepairWake
record WorkSubscription : Set where
  constructor workSubscription
  field handle : Text

module Run (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (display : Revision.Display) (configLibraries : Config.Libraries)
  (environment : Application.Environment) (errors : Service.Display)
  (sizeMaximum contract model : ℕ) (unix : Bool) (owner : Metadata.UserId)
  (explicitConfig : Maybe Path.Path) (defaultConfig : Path.Path) (explicitState : Maybe Path.Path)
  where
  module C = Config.Load conversion sizeMaximum configLibraries unix owner
  module CC = ConfigComposition.Compose conversion sizeMaximum configLibraries unix owner
  module SP = StatePath.With Text
  module FS = Persistence.With ℕ Text
  module L = Lock.With Path.Path ℕ Text
  module W (settings : Config.Runtime) configPath = Workflow.Compose conversion format display environment errors
    contract model (Config.Judge.batchSize (Config.Runtime.judge settings))
    (Config.Judge.project (Config.Runtime.judge settings))
    (Config.Judge.mcpCommand (Config.Runtime.judge settings)) (Config.Judge.mcpArgs (Config.Runtime.judge settings)) configPath
    sizeMaximum
  module F = FinalizationComposition.Bound

  data Built (config : Config.Llm) : Text → Backend.BackendState → Set where
    harness : ∀ program → Config.Llm.backend config ≢ Config.api → Built config program Backend.harness
    api : ∀ provider → Config.Llm.backend config ≡ Config.api →
      Config.Llm.provider config ≡ just provider → Built config [] (Backend.api provider)
    unavailable : Config.Llm.backend config ≡ Config.api → Config.Llm.provider config ≡ nothing →
      Built config [] Backend.unavailable

  data BuildFailed (config : Config.Llm) (detail : Text) : Set where
    harness : Config.Llm.backend config ≢ Config.api → BuildFailed config detail
    api : Config.Llm.backend config ≡ Config.api → BuildFailed config detail

  setupReport : Maybe ℕ → Text → R.Report
  setupReport now detail = record (R.newReport now (toList "blocked"))
    { blockReason = just (toList "backend_configuration") ; failureDetail = just detail }

  data Dropped : Maybe Client.Client → Set where
    absent : Dropped nothing
    released : ∀ client events → Client.Runs (Client.dropClient client) events (inj₂ tt) → Dropped (just client)

  data Executed (settings : Config.Runtime) (held : L.Locked) (configPath : Path.Path) : R.Report → Set where
    completed : ∀ program before after events client report → Built (Config.Runtime.llm settings) program before →
      W.Runs settings configPath before nothing (W.W.start settings configPath) events after client report → Dropped client → Executed settings held configPath report
    setupFailure : ∀ detail observed events report → BuildFailed (Config.Runtime.llm settings) detail →
      F.Runs (Finalization.finish (setupReport observed detail) nothing) events report → Executed settings held configPath report

  coreOf : C.Loaded → Core.Config
  coreOf loadedConfiguration = Config.Runtime.core
    (Config.Validate.Admitted.settings (C.Loaded.configuration loadedConfiguration))

  data Effect : Set where
    loadConfig resolveState clock : Effect
    prepareLog : C.Loaded → Effect
    acquire : Path.Path → Effect
    release : L.Locked → Effect
    execute : Config.Runtime → L.Locked → Path.Path → Effect
    incident status : L.Locked → R.Report → Effect
    stdout : Output → Effect
    reportDiagnostic : Text → Effect
    subscribeWork waitForRepair : Effect
    waitForWork dropWorkSubscription : WorkSubscription → Effect

  Reply : Effect → Set
  Reply loadConfig = C.Result
  Reply (prepareLog loadedConfiguration) = Operational.LogAttempt (coreOf loadedConfiguration)
  Reply resolveState = SP.Result
  Reply clock = Maybe ℕ
  Reply (acquire _) = L.FS.Result (Maybe L.Locked)
  Reply (release _) = ⊤
  Reply (execute settings held configPath) = R.Report
  Reply (incident held report) = Text ⊎ ⊤
  Reply (status held report) = Text ⊎ ⊤
  Reply (stdout _) = ⊤
  Reply (reportDiagnostic _) = ⊤
  Reply subscribeWork = Text ⊎ WorkSubscription
  Reply (waitForWork _) = Text ⊎ WorkWake
  Reply (dropWorkSubscription _) = ⊤
  Reply waitForRepair = RepairWake
  module P = Effects.Protocol Effect Reply
  open P using (Script; done; ask; _>>=_)

  invalidReport : Maybe ℕ → Text → R.Report
  invalidReport observed detail = record (R.newReport observed (toList "blocked"))
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

  pathProblem : SP.Error → Text
  pathProblem SP.xdgRelative = toList "XDG_STATE_HOME must be an absolute path. Correct it or select an absolute state directory."
  pathProblem SP.homeUnset = toList "HOME is not set. Set it or select an absolute state directory."
  pathProblem SP.parentComponent = toList "The state directory contains a parent component. Select a path without '..'."
  pathProblem (SP.currentDirectoryFailed detail) =
    toList "Cannot resolve the current directory: " ++ detail ++ toList ". Select an absolute state directory or restore access."

  stateProblem : L.FS.Error → Text
  stateProblem (L.FS.native failure) = toList "Cannot access judge state: " ++ L.FS.IOError.detail failure ++
    toList ". Restore access to the configured state directory and retry."
  stateProblem _ = toList "The judge state directory or lock is not usable. Check its type, ownership, and permissions."

  afterLock : Bool → C.Loaded → Reply (acquire []) → Script Host.Outcome
  afterLock watch loadedConfiguration (inj₁ failure) = ask (reportDiagnostic (stateProblem failure))
    (λ _ → failed watch stateUnavailable Host.unavailable)
  afterLock watch loadedConfiguration (inj₂ nothing) = ask (reportDiagnostic
    (toList "Another judge holds the state lock. Let that judge finish before retrying."))
    (λ _ → failed watch alreadyRunning Host.alreadyRunning)
  afterLock watch loadedConfiguration (inj₂ (just held)) =
    let settings = Config.Validate.Admitted.settings (C.Loaded.configuration loadedConfiguration)
    in ask (execute settings held (C.Loaded.path loadedConfiguration)) (λ result →
      emit watch (reportOutput result) >>= λ _ → ask (release held) (λ _ → done (Host.outcomeOf watch result)))

  afterLogging : Bool → C.Loaded → Script Host.Outcome
  afterLogging watch loadedConfiguration = ask resolveState λ where
    (inj₁ failure) → ask (reportDiagnostic (pathProblem failure))
      (λ _ → failed watch invalidStatePath Host.invalidConfig)
    (inj₂ resolvedPaths) → ask (acquire (StatePath.Resolved.path resolvedPaths)) (afterLock watch loadedConfiguration)

  afterLog : Bool → (loadedConfiguration : C.Loaded) → Reply (prepareLog loadedConfiguration) → Script Host.Outcome
  afterLog watch loadedConfiguration observed with Operational.LogAttempt.outcome observed
  ... | OperationalLog.For.failed detail files = ask (reportDiagnostic detail) (λ _ → afterLogging watch loadedConfiguration)
  ... | OperationalLog.For.written files = afterLogging watch loadedConfiguration

  logFailureContinues : ∀ watch loadedConfiguration observed detail files events result →
    Operational.LogAttempt.outcome observed ≡ Operational.LogAt.failed
      {coreOf loadedConfiguration} {Operational.LogAttempt.archives observed} detail files →
    P.Runs (afterLogging watch loadedConfiguration) events result →
    P.Runs (afterLog watch loadedConfiguration observed)
      ((reportDiagnostic detail , tt) ∷ events) result
  logFailureContinues watch loadedConfiguration observed detail files events result failure execution
    rewrite failure = P.replied _ _ tt execution

  afterConfig : Bool → C.Result → Script Host.Outcome
  afterConfig watch (inj₁ detail) = persistInvalid detail >>= λ _ → announce watch
    where
    announce : Bool → Script Host.Outcome
    announce true = ask (reportDiagnostic detail) (λ _ → done (Host.outcome Host.invalidConfig true false))
    announce false = ask (reportDiagnostic detail) (λ _ → failed false (invalidConfig detail) Host.invalidConfig)
  afterConfig watch (inj₂ loadedConfiguration) = ask (prepareLog loadedConfiguration) (afterLog watch loadedConfiguration)

  once : Bool → Script Host.Outcome
  once watch = ask loadConfig (afterConfig watch)

  -- No batch result terminates watch mode. Successful work proceeds
  -- immediately; idle and blocked states wait for their respective events.
  data WatchState : Set where
    subscribing : WatchState
    watching : WorkSubscription → Script Host.Outcome → WatchState
    controlling : Script WatchState → WatchState

  awaitRepair : Text → Script WatchState
  awaitRepair detail = ask (reportDiagnostic (detail ++ toList
    ". Work remains pending. Resolve the cause, then send SIGHUP to this watcher, or edit its configuration, to resume."))
    (λ _ → ask waitForRepair (λ _ → done subscribing))

  afterSubscription : Text ⊎ WorkSubscription → WatchState
  afterSubscription (inj₁ detail) = controlling (awaitRepair detail)
  afterSubscription (inj₂ subscription) = watching subscription (once true)

  afterWork : WorkSubscription → Text ⊎ WorkWake → Script WatchState
  afterWork subscription (inj₁ detail) = ask (dropWorkSubscription subscription) (λ _ → awaitRepair detail)
  afterWork subscription (inj₂ configurationChanged) = ask (dropWorkSubscription subscription) (λ _ → done subscribing)
  afterWork subscription (inj₂ workAvailable) = done (watching subscription (once true))
  afterWork subscription (inj₂ explicitRetry) = done (watching subscription (once true))

  afterWatch : WorkSubscription → Host.Outcome → WatchState
  afterWatch subscription (Host.outcome Host.success false false) = watching subscription (once true)
  afterWatch subscription (Host.outcome Host.success false true) =
    controlling (ask (waitForWork subscription) (afterWork subscription))
  afterWatch subscription problem = controlling (ask (dropWorkSubscription subscription)
    (λ _ → awaitRepair (toList "The current batch could not complete")))

  data WatchStep : Set where
    internal : WatchState → WatchStep
    external : (effect : Effect) → (Reply effect → WatchState) → WatchStep

  nextWatch : WatchState → WatchStep
  nextWatch subscribing = external subscribeWork afterSubscription
  nextWatch (watching subscription (done result)) = internal (afterWatch subscription result)
  nextWatch (watching subscription (ask effect continuation)) = external effect (λ reply → watching subscription (continuation reply))
  nextWatch (controlling (done state)) = internal state
  nextWatch (controlling (ask effect continuation)) = external effect (λ reply → controlling (continuation reply))

  watch : WatchState
  watch = subscribing

  batchResultHasContinuation : ∀ subscription result → Σ WatchState (λ continuation →
    nextWatch (watching subscription (done result)) ≡ internal continuation)
  batchResultHasContinuation subscription result = afterWatch subscription result , refl

  checkConfig : Script ℕ
  checkConfig = ask loadConfig λ where
    (inj₂ _) → ask (stdout valid) (λ _ → done 0)
    (inj₁ detail) → ask (reportDiagnostic detail) (λ _ → ask (stdout (invalidConfig detail)) (λ _ → done 2))

  data Receipt : (effect : Effect) → Reply effect → Set where
    configuration : ∀ events result → CC.Runs (C.start explicitConfig defaultConfig) events result → Receipt loadConfig result
    logging : ∀ loadedConfiguration observed → Receipt (prepareLog loadedConfiguration) observed
    path : ∀ events result → SP.Runs (SP.resolve explicitState) events result → Receipt resolveState result
    locked : ∀ path events result → L.FS.Runs (FS.acquire path) events result → Receipt (acquire path) result
    unlocked : ∀ held events → L.FS.Runs (L.release held) events tt → Receipt (release held) tt
    ran : ∀ settings held configPath report → Executed settings held configPath report → Receipt (execute settings held configPath) report
    observed : ∀ reply → Receipt clock reply
    recorded : ∀ held report reply → StateOperations.IncidentExecution report nothing reply → Receipt (incident held report) reply
    written : ∀ held report reply → Receipt (status held report) reply
    printed : ∀ output → Receipt (stdout output) tt
    diagnostic : ∀ detail → Receipt (reportDiagnostic detail) tt
    subscribed : ∀ result → Receipt subscribeWork result
    subscriptionDropped : ∀ subscription → Receipt (dropWorkSubscription subscription) tt
    workEvent : ∀ subscription event → Receipt (waitForWork subscription) event
    repairEvent : ∀ event → Receipt waitForRepair event

  data WatchTransition : WatchState → Maybe P.Event → WatchState → Set where
    internal : ∀ {before after} → nextWatch before ≡ WatchStep.internal after →
      WatchTransition before nothing after
    external : ∀ {before effect next reply} → nextWatch before ≡ WatchStep.external effect next →
      Receipt effect reply → WatchTransition before (just (effect , reply)) (next reply)

  data Runs {A : Set} : Script A → List P.Event → A → Set where
    returned : ∀ result → Runs (done result) [] result
    replied : ∀ effect continuation reply events result → Receipt effect reply → Runs (continuation reply) events result →
      Runs (ask effect continuation) ((effect , reply) ∷ events) result

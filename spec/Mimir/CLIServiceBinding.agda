{-# OPTIONS --safe #-}
-- CLI and optional hooks use the same core startup and application operations
-- as MCP. Formatting/terminal I/O are dependency operations, not DB queries.
module Mimir.CLIServiceBinding where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.CLI as CLI
import Mimir.HookProtocol as Hook
import Mimir.ApplicationProtocol as Application
import Mimir.ConfigurationPath as Path
import Mimir.ConnectionProtocol as Connection
import Mimir.ServiceConnection as Service
import Mimir.MigrationRuntime as Migration
import Mimir.ApplicationStore as Store
import Mimir.DatabaseReadCommitted as Committed

import Mimir.ApplicationOutput as Output
import Mimir.GraphReadProtocol as Read
import Mimir.CandidateGraph as Graph
import Mimir.RetrievalRanking as Ranking
import Mimir.Effects as Effects
import Mimir.Recovery as Recovery
import Mimir.McpErrors as Errors
module Correction = Errors.AgentCorrection
open CLI using (ServiceCommand; Invocation; DatabaseCommand; Admitted; WriteCall
  ; ReadCall; module DatabaseObservations; writeService; readService; statisticsService
  ; contradictionsService; interventionService; graphRead; relevantRead
  ; evidenceRead; documentRead; list; patterns; evidenceList; listRows; patternRows
  ; service; control; reembed; invocation; serviceCase; controlCase; backfillCase)
import Mimir.ToolCatalog as Tools
import Mimir.StructuredValue as Wire
import Mimir.PublicRetrievalRecovery as Search
import Mimir.PublicDocumentQueryRecovery as Documents
import Mimir.DocumentQuery as DocumentsResult
import Mimir.EvidenceRead as Evidence
import Mimir.Validation as Validation
import Mimir.CLIReembed as Reembed
import Mimir.BackfillRecovery as Backfill
import Mimir.BackfillPreparationRecovery as BackfillPreparation
import Mimir.ConfigurationProtocol as Configuration
import Mimir.ConfigurationValues as ConfigValues
import Mimir.Unsigned as Unsigned
import Mimir.StandardLibrary as Library
open import Relation.Nullary using (Dec)
import Mimir.ConfigurationSchema as ConfigurationSchema
import Mimir.ConfigurationUpgrade as Upgrade
import Mimir.JudgeConfiguration as JudgeConfiguration
import Mimir.JudgeConfigurationComposition as JudgeConfigurationBinding
import Mimir.JudgeCommandExecution as JudgeCommand
import Mimir.UnixPath as NativePath
import Mimir.UnixMetadata as Metadata

-- Offline compatibility includes the same optional runtime checks as the
-- actual CLI. A raw 'compatible' value is insufficient: execution below must
-- carry the actual core-load and (when needed) judge-load traces.
module ConfigurationChecking (library : Library.Contract) (sizeMaximum : ℕ)
  (libraries : JudgeConfiguration.Libraries) (unix : Bool) (owner : Metadata.UserId) where
  nativePath = JudgeCommand.nativePath library
  module Core = Configuration.Run
  module Retirement = ConfigurationSchema.Retirement library
  module Judge = JudgeConfiguration.Load library sizeMaximum libraries unix owner
  module Joined = JudgeConfigurationBinding.Compose library sizeMaximum libraries unix owner

  data Failure : Set where
    coreFailure : Configuration.Failure → Failure
    retiredFields runtimeFailure : Text → Failure
    retirementFailure : Validation.Fault → Failure
  data Result : Set where
    compatible : ConfigurationSchema.Config → Result
    needsInput : Failure → Result

  retired : ConfigurationSchema.Config → Text ⊎ ⊤
  retired cfg with Upgrade.checkOptional "judge" Upgrade.judgeKeys (ConfigurationSchema.Config.judge cfg)
  ... | inj₁ detail = inj₁ detail
  ... | inj₂ tt with Upgrade.checkOptional "llm" Upgrade.llmKeys (ConfigurationSchema.Config.llm cfg)
  ... | inj₁ detail = inj₁ detail
  ... | inj₂ tt = Upgrade.checkOptional "email" Upgrade.emailKeys (ConfigurationSchema.Config.email cfg)

  retention : ConfigurationSchema.Config → Validation.Fault ⊎ ⊤
  retention cfg with ConfigurationSchema.Config.retirement cfg
  ... | nothing = inj₂ tt
  ... | just value with Retirement.resolve (just value)
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ duration = inj₂ tt

  runtimeRequired : ConfigurationSchema.Config → Bool
  runtimeRequired cfg with ConfigurationSchema.Config.judge cfg | ConfigurationSchema.Config.llm cfg
  ... | nothing | nothing = false
  ... | _ | _ = true

  data Effect : Set where
    loadCore : Path.Path → Effect
    loadRuntime : Path.Path → ConfigurationSchema.Config → Effect
  Reply : Effect → Set
  Reply (loadCore _) = Configuration.Failure ⊎ ConfigurationSchema.Config
  Reply (loadRuntime _ _) = Judge.Result
  module P = Effects.Protocol Effect Reply

  afterRuntime : ConfigurationSchema.Config → Judge.Result → P.Script Result
  afterRuntime cfg (inj₁ detail) = P.done (needsInput (runtimeFailure detail))
  afterRuntime cfg (inj₂ admittedRuntime) = P.done (compatible cfg)
  afterRetention : Path.Path → ConfigurationSchema.Config → P.Script Result
  afterRetention path cfg with retention cfg
  ... | inj₁ fault = P.done (needsInput (retirementFailure fault))
  ... | inj₂ tt with runtimeRequired cfg
  ... | false = P.done (compatible cfg)
  ... | true = P.ask (loadRuntime path cfg) (afterRuntime cfg)
  afterCore : (path : Path.Path) → Reply (loadCore path) → P.Script Result
  afterCore path (inj₁ failure) = P.done (needsInput (coreFailure failure))
  afterCore path (inj₂ cfg) with retired cfg
  ... | inj₁ detail = P.done (needsInput (retiredFields detail))
  ... | inj₂ tt = afterRetention path cfg
  script : Path.Path → P.Script Result
  script path = P.ask (loadCore path) (afterCore path)

  data Receipt : (effect : Effect) → Reply effect → Set where
    coreRead : ∀ path events result → Configuration.P.Runs (Core.load path) events result → Receipt (loadCore path) result
    runtimeRejected : ∀ path cfg events detail →
      Joined.Runs (Judge.start (just (nativePath path)) (nativePath path)) events (inj₁ detail) →
      Receipt (loadRuntime path cfg) (inj₁ detail)
    runtimeAccepted : ∀ path cfg events loaded →
      Joined.Runs (Judge.start (just (nativePath path)) (nativePath path)) events (inj₂ loaded) →
      JudgeConfiguration.Runtime.core (Judge.Check.Admitted.settings (Judge.Loaded.configuration loaded)) ≡ cfg →
      Receipt (loadRuntime path cfg) (inj₂ loaded)
  data Runs : P.Script Result → List P.Event → Result → Set where
    returned : ∀ result → Runs (P.done result) [] result
    replied : ∀ effect continuation reply events result → Receipt effect reply →
      Runs (continuation reply) events result → Runs (P.ask effect continuation) ((effect , reply) ∷ events) result
  record Execution (path : Path.Path) : Set where
    constructor checkedConfiguration
    field
      result : Result
      events : List P.Event
      checked : Runs (script path) events result

-- The CLI upgrade command consumes the existing complete-file certificate,
-- then performs the real offline compatibility checks before its success line.
-- Neither a saved raw result nor an unchecked 'compatible' flag is accepted.
module ConfigurationBinding (Frame : Set) (library : Library.Contract) (sizeMaximum : ℕ)
  (libraries : JudgeConfiguration.Libraries) (unix : Bool) (owner : Metadata.UserId)
  (defaultPath : Path.Path) where
  module Checking = ConfigurationChecking library sizeMaximum libraries unix owner
  pathUTF8 : Path.Path → Maybe Text
  pathUTF8 path with Library.Contract.decodeUTF8 library (JudgeCommand.nativePath library path)
  ... | inj₁ reason = nothing
  ... | inj₂ value = just value
  module Document = Upgrade.Document Text
  module Body (directory : Maybe Text) = Document.Replacement Frame directory
  module Selected (directory : Maybe Text) = Recovery.Recoverable (Body.recoverable directory)

  directory : Maybe Path.Path → Maybe (Maybe Text)
  directory nothing = just nothing
  directory (just path) with pathUTF8 path
  ... | nothing = nothing
  ... | just value = just (just value)

  data UpgradeExecution (submitted : Maybe Path.Path) : Set where
    rejectedDirectory : directory submitted ≡ nothing → UpgradeExecution submitted
    completedUpgrade : ∀ decoded → directory submitted ≡ just decoded → ∀ before after reply →
      Selected.X.Completed decoded (Selected.script decoded tt) before after reply → UpgradeExecution submitted
    interruptedUpgrade : ∀ decoded → directory submitted ≡ just decoded → ∀ before current →
      Selected.X.Interrupted decoded (Selected.script decoded tt) before current → Text → UpgradeExecution submitted

  data Effect : Set where
    executeUpgrade : Path.Path → Maybe Path.Path → Effect
    checkCompatibility : Path.Path → Effect
    inputCorrection : Correction.Claim → Effect
    upgradeDecision : Path.Path → Document.Failure → Effect
    checkDecision : Path.Path → Checking.Failure → Effect
    recoveryDecision : Path.Path → Text → Effect
    directoryDecision : Path.Path → Effect
    announceCompatible : Path.Path → ConfigurationSchema.Config → Effect
  Reply : Effect → Set
  Reply (executeUpgrade _ directory) = UpgradeExecution directory
  Reply (checkCompatibility path) = Checking.Execution path
  Reply _ = ⊤
  module P = Effects.Protocol Effect Reply

  selectedPath : Maybe Path.Path → Path.Path
  selectedPath nothing = defaultPath
  selectedPath (just path) = path
  afterCheck : ∀ path → Checking.Execution path → P.Script ℕ
  afterCheck path checked with Checking.Execution.result checked
  ... | Checking.needsInput failure = P.ask (checkDecision path failure) (λ _ → P.done 1)
  ... | Checking.compatible cfg = P.ask (announceCompatible path cfg) (λ _ → P.done 0)
  afterUpgrade : ∀ path directory → UpgradeExecution directory → P.Script ℕ
  afterUpgrade path submitted (rejectedDirectory invalid) =
    P.ask (directoryDecision path) (λ _ → P.done 1)
  afterUpgrade path submitted (completedUpgrade decoded same before after (inj₁ failure) physical) =
    P.ask (upgradeDecision path failure) (λ _ → P.done 1)
  afterUpgrade path submitted (completedUpgrade decoded same before after (inj₂ tt) physical) =
    P.ask (checkCompatibility path) (afterCheck path)
  afterUpgrade path submitted (interruptedUpgrade decoded same before current physical detail) =
    P.ask (recoveryDecision path detail) (λ _ → P.done 1)

  dispatch : CLI.ConfigurationCommand → P.Script ℕ
  dispatch (CLI.check explicit) = P.ask (checkCompatibility (selectedPath explicit)) (afterCheck (selectedPath explicit))
  dispatch (CLI.upgrade explicit logging) =
    P.ask (executeUpgrade (selectedPath explicit) logging) (afterUpgrade (selectedPath explicit) logging)
  start : CLI.ConfigurationCommand → Maybe Text → P.Script ℕ
  start command token with CLI.admit library (CLI.invocation (CLI.configuration command) token)
  ... | inj₁ report = P.ask (inputCorrection report) (λ _ → P.done 0)
  ... | inj₂ admitted = dispatch command

  invalidFlagsCannotStartConfigurationIO : ∀ command token report →
    CLI.admit library (CLI.invocation (CLI.configuration command) token) ≡ inj₁ report →
    start command token ≡ P.ask (inputCorrection report) (λ _ → P.done 0)
  invalidFlagsCannotStartConfigurationIO command token report invalid rewrite invalid = refl

-- Initialization runs without an application/database environment: the file
-- may not exist yet. Its sole execution effect selects the fixed filesystem
-- certificate. A raw status or a caller-provided operation cannot satisfy it.
module InitializationBinding (Frame : Set) (parser : Unsigned.Parser)
  (compareFields : ∀ pairs old desired → Dec (Configuration.explicitFields pairs old ≡ Configuration.explicitFields pairs desired))
  (available : Configuration.Initialization.Input Frame parser compareFields → ConfigValues.Config →
    Configuration.Initialization.World Frame parser compareFields → Configuration.Initialization.Metadata Frame parser compareFields)
  (library : Library.Contract) (path : Path.Path) (editorValue : Maybe Text) where
  module I = Configuration.Initialization Frame parser compareFields
  module Certified = I.Execution available
  module Selected = Recovery.RecoverableFor Certified.operation
  module Editor = Configuration.Run.Creation parser

  data InitExecution (input : I.Input) : Set where
    completedInit : ∀ before after reply → Selected.X.Completed (Selected.script input) before after reply → InitExecution input
    interruptedInit : ∀ before current → Selected.X.Interrupted (Selected.script input) before current → Text → InitExecution input

  record EditorExecution : Set where
    constructor observedEditor
    field
      result : Configuration.Failure ⊎ ⊤
      events : List Configuration.P.Event
      executed : Configuration.P.Runs (Editor.editorSession path editorValue) events result

  data Effect : Set where
    executeInit : I.Input → Effect
    executeEditor : Effect
    inputCorrection : Correction.Claim → Effect
    configurationDecision : Configuration.Failure → Effect
    interruptedDecision : Text → Effect
    announceRestart : Effect
  Reply : Effect → Set
  Reply (executeInit input) = InitExecution input
  Reply executeEditor = EditorExecution
  Reply _ = ⊤
  module P = Effects.Protocol Effect Reply

  afterEditor : EditorExecution → P.Script ℕ
  afterEditor observed with EditorExecution.result observed
  ... | inj₁ failure = P.ask (configurationDecision failure) (λ _ → P.done 1)
  ... | inj₂ tt = P.done 0

  afterInit : ∀ input → InitExecution input → P.Script ℕ
  afterInit input (completedInit before after (I.needsDecision failure) physical) =
    P.ask (configurationDecision failure) (λ _ → P.done 1)
  afterInit input (completedInit before after (I.ready (I.configurationReady document)) physical) =
    P.ask announceRestart (λ _ → P.done 0)
  afterInit input (completedInit before after (I.ready (I.editorReady document)) physical) =
    P.ask executeEditor afterEditor
  afterInit input (interruptedInit before current physical detail) =
    P.ask (interruptedDecision detail) (λ _ → P.done 1)

  selected : List (Data.String.String × Text) → I.Input
  selected [] = I.interactive
  selected (first ∷ rest) = I.explicit (first , rest)

  start : List (Data.String.String × Text) → Maybe Text → P.Script ℕ
  start pairs token with CLI.admit library (CLI.invocation (CLI.init pairs) token)
  ... | inj₁ report = P.ask (inputCorrection report) (λ _ → P.done 0)
  ... | inj₂ admitted = P.ask (executeInit (selected pairs)) (afterInit (selected pairs))

  completedInitializationMeetsGoal : ∀ input before after reply →
    Selected.X.Completed (Selected.script input) before after reply → I.Goal input before after reply
  completedInitializationMeetsGoal = Selected.completedMeetsGoal

  invalidFlagsCannotStartInitialization : ∀ pairs token report →
    CLI.admit library (CLI.invocation (CLI.init pairs) token) ≡ inj₁ report →
    start pairs token ≡ P.ask (inputCorrection report) (λ _ → P.done 0)
  invalidFlagsCannotStartInitialization pairs token report invalid rewrite invalid = refl

module Run (environment : Application.Environment) where
  databaseSum = Application.Environment.databaseSum environment
  conversion = Application.Environment.library environment
  format = Application.Environment.format environment
  module A = Application.Run environment
    using (ReadRequest; Result; readView; basicView; retrievalView; documentView
      ; graphRead; relevantRead; evidenceRead; documentRead)
  module O = Output.Encode environment format using (result)
  module B = Application.Run.C.Basic environment
    using (Request; View; listBeliefs; listPatterns; evidence)
  module RetrievalResults = Application.Run.C.Retrieval environment using (Result; completed)
  module DocumentResults = Application.Run.C.DocumentQuery environment using (value)
  module Args = CLI.Arguments format
  module D = DatabaseObservations databaseSum (Application.Environment.calculator environment)
  module Observed = Recovery.RecoverableFor D.operation

  data Failure : Set where
    connection output : Text → Failure

  -- The terminal renderer receives only the selected complete data. It has
  -- no database access and does not parse JSON to recover scalar values.
  data Line : Set where
    inputDecision : Correction.Claim → Line
    certifiedOutput : A.Result → Line
    beliefOutput : List Graph.BeliefValues → Line
    patternOutput : List Graph.PatternValues → Line
    evidenceOutput : List Evidence.Reference → Line
    retrievalOutput : Search.Response → Line
    documentOutput : DocumentsResult.Result → Line
    countedOutput : Read.Statistics → Line
    emptyIntervention emptyContradictions : Line
    intervention : ℕ → Float → Maybe Graph.BeliefValues → Line
    contradiction : ℕ → ℕ → Maybe Graph.BeliefValues → Maybe Graph.BeliefValues → Line
    observationDecision : D.N.Result → Line

  data Effect : Set where
    connect : Effect
    execute : Tools.Tool → Wire.Value → Effect
    executeRead : A.ReadRequest → Effect
    executeBackfill : ℕ → Effect
    observe : D.Request → Effect
    print : Line → Effect

  Reply : Effect → Set
  Reply connect = Text ⊎ ⊤
  Reply (execute _ _) = A.Result
  Reply (executeRead _) = A.Result
  Reply (executeBackfill _) = Text ⊎ ⊤
  Reply (observe _) = Text ⊎ D.Result
  Reply (print _) = Text ⊎ ⊤
  module P = Effects.Protocol Effect Reply
  open P using (Script; done; ask) renaming (_>>=_ to _then_)

  data Observation (input : D.Request) (before : Store.World) : D.Result → Set where
    completedObservation : ∀ after reply →
      Observed.X.Completed (Observed.script input) before after reply → Observation input before reply

  emit : Line → Script (Failure ⊎ ⊤)
  emit line = ask (print line) λ where
    (inj₁ error) → done (inj₁ (output error))
    (inj₂ tt) → done (inj₂ tt)

  outputLines : D.Result → List Line
  outputLines (D.counts values) = countedOutput values ∷ []
  outputLines (D.pairs []) = emptyContradictions ∷ []
  outputLines (D.pairs values@(_ ∷ _)) = map (λ { (a , b , first , second) → contradiction a b first second }) values
  outputLines (D.projection (D.N.calculated []) rows) = emptyIntervention ∷ []
  outputLines (D.projection (D.N.calculated (_ ∷ _)) rows) = map
    (λ { (id , probability , belief) → intervention id probability belief }) rows
  outputLines (D.projection result rows) = observationDecision result ∷ []

  emitLines : List Line → Script (Failure ⊎ ⊤)
  emitLines [] = done (inj₂ tt)
  emitLines (line ∷ rest) = emit line then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ tt) → emitLines rest

  observedOutput : D.Result → Script (Failure ⊎ ⊤)
  observedOutput result = emitLines (outputLines result)

  data Printed : List Line → List P.Event → Set where
    none : Printed [] []
    next : ∀ line lines events → Printed lines events → Printed (line ∷ lines) ((print line , inj₂ tt) ∷ events)

  completedOutputIsExact : ∀ lines events → P.Runs (emitLines lines) events (inj₂ tt) → Printed lines events
  completedOutputIsExact [] .[] (P.returned _) = none
  completedOutputIsExact (line ∷ lines) events (P.replied _ _ (inj₁ error) ())
  completedOutputIsExact (line ∷ lines) events (P.replied _ _ (inj₂ tt) rest) =
    next line lines _ (completedOutputIsExact lines _ rest)

  observationOutputMeetsGoal : ∀ input before after reply → Observed.X.Completed (Observed.script input) before after reply →
    ∀ events → P.Runs (observedOutput reply) events (inj₂ tt) →
    D.Goal input before after reply × Printed (outputLines reply) events
  observationOutputMeetsGoal input before after reply complete events emitted =
    D.completedMeetsGoal input before after reply complete , completedOutputIsExact (outputLines reply) events emitted

  afterObservation : Text ⊎ D.Result → Script (Failure ⊎ ⊤)
  afterObservation (inj₁ error) = done (inj₁ (connection error))
  afterObservation (inj₂ result) = observedOutput result

  readRequest : ReadCall → A.ReadRequest
  readRequest (graphRead request) = A.graphRead request
  readRequest (relevantRead text limit project prefer evidence) =
    A.relevantRead (Search.fromFields text limit project prefer evidence nothing)
  readRequest (evidenceRead belief) = A.evidenceRead belief
  readRequest (documentRead text project limit) = A.documentRead (Documents.query text project limit)

  -- The structured CLI report is derived from the terminal proof packet;
  -- no raw JSON object can stand in for a completed operation report.
  structuredReport : A.Result → Wire.Value
  structuredReport = O.result

  publicOutput : A.Result → Script (Failure ⊎ ⊤)
  publicOutput result = emit (certifiedOutput result)

  basicOutput : ServiceCommand → (request : B.Request) → B.View request → A.Result → Script (Failure ⊎ ⊤)
  basicOutput (list _ limit) (B.listBeliefs _ _) rows result = emit (beliefOutput (listRows limit rows))
  basicOutput (patterns _ limit) (B.listPatterns _) rows result = emit (patternOutput (patternRows limit rows))
  basicOutput (evidenceList _) (B.evidence _) rows result = emit (evidenceOutput rows)
  basicOutput command request value result = publicOutput result

  retrievalResponse : RetrievalResults.Result → Search.Response
  retrievalResponse (RetrievalResults.completed _ _ _ _ value) = value

  readOutput : ServiceCommand → A.Result → Script (Failure ⊎ ⊤)
  readOutput command result with A.readView result
  ... | nothing = publicOutput result
  ... | just (A.basicView request value) = basicOutput command request value result
  ... | just (A.retrievalView request value) = emit (retrievalOutput (retrievalResponse value))
  ... | just (A.documentView request value) = emit (documentOutput (DocumentResults.value value))

  inputFault : Validation.Fault → Script (Failure ⊎ ⊤)
  inputFault detail = emit (inputDecision (Correction.claim
    (Correction.item Correction.arguments detail
      (toList "Arguments accepted by this Mimir command.")
      (toList "Correct the reported fields and rerun the original command. If a required value is unknown, ask the user instead of guessing.")) []))

  attachToken : Maybe Text → Wire.Value → Wire.Value
  attachToken nothing arguments = arguments
  attachToken (just token) arguments = Args.withToken token arguments

  dispatchService : ServiceCommand → Maybe Text → Script (Failure ⊎ ⊤)
  dispatchService command token with Args.serviceRoute conversion command
  ... | inj₁ detail = inputFault detail
  ... | inj₂ (writeService selected) = ask (execute (WriteCall.tool selected)
    (attachToken token (WriteCall.arguments selected))) publicOutput
  ... | inj₂ (readService selected) = ask (executeRead (readRequest selected)) (readOutput command)
  ... | inj₂ statisticsService = ask (observe D.readStats) afterObservation
  ... | inj₂ (contradictionsService project) = ask (observe (D.readContradictions project)) afterObservation
  ... | inj₂ (interventionService id value) = ask (observe (D.readIntervention id value)) afterObservation

  connectThen : Script (Failure ⊎ ⊤) → Script (Failure ⊎ ⊤)
  connectThen program = ask connect λ where
    (inj₁ error) → done (inj₁ (connection error))
    (inj₂ tt) → program

  afterBackfill : Text ⊎ ⊤ → Script (Failure ⊎ ⊤)
  afterBackfill (inj₁ detail) = done (inj₁ (connection detail))
  afterBackfill (inj₂ tt) = done (inj₂ tt)

  dispatch : (call : Invocation) → DatabaseCommand (Invocation.command call) → Admitted conversion call → Script (Failure ⊎ ⊤)
  dispatch (invocation (service command) token) (serviceCase .command) admitted = connectThen (dispatchService command token)
  dispatch (invocation (control command) token) (controlCase .command) admitted = connectThen
    (ask (execute (Args.controlTool command) (Args.controlArguments command token)) publicOutput)
  dispatch (invocation reembed token) backfillCase admitted = ask (executeBackfill (Admitted.token admitted)) afterBackfill

  start : (call : Invocation) → DatabaseCommand (Invocation.command call) → Script (Failure ⊎ ⊤)
  start call selected with CLI.admit conversion call
  ... | inj₁ detail = emit (inputDecision detail)
  ... | inj₂ admitted = dispatch call selected admitted

  invalidPreflightOnlyPrintsCorrection : ∀ call selected detail →
    CLI.admit conversion call ≡ inj₁ detail → start call selected ≡ emit (inputDecision detail)
  invalidPreflightOnlyPrintsCorrection call selected detail problems rewrite problems = refl

  invalidPreflightCannotConnect : ∀ call selected detail events finalResult →
    CLI.admit conversion call ≡ inj₁ detail → P.Runs (start call selected) events finalResult →
    Σ (Reply (print (inputDecision detail)))
      (λ reply → events ≡ ((print (inputDecision detail) , reply) ∷ []))
  invalidPreflightCannotConnect call selected detail events finalResult problems execution rewrite problems with execution
  ... | P.replied _ _ (inj₁ error) (P.returned _) = inj₁ error , refl
  ... | P.replied _ _ (inj₂ tt) (P.returned _) = inj₂ tt , refl

  exit : Failure ⊎ ⊤ → ℕ
  exit (inj₁ _) = 1
  exit (inj₂ tt) = 0

module Bound (environment : Application.Environment)
  (sizeMaximum : ℕ) (path : Path.Path) (connectionEnvironment : Connection.Environment)
  (decimalPort : ℕ → Text) (certificateBlocks : Text → List Text) (unix : Bool)
  (reads : Committed.Contract Store.World)
  (prefixPostgres : BackfillPreparation.PostgreSQL (Application.Environment.library environment) (Application.Environment.format environment))
  (journal : Backfill.JournalEncoding (Application.Environment.library environment)) where
  conversion = Application.Environment.library environment
  format = Application.Environment.format environment
  module C = Run environment
  module BR = Reembed.Run sizeMaximum path connectionEnvironment decimalPort certificateBlocks unix conversion format prefixPostgres (Application.Environment.postgres environment) journal
  private
    module S = Service.Bound sizeMaximum path connectionEnvironment decimalPort certificateBlocks unix
    module M = Migration.Runtime Text Text
    module H = Hook.Run environment
    module A = Application.Run environment using (Runs; start; startRead)

  -- Error display is an ordinary anyhow/terminal boundary. It does not turn
  -- a configuration or startup failure into a successful connection receipt.
  data Connected (migrations : M.Inputs) : C.Reply C.connect → Set where
    configFailed : ∀ failure detail → S.Receipt migrations (S.configurationFailure failure) → Connected migrations (inj₁ detail)
    serviceFailed : ∀ config failure detail → S.Receipt migrations (S.startupFailure config failure) → Connected migrations (inj₁ detail)
    ready : ∀ config service → S.Receipt migrations (S.connected config service) →
      Service.Compatible config environment → Connected migrations (inj₂ tt)

  data BackfillReceipt (migrations : M.Inputs) (token : ℕ) : C.Reply (C.executeBackfill token) → Set where
    completed : ∀ events → BR.Trace migrations (BR.start token) events BR.finished → BackfillReceipt migrations token (inj₂ tt)
    failed : ∀ events cause detail → BR.Trace migrations (BR.start token) events (BR.failed cause) → BackfillReceipt migrations token (inj₁ detail)

  data Receipt (migrations : M.Inputs) : (effect : C.Effect) → C.Reply effect → Set where
    connected : ∀ reply → Connected migrations reply → Receipt migrations C.connect reply
    executed : ∀ tool submitted initial events reply →
      A.Runs (A.start tool submitted initial) events reply → Receipt migrations (C.execute tool submitted) reply
    readExecuted : ∀ request initial events reply →
      A.Runs (A.startRead request initial) events reply → Receipt migrations (C.executeRead request) reply
    backfilled : ∀ token reply → BackfillReceipt migrations token reply → Receipt migrations (C.executeBackfill token) reply
    observed : ∀ request (event : Committed.Contract.Read reads) reply →
      C.Observation request (Committed.Contract.snapshot reads event) reply → Receipt migrations (C.observe request) (inj₂ reply)
    observationFailed : ∀ request detail → Receipt migrations (C.observe request) (inj₁ detail)
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
    executed : ∀ request initial events reply →
      A.Runs (A.startRead request initial) events reply → HookReceipt migrations (H.execute request) reply
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

-- The real CLI selector retains actual submitted arguments and delegates only
-- to its fixed owners. Judge/hook ownership is explicit; it is never a
-- successful no-op fallback. Every managed execution has the selected script
-- and its mandatory receipts in its type.
module ManagedEntry (environment : Application.Environment)
  (sizeMaximum : ℕ) (path : Path.Path) (connectionEnvironment : Connection.Environment)
  (decimalPort : ℕ → Text) (certificateBlocks : Text → List Text) (unix : Bool)
  (reads : Committed.Contract Store.World)
  (prefixPostgres : BackfillPreparation.PostgreSQL (Application.Environment.library environment) (Application.Environment.format environment))
  (journal : Backfill.JournalEncoding (Application.Environment.library environment))
  (Frame : Set) (parser : Unsigned.Parser)
  (compareFields : ∀ pairs old desired → Dec (Configuration.explicitFields pairs old ≡ Configuration.explicitFields pairs desired))
  (available : Configuration.Initialization.Input Frame parser compareFields → ConfigValues.Config →
    Configuration.Initialization.World Frame parser compareFields → Configuration.Initialization.Metadata Frame parser compareFields)
  (libraries : JudgeConfiguration.Libraries) (owner : Metadata.UserId) (editorValue : Maybe Text) where
  library = Application.Environment.library environment
  module Database = Bound environment sizeMaximum path connectionEnvironment decimalPort certificateBlocks unix reads prefixPostgres journal
  module D = Database.C
  module Init = InitializationBinding Frame parser compareFields available library path editorValue
  module Config = ConfigurationBinding Frame library sizeMaximum libraries unix owner path
  module M = Migration.Runtime Text Text

  data Call : Set where
    databaseCall : (call : CLI.Invocation) → CLI.DatabaseCommand (CLI.Invocation.command call) → Call
    initializationCall : List (Data.String.String × Text) → Maybe Text → Call
    configurationCall : CLI.ConfigurationCommand → Maybe Text → Call
    correctionCall : Correction.Claim → Call
  data Selection : Set where
    managed : Call → Selection
    judgeOwner : CLI.JudgeCommand → Selection
    hookOwner : CLI.HookCommand → Selection
  route : CLI.Invocation → Selection
  route call@(CLI.invocation (CLI.service command) token) = managed (databaseCall call (CLI.serviceCase command))
  route call@(CLI.invocation (CLI.control command) token) = managed (databaseCall call (CLI.controlCase command))
  route call@(CLI.invocation CLI.reembed token) = managed (databaseCall call CLI.backfillCase)
  route (CLI.invocation (CLI.init pairs) token) = managed (initializationCall pairs token)
  route (CLI.invocation (CLI.configuration command) token) = managed (configurationCall command token)
  route (CLI.invocation (CLI.judge command) token) = judgeOwner command
  route (CLI.invocation (CLI.hook command) token) = hookOwner command
  select : CLI.Invocation → Selection
  select call with CLI.admit library call
  ... | inj₁ report = managed (correctionCall report)
  ... | inj₂ admitted = route call

  data Effect : Set where
    database : D.Effect → Effect
    initialization : Init.Effect → Effect
    configuration : Config.Effect → Effect
    correction : Correction.Claim → Effect
  Reply : Effect → Set
  Reply (database effect) = D.Reply effect
  Reply (initialization effect) = Init.Reply effect
  Reply (configuration effect) = Config.Reply effect
  Reply (correction _) = ⊤
  module P = Effects.Protocol Effect Reply
  liftDatabase : D.P.Script (D.Failure ⊎ ⊤) → P.Script ℕ
  liftDatabase (D.P.done value) = P.done (D.exit value)
  liftDatabase (D.P.ask effect continuation) = P.ask (database effect) (λ reply → liftDatabase (continuation reply))
  liftInitialization : Init.P.Script ℕ → P.Script ℕ
  liftInitialization (Init.P.done value) = P.done value
  liftInitialization (Init.P.ask effect continuation) = P.ask (initialization effect) (λ reply → liftInitialization (continuation reply))
  liftConfiguration : Config.P.Script ℕ → P.Script ℕ
  liftConfiguration (Config.P.done value) = P.done value
  liftConfiguration (Config.P.ask effect continuation) = P.ask (configuration effect) (λ reply → liftConfiguration (continuation reply))
  program : Call → P.Script ℕ
  program (databaseCall call selected) = liftDatabase (D.start call selected)
  program (initializationCall pairs token) = liftInitialization (Init.start pairs token)
  program (configurationCall command token) = liftConfiguration (Config.start command token)
  program (correctionCall report) = P.ask (correction report) (λ _ → P.done 0)

  data Receipt (migrations : M.Inputs) : (effect : Effect) → Reply effect → Set where
    databaseObserved : ∀ effect reply → Database.Receipt migrations effect reply → Receipt migrations (database effect) reply
    initializationObserved : ∀ effect reply → Receipt migrations (initialization effect) reply
    configurationObserved : ∀ effect reply → Receipt migrations (configuration effect) reply
    correctionWritten : ∀ report → Receipt migrations (correction report) tt
  data Runs (migrations : M.Inputs) : P.Script ℕ → List P.Event → ℕ → Set where
    returned : ∀ result → Runs migrations (P.done result) [] result
    replied : ∀ effect continuation reply events result → Receipt migrations effect reply →
      Runs migrations (continuation reply) events result → Runs migrations (P.ask effect continuation) ((effect , reply) ∷ events) result

  -- Offline configuration remains offline in the actual assembled trace,
  -- including correction and interrupted-publication replies. The database
  -- constructor cannot occur merely because this module also hosts DB calls.
  data OfflineEffect : Effect → Set where
    initEffect : ∀ effect → OfflineEffect (initialization effect)
    configEffect : ∀ effect → OfflineEffect (configuration effect)
    correctionEffect : ∀ report → OfflineEffect (correction report)
  data Offline : List P.Event → Set where
    noEffects : Offline []
    offlineStep : ∀ {effect reply events} → OfflineEffect effect → Offline events → Offline ((effect , reply) ∷ events)

  initializationOffline : ∀ migrations script events result →
    Runs migrations (liftInitialization script) events result → Offline events
  initializationOffline migrations (Init.P.done value) .[] .value (returned .value) = noEffects
  initializationOffline migrations (Init.P.ask effect continuation) ._ result
    (replied _ _ reply events .result receipt rest) =
    offlineStep (initEffect effect) (initializationOffline migrations (continuation reply) events result rest)

  configurationOffline : ∀ migrations script events result →
    Runs migrations (liftConfiguration script) events result → Offline events
  configurationOffline migrations (Config.P.done value) .[] .value (returned .value) = noEffects
  configurationOffline migrations (Config.P.ask effect continuation) ._ result
    (replied _ _ reply events .result receipt rest) =
    offlineStep (configEffect effect) (configurationOffline migrations (continuation reply) events result rest)

  initializationCannotRunDatabase : ∀ migrations pairs token events result →
    Runs migrations (program (initializationCall pairs token)) events result → Offline events
  initializationCannotRunDatabase migrations pairs token = initializationOffline migrations (Init.start pairs token)

  configurationCannotRunDatabase : ∀ migrations command token events result →
    Runs migrations (program (configurationCall command token)) events result → Offline events
  configurationCannotRunDatabase migrations command token = configurationOffline migrations (Config.start command token)

  record Execution (migrations : M.Inputs) (submitted : CLI.Invocation) : Set where
    constructor managedExecution
    field
      selected : Call
      selection : select submitted ≡ managed selected
      result : ℕ
      events : List P.Event
      executed : Runs migrations (program selected) events result

  invalidInputSelectsCorrection : ∀ call report → CLI.admit library call ≡ inj₁ report →
    select call ≡ managed (correctionCall report)
  invalidInputSelectsCorrection call report invalid rewrite invalid = refl

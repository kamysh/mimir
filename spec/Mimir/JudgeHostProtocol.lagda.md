# How the judge watcher completes and resumes work

The watcher subscribes to database work notifications before it checks the
queue. Each fresh subscription is immediately followed by a batch attempt.
A successful nonempty batch starts another batch, and an empty queue waits
for new work. Reconnecting repeats the subscribe-then-check sequence so work
queued during a database outage is picked up.

## Completion and deferral

The judge confirms a review by reading back the selected experience. The
experience must still have the selected source revision, that revision must
be marked reviewed, and the saved review revision must have advanced.
A model's success message supplies no confirmation. A source that changed
in the meantime is reported as corrected. A selected revision that remains
pending stays eligible unless an attempted review identified a reason to hold it.
Final readback checks even revisions the judge never reached. It cannot put
any of them on hold. Other experience revisions continue. A new
revision or a confirmed review invalidates the old deferral. If final readback
leaves a rejected review deferred, the watcher immediately checks for other
eligible work. The report retains the failure reason. If only deferred work
remains, the watcher waits for a work event.

[JudgeBatchReadback](JudgeBatchReadback.agda) defines confirmation and
deferral. [JudgeWorkflowComposition](JudgeWorkflowComposition.agda)
connects the runner's receipts to the batch result.

## Recovering a review that did not save

| What happened | What Mimir does next |
| --- | --- |
| The judge says it is done and there is no confirmed review | Read PostgreSQL before accepting completion. If the selected revision is still pending, tell the judge to submit `review_experience` for that selection. If it again declares completion without a saved review after receiving that instruction, try the mechanical correction below before opening a repair case. If the source changed, select its new revision normally. |
| An assessment, feedback entry, or link refers to an undeclared belief candidate | Return the field path, entry index, and missing key to the judge. It can declare a supported belief under that key, reference an existing eligible belief by its database UUID, or remove the unsupported reference. A new declaration still requires an indexed supporting passage and an embedding before publication. |
| A graph explanation is requested outside the selected project | Give the judge the scope correction and continue. It may explain a belief in the selected project or read an eligible global belief as context. The project boundary applies to the corrected request. |

After a refusal, the next submission must address the reported defect. If
the judge repeats the same invalid field or stops without a saved review,
Mimir can correct the latest rejected draft when the typed fault points to
an assessment that uses a declared procedure as a belief. It removes the
assessments with that type mismatch, keeps the procedures and extracted
statements, and marks a complete source unresolved if a statement from it
lost its last assessment. It preserves other entries and never guesses a
replacement belief. The same source and review revision checks, full review
validation, transactional publication, and PostgreSQL readback apply to the
corrected draft. A refusal cannot save a review or advance its revision.
If the selected revision is still pending and the correction cannot be
applied, leave a repair case and process other eligible work.

Only an unresolved case with a concrete remedy can keep a source revision
on hold. The watcher reconstructs those holds from the repair cases. An
old status report alone cannot prevent a review from running. The failed
attempt's transcript remains available. Each fresh attempt begins with the
stored source. [Failed reviews](JudgeRevisionPolicy.lagda.md) describes the
order of fresh attempts and how a completed remedy releases a hold.

## Action required

When automatic correction cannot proceed, Mimir immediately makes an alert
eligible for delivery, independent of the daily statistics schedule. It
identifies the affected experience and revision when there is one, explains
the specific obstacle, and gives a concrete action the recipient can take.
Repeated observations of the same unresolved case reuse its notification
state. A separate affected review gets its own alert, even if it failed for
the same reason. The notification worker owns delivery. A failed delivery
keeps the alert available for the configured delivery recovery and appears
in the operational status. Review processing continues independently.

The judge builds one transcript per attempted source revision in memory.
Each tool response appears once, at the call that returned it. A confirmed
review or a superseded source discards the transcript. A review that ends
unresolved publishes its transcript in PostgreSQL; a pin selected but never
attempted produces no transcript. A failed database readback requires an
authoritative check before publication, since the review may have saved.
The alert links to the saved transcript or says that publication is pending.
A running watcher retries a pending transcript on reconnection. Pending
transcripts exist only in memory and may be lost if that process exits.
Operational logs record outcomes and actions without per-step debug entries.

For an assessment with an invalid target, the email directs the operator to
`mimir judge repair --experience <uuid> --revision <revision>`. The command
opens the rejected submission for that exact revision and explains the
assessment, its evidence and the invalid target. A proposed procedure is a
different type from a belief. The operator can choose a durable belief
owned by this project by its text or remove the assessment. When removal leaves an extracted
item without an assessment, the preview states which sources will be marked
unresolved and why; the extracted statements are preserved. Other entries
remain intact. The command repeats for additional invalid assessments,
then requires explicit confirmation before submitting the corrected review.
Cancellation and end of input leave the review pending. Success requires
both the correction's submission receipt and PostgreSQL readback, so a
concurrent operator's save is not reported as the current operator's edit.

Diagnostics present the cause and next action in plain language by default.
Raw transcript JSON requires `--json`. For a missing submission,
`--retry` starts a fresh attempt that requires an actual review submission. Before
applying an answer, Mimir rereads the selected source and review revisions.
If the source changed or somebody already reviewed it, show the current
state and use that state for the next decision. Otherwise apply the repair
through the normal review path. If the operation fails, clean up the attempt
and preserve the unresolved case with a concrete next action.

The repair case is resolved only when PostgreSQL confirms a review for that
experience and intended source revision. A quiet queue, a saved unrelated
review, and accepted email delivery provide no such confirmation. A shared
prerequisite such as invalid configuration uses its own repair action and
wake-up path below. For an unreadable result, the action is to restore the read; the alert cannot
claim the review failed to save. If a fresh judge process also exits without
an explanation or a recovery signal, the repair dialog offers the configured
backend and account as choices the operator can change. A known provider
reset or restored connection wakes the affected work automatically.

## Waiting and recovery

When PostgreSQL is temporarily unavailable, the watcher reconnects, including
when a disconnect happens during the wait after a blocked batch. The
reconnect wait exists because a disconnected subscriber cannot receive a
work notification. The watcher reports the outage once and checks the
queue after it reconnects.

The batch returns its next action alongside its human-readable report. The
watcher can wait for new work only when selection found no eligible review.
A failed attempt has to identify its recovery action at the point of failure.

Lock contention wakes on release of the lock. A known provider reset wakes at
the time supplied by the provider. Each wait first checks whether its
condition has already been satisfied. If an operator must change a setting,
restore access or select a working backend, the watcher immediately queues
the observed cause and the corresponding action for email delivery. Correcting
the named prerequisite wakes the watcher. Each wake establishes a fresh
subscription and checks the stored queue. Email delivery proceeds separately.

## Which part recovers

| Where work stopped | What allows work to continue |
| --- | --- |
| Configuration, database setup, or state access | Give the operator the specific correction. Recheck the prerequisite and start a new batch when it is restored. |
| Another judge owns the lock | Wait for its release, then subscribe and check pending work. |
| Database connection | Reconnect and check the queue. A shared outage is reported once per episode. |
| Tool startup, handshake, or incompatible selection response | The failed startup releases its child. Correct the named MCP connection or compatibility problem, then start from the stored work. A failed lookup of one held revision keeps only that revision on hold. |
| Model exit, tool failure, or a missing submission | Close the attempt, check the database and apply the [review recovery rule](JudgeRevisionPolicy.lagda.md). |
| The review needs a decision | Register the exact revision and the available correction. Work continues on other reviews while the operator uses the repair command. |
| Log, status or incident persistence | Surface the access problem and keep the database review result. After access returns the next status write reports current work. |
| Email delivery | The mail worker retains the original message. It honors the configured delivery policy. Restoring the mail account or delivery settings reopens an exhausted delivery. Reviews continue independently. |

The [watcher](../../crates/cli/src/judge/watcher.rs) and
[batch runner](../../crates/cli/src/judge/runner.rs) are the corresponding runtime entry points.
[Operations](../../docs/operations.md) describes the operator actions.

```agda
{-# OPTIONS --safe #-}
-- Run/check-config host control. Configuration, path resolution and lock
-- outcomes are distinct. Invalid configuration persistence is best effort;
-- ordinary runs retain the lock through finalization and output.
module Mimir.JudgeHostProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
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
import Mimir.JudgeRevisionPolicy as Recovery
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
import Mimir.NotificationDelivery as Delivery

module R = Records.Over UUIDValue.UUID

data Output : Set where
  valid invalidStatePath alreadyRunning stateUnavailable : Output
  invalidConfig : Text → Output
  reportOutput : R.Report → Output

-- Work notifications wake an idle watcher. A temporary database outage has
-- its own retry event, which does not depend on an operator or a subscription.
data WorkWake : Set where
  workAvailable configurationChanged explicitRetry : WorkWake
  repairCompleted : (problem : Recovery.Case) →
    Recovery.RemedyApplied (Recovery.Case.selected problem) (Recovery.Case.choice problem) → WorkWake
data ReconnectWake : Set where retryDue configurationChanged explicitRetry : ReconnectWake
data SubscriptionFailure : Set where
  configurationFailure databaseUnavailable databaseSetupFailure : Text → SubscriptionFailure
record WorkSubscription : Set where
  constructor workSubscription
  field handle : Text

-- Waits observe the current condition as well as subsequent changes, so
-- correction between diagnosis and registration is visible.
data WakeCondition : Set where
  corrected : Host.Remedy → WakeCondition
  lockReleased providerAvailable : WakeCondition
  providerReset : ℕ → WakeCondition

data RepairWake (condition : WakeCondition) : Maybe WorkSubscription → Set where
  restored configurationChanged explicitRetry : ∀ {subscription} → RepairWake condition subscription
  databaseDisconnected : ∀ {subscription} → Text → RepairWake condition (just subscription)

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
  module F = FinalizationComposition.Bound format

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

  data Executed (settings : Config.Runtime) (held : L.Locked) (configPath : Path.Path) (mode : Recovery.Selection) : Host.Batch → Set where
    completed : ∀ program before after events client report → Built (Config.Runtime.llm settings) program before →
      W.Runs settings configPath before nothing (W.W.start settings configPath mode) events after client report → Dropped client → Executed settings held configPath mode report
    setupFailure : ∀ detail observed events report → BuildFailed (Config.Runtime.llm settings) detail →
      F.Runs (Finalization.finish (setupReport observed detail) nothing) events report → Executed settings held configPath mode (Host.batch report (Host.whenCorrected (Host.selectWorkingBackend detail)))

  coreOf : C.Loaded → Core.Config
  coreOf loadedConfiguration = Config.Runtime.core
    (Config.Validate.Admitted.settings (C.Loaded.configuration loadedConfiguration))

  data Effect : Set where
    loadConfig resolveState clock : Effect
    prepareLog : C.Loaded → Effect
    acquire : Path.Path → Effect
    release : L.Locked → Effect
    execute : Config.Runtime → L.Locked → Path.Path → Recovery.Selection → Effect
    incident status : L.Locked → R.Report → Effect
    stdout : Output → Effect
    reportDiagnostic : Text → Effect
    subscribeWork waitForReconnect : Effect
    queueAction : Host.Remedy → Effect
    waitForRepair : WakeCondition → Maybe WorkSubscription → Effect
    waitForWork dropWorkSubscription : WorkSubscription → Effect

  Reply : Effect → Set
  Reply loadConfig = C.Result
  Reply (prepareLog loadedConfiguration) = Operational.LogAttempt (coreOf loadedConfiguration)
  Reply resolveState = SP.Result
  Reply clock = Maybe ℕ
  Reply (acquire _) = L.FS.Result (Maybe L.Locked)
  Reply (release _) = ⊤
  Reply (execute settings held configPath mode) = Host.Batch
  Reply (incident held report) = Text ⊎ ⊤
  Reply (status held report) = Text ⊎ ⊤
  Reply (stdout _) = ⊤
  Reply (reportDiagnostic _) = ⊤
  Reply subscribeWork = SubscriptionFailure ⊎ WorkSubscription
  Reply (waitForWork _) = Text ⊎ WorkWake
  Reply (dropWorkSubscription _) = ⊤
  Reply (queueAction remedy) = ⊤
  Reply (waitForRepair condition subscription) = RepairWake condition subscription
  Reply waitForReconnect = ReconnectWake
  module P = Effects.Protocol Effect Reply
  open P using (Script; done; ask; _>>=_)

  blockedReport : Text → Maybe ℕ → Text → R.Report
  blockedReport reason observed detail = record (R.newReport observed (toList "blocked"))
    { blockReason = just reason ; failureDetail = just detail }

  persistBlocked : Text → Text → Script ⊤
  persistBlocked reason detail = ask resolveState λ where
    (inj₁ _) → done tt
    (inj₂ resolvedPaths) → ask (acquire (StatePath.Resolved.path resolvedPaths)) λ where
      (inj₁ _) → done tt
      (inj₂ nothing) → done tt
      (inj₂ (just held)) → ask clock (λ observed →
        ask (incident held (blockedReport reason observed detail)) (λ _ →
          ask (status held (blockedReport reason observed detail)) (λ _ → ask (release held) done)))

  emit : Bool → Output → Script ⊤
  emit true output = done tt
  emit false output = ask (stdout output) done

  failed : Bool → Output → Host.Exit → Host.Continuation → Script Host.Outcome
  failed watch output code next = emit watch output >>= λ _ → done (Host.outcome code next)

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

  afterLock : Recovery.Selection → Bool → C.Loaded → Reply (acquire []) → Script Host.Outcome
  afterLock mode watch loadedConfiguration (inj₁ failure) = ask (reportDiagnostic (stateProblem failure))
    (λ _ → failed watch stateUnavailable Host.unavailable (Host.whenCorrected (Host.restoreStateAccess (stateProblem failure))))
  afterLock mode watch loadedConfiguration (inj₂ nothing) = ask (reportDiagnostic
    (toList "Another judge holds the state lock. Let that judge finish before retrying."))
    (λ _ → failed watch alreadyRunning Host.alreadyRunning Host.whenLockReleased)
  afterLock mode watch loadedConfiguration (inj₂ (just held)) =
    let settings = Config.Validate.Admitted.settings (C.Loaded.configuration loadedConfiguration)
    in ask (execute settings held (C.Loaded.path loadedConfiguration) mode) (λ result →
      emit watch (reportOutput (Host.Batch.report result)) >>= λ _ → ask (release held) (λ _ → done (Host.outcomeOf result)))

  afterLogging : Recovery.Selection → Bool → C.Loaded → Script Host.Outcome
  afterLogging mode watch loadedConfiguration = ask resolveState λ where
    (inj₁ failure) → ask (reportDiagnostic (pathProblem failure))
      (λ _ → failed watch invalidStatePath Host.invalidConfig (Host.whenCorrected (Host.restoreStateAccess (pathProblem failure))))
    (inj₂ resolvedPaths) → ask (acquire (StatePath.Resolved.path resolvedPaths)) (afterLock mode watch loadedConfiguration)

  afterLog : Recovery.Selection → Bool → (loadedConfiguration : C.Loaded) → Reply (prepareLog loadedConfiguration) → Script Host.Outcome
  afterLog mode watch loadedConfiguration observed with Operational.LogAttempt.outcome observed
  ... | OperationalLog.For.failed detail files = ask (reportDiagnostic detail) (λ _ →
    ask (queueAction (Host.restoreLogAccess detail)) (λ _ → afterLogging mode watch loadedConfiguration))
  ... | OperationalLog.For.written files = afterLogging mode watch loadedConfiguration

  logFailureContinues : ∀ mode watch loadedConfiguration observed detail files events result →
    Operational.LogAttempt.outcome observed ≡ Operational.LogAt.failed
      {coreOf loadedConfiguration} detail files →
    P.Runs (afterLogging mode watch loadedConfiguration) events result →
    P.Runs (afterLog mode watch loadedConfiguration observed)
      ((reportDiagnostic detail , tt) ∷ (queueAction (Host.restoreLogAccess detail) , tt) ∷ events) result
  logFailureContinues mode watch loadedConfiguration observed detail files events result failure execution
    rewrite failure = P.replied _ _ tt (P.replied _ _ tt execution)

  afterConfig : Recovery.Selection → Bool → C.Result → Script Host.Outcome
  afterConfig mode watch (inj₁ detail) = persistBlocked (toList "invalid_config") detail >>= λ _ → announce watch
    where
    announce : Bool → Script Host.Outcome
    announce true = ask (reportDiagnostic detail) (λ _ → done (Host.outcome Host.invalidConfig (Host.whenCorrected (Host.correctConfiguration detail))))
    announce false = ask (reportDiagnostic detail) (λ _ → failed false (invalidConfig detail) Host.invalidConfig (Host.whenCorrected (Host.correctConfiguration detail)))
  afterConfig mode watch (inj₂ loadedConfiguration) = ask (prepareLog loadedConfiguration) (afterLog mode watch loadedConfiguration)

  once : Recovery.Selection → Bool → Script Host.Outcome
  once mode watch = ask loadConfig (afterConfig mode watch)

  -- No batch result terminates watch mode. Successful work proceeds
  -- immediately; deferred batches continue to the next batch; idle and
  -- failed states wait for their respective events.
  data WatchState : Set where
    subscribing : (outageReported : Bool) → WatchState
    watching : WorkSubscription → Script Host.Outcome → WatchState
    serving : WorkSubscription → List Recovery.Entry → Script Host.Outcome → WatchState
    controlling : Script WatchState → WatchState

  reconnect : Script WatchState
  reconnect = ask waitForReconnect λ where
    retryDue → done (subscribing true)
    configurationChanged → done (subscribing false)
    explicitRetry → done (subscribing false)

  awaitDatabase : Text → Script WatchState
  awaitDatabase detail = persistBlocked (toList "database_unavailable") detail >>= λ _ →
    ask (reportDiagnostic (toList "PostgreSQL is unavailable; Mimir will retry the connection. " ++ detail))
      (λ _ → reconnect)

  resetSubscription : Maybe WorkSubscription → Script WatchState
  resetSubscription nothing = done (subscribing false)
  resetSubscription (just subscription) =
    ask (dropWorkSubscription subscription) (λ _ → done (subscribing false))

  resumeRepair : ∀ condition (subscription : Maybe WorkSubscription) → RepairWake condition subscription → Script WatchState
  resumeRepair condition subscription restored = resetSubscription subscription
  resumeRepair condition subscription configurationChanged = resetSubscription subscription
  resumeRepair condition subscription explicitRetry = resetSubscription subscription
  resumeRepair condition (just subscription) (databaseDisconnected detail) =
    ask (dropWorkSubscription subscription) (λ _ → awaitDatabase detail)

  await : WakeCondition → Maybe WorkSubscription → Script WatchState
  await condition subscription = ask (waitForRepair condition subscription) (resumeRepair condition subscription)

  requestCorrection : Maybe WorkSubscription → Host.Remedy → Script WatchState
  requestCorrection subscription remedy =
    ask (queueAction remedy) (λ _ → await (corrected remedy) subscription)

  afterSubscription : Bool → SubscriptionFailure ⊎ WorkSubscription → WatchState
  afterSubscription _ (inj₁ (configurationFailure detail)) = controlling
    (persistBlocked (toList "invalid_config") detail >>= λ _ → requestCorrection nothing (Host.correctConfiguration detail))
  afterSubscription _ (inj₁ (databaseSetupFailure detail)) = controlling
    (persistBlocked (toList "database_setup") detail >>= λ _ → requestCorrection nothing (Host.restoreDatabaseSetup detail))
  afterSubscription false (inj₁ (databaseUnavailable detail)) = controlling (awaitDatabase detail)
  afterSubscription true (inj₁ (databaseUnavailable _)) = controlling reconnect
  afterSubscription _ (inj₂ subscription) = watching subscription (once Recovery.scanQueue true)

  afterWork : WorkSubscription → Text ⊎ WorkWake → Script WatchState
  afterWork subscription (inj₁ detail) = ask (dropWorkSubscription subscription) (λ _ → awaitDatabase detail)
  afterWork subscription (inj₂ configurationChanged) = ask (dropWorkSubscription subscription) (λ _ → done (subscribing false))
  afterWork subscription (inj₂ (repairCompleted problem evidence)) = done (watching subscription (once Recovery.scanQueue true))
  afterWork subscription (inj₂ workAvailable) = done (watching subscription (once Recovery.scanQueue true))
  afterWork subscription (inj₂ explicitRetry) = ask (dropWorkSubscription subscription) (λ _ → done (subscribing false))

  serve : WorkSubscription → List Recovery.Entry → WatchState
  serve subscription [] = watching subscription (once Recovery.scanQueue true)
  serve subscription (item ∷ rest) = serving subscription rest (once (Recovery.runEntry item) true)

  afterWatch : WorkSubscription → Host.Outcome → WatchState
  afterWatch subscription (Host.outcome _ (Host.scheduled work)) = serve subscription work
  afterWatch subscription (Host.outcome _ Host.whenDatabaseReturns) = controlling
    (ask (dropWorkSubscription subscription) (λ _ → reconnect))
  afterWatch subscription (Host.outcome _ Host.whenProviderAvailable) =
    controlling (await providerAvailable (just subscription))
  afterWatch subscription (Host.outcome _ Host.scan) = watching subscription (once Recovery.scanQueue true)
  afterWatch subscription (Host.outcome _ Host.whenWorkArrives) =
    controlling (ask (waitForWork subscription) (afterWork subscription))
  afterWatch subscription (Host.outcome _ Host.whenLockReleased) =
    controlling (await lockReleased (just subscription))
  afterWatch subscription (Host.outcome _ (Host.whenProviderResets time)) =
    controlling (await (providerReset time) (just subscription))
  afterWatch subscription (Host.outcome _ (Host.whenCorrected remedy)) =
    controlling (requestCorrection (just subscription) remedy)

  afterTurn : WorkSubscription → List Recovery.Entry → Host.Outcome → WatchState
  afterTurn subscription rest (Host.outcome _ Host.scan) = serve subscription rest
  afterTurn subscription rest (Host.outcome _ (Host.scheduled later)) = serve subscription (rest ++ later)
  afterTurn subscription rest result = afterWatch subscription result

  -- One eligible peer has finished. Work it adds behind the target cannot
  -- move that target back or consume its turn.
  peerCannotPostpone : ∀ subscription {target ahead queue} →
    Recovery.BeforeTurn target ahead queue → ∀ later code →
    Σ (List Recovery.Entry) (λ remaining → Recovery.BeforeTurn target ahead remaining ×
      afterTurn subscription queue (Host.outcome code (Host.scheduled later)) ≡ serve subscription remaining)
  peerCannotPostpone subscription order later code = _ , Recovery.appendPreservesTurn order later , refl

  data WatchStep : Set where
    internal : WatchState → WatchStep
    external : (effect : Effect) → (Reply effect → WatchState) → WatchStep

  nextWatch : WatchState → WatchStep
  nextWatch (subscribing outageReported) = external subscribeWork (afterSubscription outageReported)
  nextWatch (watching subscription (done result)) = internal (afterWatch subscription result)
  nextWatch (watching subscription (ask effect continuation)) = external effect (λ reply → watching subscription (continuation reply))
  nextWatch (serving subscription rest (done result)) = internal (afterTurn subscription rest result)
  nextWatch (serving subscription rest (ask effect continuation)) =
    external effect (λ reply → serving subscription rest (continuation reply))
  nextWatch (controlling (done state)) = internal state
  nextWatch (controlling (ask effect continuation)) = external effect (λ reply → controlling (continuation reply))

  watchCore : WatchState
  watchCore = subscribing false

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
    ran : ∀ settings held configPath mode report → Executed settings held configPath mode report → Receipt (execute settings held configPath mode) report
    observed : ∀ reply → Receipt clock reply
    recorded : ∀ held report reply → StateOperations.IncidentExecution report nothing reply → Receipt (incident held report) reply
    written : ∀ held report reply → Receipt (status held report) reply
    printed : ∀ output → Receipt (stdout output) tt
    diagnostic : ∀ detail → Receipt (reportDiagnostic detail) tt
    subscribed : ∀ result → Receipt subscribeWork result
    subscriptionDropped : ∀ subscription → Receipt (dropWorkSubscription subscription) tt
    workEvent : ∀ subscription event → Receipt (waitForWork subscription) event
    actionQueued : ∀ remedy → Host.Recorded format (Host.prerequisite remedy) → Receipt (queueAction remedy) tt
    repairEvent : ∀ condition subscription event → Receipt (waitForRepair condition subscription) event
    reconnectEvent : ∀ event → Receipt waitForReconnect event

  data WatchTransition : WatchState → Maybe P.Event → WatchState → Set where
    internal : ∀ {before after} → nextWatch before ≡ WatchStep.internal after →
      WatchTransition before nothing after
    external : ∀ {before effect next reply} → nextWatch before ≡ WatchStep.external effect next →
      Receipt effect reply → WatchTransition before (just (effect , reply)) (next reply)

  operatorActionPrecedesWait : ∀ subscription remedy → Host.Recorded format (Host.prerequisite remedy) →
    WatchTransition (controlling (requestCorrection subscription remedy))
      (just (queueAction remedy , tt)) (controlling (await (corrected remedy) subscription))
  operatorActionPrecedesWait subscription remedy receipt = external refl (actionQueued remedy receipt)

  restoredStartsFresh : ∀ condition →
    WatchTransition (controlling (await condition nothing))
      (just (waitForRepair condition nothing , restored)) (controlling (done (subscribing false)))
  restoredStartsFresh condition = external refl (repairEvent condition nothing restored)

  repairWakesIdleQueue : ∀ subscription problem evidence →
    WatchTransition (controlling (ask (waitForWork subscription) (afterWork subscription)))
      (just (waitForWork subscription , inj₂ (repairCompleted problem evidence)))
      (controlling (done (watching subscription (once Recovery.scanQueue true))))
  repairWakesIdleQueue subscription problem evidence = external refl
    (workEvent subscription (inj₂ (repairCompleted problem evidence)))

  -- The retry wake does not require a file edit or signal. Every newly
  -- established subscription starts a batch, which checks pending work.
  outageRetryResubscribes :
    WatchTransition (controlling reconnect) (just (waitForReconnect , retryDue))
      (controlling (done (subscribing true)))
  outageRetryResubscribes = external refl (reconnectEvent retryDue)

  repeatedOutageReusesDiagnostic : ∀ detail →
    WatchTransition (subscribing true) (just (subscribeWork , inj₁ (databaseUnavailable detail)))
      (controlling reconnect)
  repeatedOutageReusesDiagnostic detail = external refl (subscribed (inj₁ (databaseUnavailable detail)))

  subscriptionStartsBatch : ∀ outageReported subscription →
    WatchTransition (subscribing outageReported) (just (subscribeWork , inj₂ subscription))
      (watching subscription (once Recovery.scanQueue true))
  subscriptionStartsBatch outageReported subscription = external refl (subscribed (inj₂ subscription))

  -- Delivery failure and cleanup never suspend the review controller. The
  -- public watcher combines both transition systems rather than awaiting mail
  -- inside a review step. A fresh delivery consumes the original message.
  module Notifications = Delivery.Alongside WatchState (Maybe P.Event) WatchTransition

  watch : Notifications.State
  watch = watchCore , Delivery.idle

  data Runs {A : Set} : Script A → List P.Event → A → Set where
    returned : ∀ result → Runs (done result) [] result
    replied : ∀ effect continuation reply events result → Receipt effect reply → Runs (continuation reply) events result →
      Runs (ask effect continuation) ((effect , reply) ∷ events) result
```

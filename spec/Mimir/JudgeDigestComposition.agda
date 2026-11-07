{-# OPTIONS --safe #-}
-- Daily/watch integration: actual validated configuration, notifier cursor,
-- core database startup, one read-only snapshot, delivery, and loop control.
module Mimir.JudgeDigestComposition where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; take; length)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllProperties
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; m≤n+m)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.JudgeHost as Host
import Mimir.JudgeHostProtocol as HostProtocol
import Mimir.JudgeFinalization as Finalization
import Mimir.JudgeDigest as Digest
import Mimir.JudgeDigestSnapshot as Snapshot
import Mimir.JudgeConfiguration as Config
import Mimir.JudgeStatePath as StatePath
import Mimir.JudgeHarnessAdapter as Harness
import Mimir.JudgeServiceBinding as Service
import Mimir.ApplicationProtocol as Application
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
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
import Mimir.ConfigurationValues as Values
import Mimir.MigrationRuntime as Migration
import Mimir.UnixPath as Path
import Mimir.UnixMetadata as Metadata
import Mimir.UUIDV4 as UUID
import Mimir.Effects as Effects
import Mimir.ReviewObservation as Observation
import Mimir.JudgeAcknowledgement as Acknowledgement
import Mimir.JudgeSelection as Selection
import Mimir.JudgeBatchReadback as Readback

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

  pathResult : H.SP.Result → Text ⊎ Path.Path
  pathResult (inj₁ error) = inj₁ (toList "invalid notification state path")
  pathResult (inj₂ path) = inj₂ (StatePath.Resolved.path path)
  cursorResult : N.Error ⊎ Daily.Cursor → Text ⊎ Daily.Cursor
  cursorResult (inj₁ error) = inj₁ (toList "notification cursor unavailable")
  cursorResult (inj₂ savedCursor) = inj₂ savedCursor

  data State : Set where idle : State; connected : ℕ → Snapshot.State → State

  data Receipt (migrations : M.Inputs) : State → (effect : Digest.Effect) → Digest.Reply effect → State → Set where
    -- The read uses the existing bounded status-file decoder; unavailable
    -- or absent state yields no report and an explicit diagnostic action.
    reportRead : ∀ state path report → Receipt migrations state (Digest.readReport path) report state
    clock : ∀ state now → Receipt migrations state Digest.localNow now state
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

  -- Native completions. A queue hint causes a durable rescan; it is not
  -- evidence that a review completed or that a particular row exists.
  data WorkWait : Host.QueueWake → Set where
    notification : WorkWait Host.workAvailable
    configurationChanged : WorkWait Host.configurationChanged
    listenerFailed : WorkWait Host.disconnected
    interrupted : WorkWait Host.interrupted

  selectedDatabase : C.Loaded → Values.Database
  selectedDatabase loadedConfiguration = Values.Config.db (Core.Config.core
    (Config.Runtime.core (Config.Validate.Admitted.settings (C.Loaded.configuration loadedConfiguration))))

  -- The same loaded value determines LISTEN's database and the first batch.
  -- Calling H.once here would reread a mutable source and break this link.
  record FirstBatch (result : Host.Outcome) : Set where
    field loaded : C.Loaded
          admitted : H.Receipt H.loadConfig (inj₂ loaded)
          subscriptionEvents : List Host.Subscription.Event
          connection : ℕ
          subscribed : Host.Subscription.Runs (Host.Subscription.start (selectedDatabase loaded))
            subscriptionEvents (inj₂ connection)
          batchEvents : List H.P.Event
          completed : H.Runs (H.afterConfig true (inj₂ loaded)) batchEvents result

  -- The core loop admits a captured daily-summary job. SMTP execution belongs
  -- to the owned consumer and is not a premise of the next review round.
  data DigestQueued (settings : Config.Runtime) (outcome : Host.Outcome) : Text ⊎ Bool → Set where
    disabled : Email.Config.enabled (Config.Runtime.email settings) ≡ false → DigestQueued settings outcome (inj₂ false)
    accepted : ∀ resolved before after → H.Receipt H.resolveState (inj₂ resolved) →
      Finalization.WorkerQueue.Accepted
        (Finalization.digestJob (Config.Runtime.email settings)
          (Values.Config.db (Core.Config.core (Config.Runtime.core settings)))
          (StatePath.Resolved.path resolved) outcome) before after →
      DigestQueued settings outcome (inj₂ false)
    unavailable : DigestQueued settings outcome (inj₂ true)

  data Step (migrations : M.Inputs) (interval threshold : ℕ) : Host.Phase → Host.Phase → Set where
    initialConfigurationFailed : ∀ state detail → H.Receipt H.loadConfig (inj₁ detail) →
      Step migrations interval threshold (Host.subscribing state) (Host.waitingConfiguration state)
    correctedConfiguration : ∀ state → WorkWait Host.configurationChanged →
      Step migrations interval threshold (Host.waitingConfiguration state) (Host.subscribing state)
    stoppedAtConfiguration : ∀ state → WorkWait Host.interrupted →
      Step migrations interval threshold (Host.waitingConfiguration state) (Host.exited Host.success)
    initialSubscriptionFailed : ∀ state loaded detail events → H.Receipt H.loadConfig (inj₂ loaded) →
      Host.Subscription.Runs (Host.Subscription.start (selectedDatabase loaded)) events (inj₁ detail) →
      Step migrations interval threshold (Host.subscribing state) (Host.exited Host.unavailable)
    firstBatch : ∀ state result → FirstBatch result →
      Step migrations interval threshold (Host.subscribing state) (Host.digest state result)
    batch : ∀ state loadedConfiguration events result → H.Receipt H.loadConfig (inj₂ loadedConfiguration) →
      H.Runs (H.afterConfig true (inj₂ loadedConfiguration)) events result →
      Step migrations interval threshold (Host.running state) (Host.digest state result)
    digest : ∀ state settings outcome result → DigestQueued settings outcome result →
      Step migrations interval threshold (Host.digest state outcome)
        (Host.step sizeMaximum interval threshold (Host.digest state outcome) result)
    continued : ∀ state messages →
      Step migrations interval threshold (Host.continuing state messages) (Host.running state)
    configurationAtBoundary : ∀ state messages → WorkWait Host.configurationChanged →
      Step migrations interval threshold (Host.continuing state messages) (Host.subscribing state)
    configurationAtTimer : ∀ state seconds messages → WorkWait Host.configurationChanged →
      Step migrations interval threshold (Host.waiting state seconds messages) (Host.subscribing state)
    workWoke : ∀ state messages reply → WorkWait reply →
      Step migrations interval threshold (Host.awaitingWork state messages)
        (Host.step sizeMaximum interval threshold (Host.awaitingWork state messages) reply)
    waited : ∀ state seconds messages result → Waited seconds messages result →
      Step migrations interval threshold (Host.waiting state seconds messages)
        (Host.step sizeMaximum interval threshold (Host.waiting state seconds messages) result)

  data Trace (migrations : M.Inputs) (interval threshold : ℕ) : Host.Phase → Host.Phase → Set where
    empty : ∀ phase → Trace migrations interval threshold phase phase
    more : ∀ before middle after → Step migrations interval threshold before middle →
      Trace migrations interval threshold middle after → Trace migrations interval threshold before after

  firstBatchRequiresSubscription : ∀ migrations interval threshold state result →
    Step migrations interval threshold (Host.subscribing state) (Host.digest state result) →
    FirstBatch result
  firstBatchRequiresSubscription migrations interval threshold state result (firstBatch .state .result receipt) = receipt

  invalidConfigurationCannotStartBatch : ∀ migrations interval threshold state result →
    Step migrations interval threshold (Host.waitingConfiguration state) (Host.digest state result) → ⊥
  invalidConfigurationCannotStartBatch migrations interval threshold state result ()

  firstBatchAcknowledgedListen : ∀ result (receipt : FirstBatch result) →
    FirstBatch.subscriptionEvents receipt ≡
      ((Host.Subscription.connect (selectedDatabase (FirstBatch.loaded receipt)) , inj₂ (FirstBatch.connection receipt)) ∷
       (Host.Subscription.listen (FirstBatch.connection receipt) , inj₂ tt) ∷ [])
  firstBatchAcknowledgedListen result receipt = Host.Subscription.successRequiresAcknowledgedListen
    (selectedDatabase (FirstBatch.loaded receipt)) (FirstBatch.subscriptionEvents receipt)
    (FirstBatch.connection receipt) (FirstBatch.subscribed receipt)

  -- A complete round uses the actual batch and digest programs. Productive
  -- completion continues without a timer. Other paths retain their existing
  -- external timer condition until their event-driven replacements are wired.
  problem : Text ⊎ Bool → Bool
  problem (inj₁ error) = true
  problem (inj₂ digestProblem) = digestProblem

  nextWatch : Host.Watch → Host.Outcome → Text ⊎ Bool → Host.Watch
  nextWatch before batchResult reply = record (Host.advance sizeMaximum before batchResult)
    { digestProblem = problem reply }

  data Continues (state : Host.Watch) : Host.Phase → Set where
    immediately : ∀ messages → Continues state (Host.continuing state messages)
    afterWork : ∀ messages → WorkWait Host.workAvailable → Continues state (Host.awaitingWork state messages)
    afterTimer : ∀ seconds messages → Waited seconds messages false →
      Continues state (Host.waiting state seconds messages)

  continuationTrace : ∀ migrations interval threshold state phase → Continues state phase →
    Trace migrations interval threshold phase (Host.running state)
  continuationTrace migrations interval threshold state .(Host.continuing state messages)
    (immediately messages) = more _ _ _ (continued state messages) (empty _)
  continuationTrace migrations interval threshold state .(Host.awaitingWork state messages)
    (afterWork messages observed) = more _ _ _ (workWoke state messages Host.workAvailable observed) (empty _)
  continuationTrace migrations interval threshold state .(Host.waiting state seconds messages)
    (afterTimer seconds messages timerReady) = more _ _ _ (waited state seconds messages false timerReady) (empty _)

  successfulRoundNeedsNoTimer : ∀ interval threshold before reply →
    Continues (nextWatch before (Host.outcome Host.success false false) reply)
      (Host.step sizeMaximum interval threshold
        (Host.digest before (Host.outcome Host.success false false)) reply)
  successfulRoundNeedsNoTimer interval threshold before (inj₁ error) = immediately _
  successfulRoundNeedsNoTimer interval threshold before (inj₂ problem) = immediately _

  record Round (migrations : M.Inputs) (interval threshold : ℕ) (before : Host.Watch) : Set where
    constructor continuedRound
    field outcome : Host.Outcome
          loadedConfiguration : C.Loaded
          admitted : H.Receipt H.loadConfig (inj₂ loadedConfiguration)
          batchEvents : List H.P.Event
          batchDone : H.Runs (H.afterConfig true (inj₂ loadedConfiguration)) batchEvents outcome
          digestReply : Text ⊎ Bool
          digestDone : DigestQueued
            (Config.Validate.Admitted.settings (C.Loaded.configuration loadedConfiguration)) outcome digestReply
          continuationReady : Continues (nextWatch before outcome digestReply)
            (Host.step sizeMaximum interval threshold (Host.digest before outcome) digestReply)

  roundTrace : ∀ migrations interval threshold before → (round : Round migrations interval threshold before) →
    Trace migrations interval threshold (Host.running before)
      (Host.running (nextWatch before (Round.outcome round) (Round.digestReply round)))
  roundTrace migrations interval threshold before
    (continuedRound batchResult loadedConfiguration admitted batchEvents batchDone reply digestDone continuationReady) =
    more _ _ _ (batch before loadedConfiguration _ _ admitted batchDone)
      (more _ _ _ (digest before _ _ _ digestDone)
        (continuationTrace migrations interval threshold _ _ continuationReady))

  appendTrace : ∀ {migrations interval threshold before middle after} →
    Trace migrations interval threshold before middle → Trace migrations interval threshold middle after →
    Trace migrations interval threshold before after
  appendTrace (empty _) second = second
  appendTrace (more _ _ _ step rest) second = more _ _ _ step (appendTrace rest second)

  Confirmed : Observation.Snapshot → Set
  Confirmed observed = Acknowledgement.Evidence (Observation.pinSnapshot observed)

  -- Selection and confirmations must occur inside the actual host batch,
  -- not in an unrelated successful call or in a model's account of its work.
  module ProgressOf (settings : Config.Runtime) (program : Text) (path configPath : Path.Path) where
    private module W = H.W true settings program path configPath
    private module P = W.W

    record ConfirmedRead (events : List P.P.Event) (selected : Observation.Snapshot) : Set where
      field observed : Observation.Snapshot
            valid : Observation.SnapshotValid observed
            acknowledged : Observation.Ack (Observation.pinSnapshot selected) observed
            occurred : Any (_≡ (P.readback (Readback.getExperience (Observation.pinSnapshot selected)) , inj₂ (just observed))) events

    record BatchEvidence (events : List P.P.Event) (remaining selected : List Observation.Snapshot) : Set where
      field excluded : List ℕ
            queried : Any (_≡ (P.selection (Selection.pending
              (Config.Judge.project (Config.Runtime.judge settings))
              (Config.Judge.batchSize (Config.Runtime.judge settings)) excluded) , inj₂ selected)) events
            ordered : selected ≡ take (Config.Judge.batchSize (Config.Runtime.judge settings)) remaining
            confirmed : All (ConfirmedRead events) selected

    evidence : ∀ {events remaining selected} → BatchEvidence events remaining selected → All Confirmed selected
    evidence observedBatch = All.map (λ read → Acknowledgement.evidence (ConfirmedRead.observed read)
      (ConfirmedRead.valid read) (ConfirmedRead.acknowledged read)) (BatchEvidence.confirmed observedBatch)

  data ObservedRun : ∀ {effect reply} → H.Receipt effect reply → List Observation.Snapshot → List Observation.Snapshot → Set where
    completedBatch : ∀ {settings held configPath report program before after events client snapshot preparationEvents prepared built execution dropped remaining selected} →
      ProgressOf.BatchEvidence settings program (H.L.Locked.path held)
        (H.PreparedMcpConfig.path snapshot) events remaining selected →
      ObservedRun (H.ran true settings held configPath report
        (H.completed program before after events client report snapshot preparationEvents prepared built execution dropped)) remaining selected

  observedEvidence : ∀ {effect reply} (receipt : H.Receipt effect reply) {remaining selected} →
    ObservedRun receipt remaining selected → All Confirmed selected
  observedEvidence receipt (completedBatch {settings = settings} {held = held} {configPath = configPath} {program = program} seen) =
    ProgressOf.evidence settings program (H.L.Locked.path held) _ seen

  ContainsBatch : ∀ {A script events result} → H.Runs {A} script events result →
    List Observation.Snapshot → List Observation.Snapshot → Set
  ContainsBatch (H.returned result) remaining selected = ⊥
  ContainsBatch (H.replied _ _ _ _ _ receipt rest) remaining selected =
    ObservedRun receipt remaining selected ⊎ ContainsBatch rest remaining selected

  containedEvidence : ∀ {A script events result} (run : H.Runs {A} script events result) {remaining selected} →
    ContainsBatch run remaining selected → All Confirmed selected
  containedEvidence (H.returned result) ()
  containedEvidence (H.replied _ _ _ _ _ receipt rest) (inj₁ seen) = observedEvidence receipt seen
  containedEvidence (H.replied _ _ _ _ _ receipt rest) (inj₂ later) = containedEvidence rest later

  -- Recovery is stronger than a reachable endpoint: every nonempty attempt
  -- selects a positive prefix of this stable, ordered queue and actual final
  -- reads confirm that prefix. It does not assume completion of the suffix.
  record RecoveredRound (migrations : M.Inputs) (interval threshold : ℕ)
    (before : Host.Watch) (remaining : List Observation.Snapshot) : Set where
    constructor recoveredRound
    field round : Round migrations interval threshold before
          first : Observation.Snapshot
          additional rest : List Observation.Snapshot
          split : remaining ≡ (first ∷ additional) ++ rest
          selected : ContainsBatch (Round.batchDone round) remaining (first ∷ additional)

  suffixBound : ∀ (prefix suffix : List Observation.Snapshot) → length suffix ≤ length (prefix ++ suffix)
  suffixBound prefix suffix rewrite length-++ prefix {ys = suffix} = m≤n+m (length suffix) (length prefix)

  predecessorBound : ∀ {m n} → suc m ≤ suc n → m ≤ n
  predecessorBound (s≤s bound) = bound

  -- Arbitrary observed recovered histories, not a chosen successful path.
  data RecoveredTrace (migrations : M.Inputs) (interval threshold : ℕ) :
    ℕ → Host.Watch → List Observation.Snapshot → Host.Watch → List Observation.Snapshot → Set where
    stopped : ∀ before remaining → RecoveredTrace migrations interval threshold 0 before remaining before remaining
    idleRound : ∀ count before after remaining (round : Round migrations interval threshold before) →
      RecoveredTrace migrations interval threshold count
        (nextWatch before (Round.outcome round) (Round.digestReply round)) [] after remaining →
      RecoveredTrace migrations interval threshold (suc count) before [] after remaining
    productiveRound : ∀ count before remaining after final
      (recovered : RecoveredRound migrations interval threshold before remaining) →
      RecoveredTrace migrations interval threshold count
        (nextWatch before (Round.outcome (RecoveredRound.round recovered)) (Round.digestReply (RecoveredRound.round recovered)))
        (RecoveredRound.rest recovered) after final →
      RecoveredTrace migrations interval threshold (suc count) before remaining after final

  recoveredExecution : ∀ {migrations interval threshold count before remaining after final} →
    RecoveredTrace migrations interval threshold count before remaining after final →
    Trace migrations interval threshold (Host.running before) (Host.running after)
  recoveredExecution (stopped before remaining) = empty _
  recoveredExecution (idleRound _ _ _ _ round rest) = appendTrace (roundTrace _ _ _ _ round) (recoveredExecution rest)
  recoveredExecution (productiveRound _ _ _ _ _ recovered rest) =
    appendTrace (roundTrace _ _ _ _ (RecoveredRound.round recovered)) (recoveredExecution rest)

  emptyQueueStaysEmpty : ∀ {migrations interval threshold count before after final} →
    RecoveredTrace migrations interval threshold count before [] after final → final ≡ []
  emptyQueueStaysEmpty (stopped _ _) = refl
  emptyQueueStaysEmpty (idleRound _ _ _ _ round rest) = emptyQueueStaysEmpty rest
  emptyQueueStaysEmpty (productiveRound _ _ _ _ _ (recoveredRound _ _ _ _ () _) rest)

  -- Every history meeting the conditions has finished by this bound. A retry
  -- or deferred result alone cannot inhabit productiveRound.
  allRecoveredHistoriesFinish : ∀ {migrations interval threshold count before remaining after final} →
    length remaining ≤ count → RecoveredTrace migrations interval threshold count before remaining after final →
    All Confirmed remaining × final ≡ []
  allRecoveredHistoriesFinish {remaining = []} bound history = [] , emptyQueueStaysEmpty history
  allRecoveredHistoriesFinish {count = zero} {remaining = first ∷ rest} () history
  allRecoveredHistoriesFinish {count = suc count} {remaining = first ∷ rest} bound
    (productiveRound _ _ _ _ _ (recoveredRound round .first additional tail refl selected) history)
    with allRecoveredHistoriesFinish (≤-trans (suffixBound additional tail) (predecessorBound bound)) history
  ... | confirmations , emptyQueue =
    AllProperties.++⁺ (containedEvidence (Round.batchDone round) selected) confirmations , emptyQueue

  record Drained (migrations : M.Inputs) (interval threshold : ℕ)
    (before : Host.Watch) (remaining : List Observation.Snapshot) : Set where
    field after : Host.Watch
          attempts : ℕ
          bounded : attempts ≤ length remaining
          executed : Trace migrations interval threshold (Host.running before) (Host.running after)
          confirmed : All Confirmed remaining

  everyStableRevisionEventuallyConfirmed : ∀ migrations interval threshold before original →
    (∀ count → Σ Host.Watch (λ after → Σ (List Observation.Snapshot) (λ remaining →
      RecoveredTrace migrations interval threshold count before original after remaining))) →
    Drained migrations interval threshold before original
  everyStableRevisionEventuallyConfirmed migrations interval threshold before original continues
    with continues (length original)
  ... | after , remaining , history with allRecoveredHistoriesFinish ≤-refl history
  ... | confirmations , emptyQueue = record
    { after = after ; attempts = length original ; bounded = ≤-refl
    ; executed = recoveredExecution history ; confirmed = confirmations }

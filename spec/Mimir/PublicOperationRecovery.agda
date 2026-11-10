{-# OPTIONS --safe #-}
-- Concrete operation kinds determine their inputs, replies and business
-- goals. There is no caller-selected goal, script or physical relation here.
module Mimir.PublicOperationRecovery where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.PublicRequest as Public
import Mimir.StandardLibrary as Library
import Mimir.PublicEncoding as Encoding
import Mimir.PosteriorComputation as Posterior
import Mimir.RetrievalRanking as Ranking
import Mimir.StorageReadBinding as Database
import Mimir.ConfigurationValues as Config
import Mimir.Recovery as Recovery
import Mimir.RegisteredStoreAdmission as Registered
import Mimir.ToolCatalog as Tools
import Mimir.ProjectDeletion as Project
import Mimir.DirectGraphRecovery as Edges
import Mimir.GroundingRecovery as Ground
import Mimir.Validation as Validation
import Mimir.RecoverableStoreStep as Step
import Mimir.PublicLearningContextRecovery as Context
import Mimir.IndependentBeliefRecovery as IndependentIntent
import Mimir.SweepRecovery as Sweep
import Mimir.ExperienceSourceRecovery as Source
import Mimir.ReviewPublicationRecovery as ReviewPublication
import Mimir.ReviewPreparationRecovery as ReviewPreparation
import Mimir.OperationControls as Controls

import Mimir.PublicOperationCatalogue as Catalogue
import Mimir.PublicOperationJournal as Journal

module Run (library : Library.Contract) (format : Encoding.Formatting)
  (databaseSum : List Float → Float) (calculator : Posterior.Calculator)
  (arithmetic : Ranking.F32) (unicode : Ranking.Unicode)
  (vectors : Database.VectorOperations) (configuration : Config.Config)
  (textBefore : Text → Text → Bool)
  (allocateOwner : ℕ → Store.World → IndependentIntent.Allocation)
  (database : ℕ) (postgres : Controls.PostgreSQL)
  (serverTime : ℕ → Store.World → ℤ)
  (utcTimestamp : Text → Validation.Fault Data.Sum.⊎ ℤ)
  (sourcePostgres : Source.PostgreSQL)
  (sweepObservation : ℕ → Store.World → Sweep.Metadata)
  (reviewDependencies : ReviewPublication.Dependencies)
  (reviewCodec : ReviewPreparation.AllocationEncoding.Codec format)
  (reviewBackend : Store.World → ReviewPublication.Preparing.Claim → Text Data.Sum.⊎ List Store.Vector) where
  private
    module Request = Public.Decode library using (Invocation; module Invocation)
  private
    module C = Catalogue.Run library format databaseSum calculator arithmetic unicode vectors configuration
        textBefore allocateOwner database postgres serverTime utcTimestamp sourcePostgres sweepObservation
        reviewDependencies reviewCodec reviewBackend using
      (Kind; patternWrite; patternRemoval; beliefRemoval; independentWrite; projectRemoval; relationship; grounding; propagation; decay; documentRemoval; defeat; sweep; sourceWrite; reviewWrite; documentLoading; Input; Result; Goal; Success; Certificate; certificate; executable; Choice; choose; ReviewEnvironment; module Creating)
  open C using (Kind; patternWrite; patternRemoval; beliefRemoval; independentWrite; projectRemoval; relationship; grounding; propagation; decay; documentRemoval; defeat; sweep; sourceWrite; reviewWrite; documentLoading; Input; Result; Goal; Success; Certificate; certificate; executable; Choice; choose; ReviewEnvironment; module Creating)

  -- The closed native tool selects its concrete writer family. The caller
  -- supplies no family, input conversion, operation name or proof capability.
  private
    module WriterSelection (environment : ReviewEnvironment) where
      module Replay = Catalogue.Run.Cached library format databaseSum calculator arithmetic unicode vectors configuration
        textBefore allocateOwner database postgres serverTime utcTimestamp sourcePostgres sweepObservation
        reviewDependencies reviewCodec reviewBackend environment using
        (Writer; projectWriter; patternWriter; independentWriter; patternRemover; beliefRemover; relationshipWriter
        ; groundingWriter; propagator; decayer; documentRemover; defeater; sweeper; sourceWriter; reviewer; documentLoader
        ; writerInput; writerName)
      record Selected (tool : Tools.Tool) : Set where
        field kind : Kind
              writer : Replay.Writer kind
              operationName : Replay.writerName writer ≡ toList (Tools.wireName tool)

      select : ∀ tool → Tools.kind tool ≡ Tools.businessWrite →
        ∀ {submitted} → Request.Invocation tool submitted → Selected tool
      select Tools.insertBelief allowed inputView = record
        { kind = independentWrite requested; writer = Replay.independentWriter; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.deleteBelief allowed inputView = record
        { kind = beliefRemoval requested; writer = Replay.beliefRemover; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.deleteProject allowed inputView = record
        { kind = projectRemoval (proj₁ project); writer = Replay.projectWriter; operationName = refl }
        where project = Creating.readProject (Request.Invocation.arguments inputView) (Request.Invocation.request inputView)
                (Request.Invocation.decoded inputView)
      select Tools.deletePattern allowed inputView = record
        { kind = patternRemoval requested; writer = Replay.patternRemover; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.insertPattern allowed inputView = record
        { kind = patternWrite requested; writer = Replay.patternWriter; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.recordSupport allowed inputView = record
        { kind = relationship Edges.support requested; writer = Replay.relationshipWriter; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.recordCause allowed inputView = record
        { kind = relationship Edges.cause requested; writer = Replay.relationshipWriter; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.recordDefeat allowed inputView = record
        { kind = defeat requested; writer = Replay.defeater; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.recordContradiction allowed inputView = record
        { kind = relationship Edges.contradiction requested; writer = Replay.relationshipWriter; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.getBelief () inputView
      select Tools.listBeliefs () inputView
      select Tools.listPatterns () inputView
      select Tools.getContradictions () inputView
      select Tools.decayAll allowed inputView = record
        { kind = decay requested; writer = Replay.decayer; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.sweepExpiredDefeated allowed inputView = record
        { kind = sweep requested; writer = Replay.sweeper; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.queryRelevant () inputView
      select Tools.addEvidence allowed inputView = record
        { kind = grounding Ground.addition requested; writer = Replay.groundingWriter; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.getEvidence () inputView
      select Tools.propagateFrom allowed inputView = record
        { kind = propagation requested; writer = Replay.propagator; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.queryIntervention () inputView
      select Tools.loadDocument allowed inputView = record
        { kind = documentLoading requested; writer = Replay.documentLoader; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.queryDocument () inputView
      select Tools.clearDocument allowed inputView = record
        { kind = documentRemoval requested; writer = Replay.documentRemover; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.getLearningReview () inputView
      select Tools.learningCapabilities () inputView
      select Tools.getLessonAssessment () inputView
      select Tools.lessonAssessmentHistory () inputView
      select Tools.explainBelief () inputView
      select Tools.recordExperience allowed inputView = record
        { kind = sourceWrite requested; writer = Replay.sourceWriter; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.pendingExperiences () inputView
      select Tools.reviewExperience allowed inputView = record
        { kind = reviewWrite requested; writer = Replay.reviewer; operationName = refl }
        where requested = Request.Invocation.request inputView
      select Tools.getExperience () inputView
      select Tools.experienceHistory () inputView
      select Tools.queryLearningContext () inputView
      select Tools.reserveOperation () inputView
      select Tools.operationOutcome () inputView
      select Tools.cancelOperation () inputView

      selected : (call : Creating.Call) → Selected (Creating.Call.tool call)
      selected call = select (Creating.Call.tool call) (Creating.Call.writer call) (Creating.Call.invocation call)
      choice : Creating.Call → Choice
      choice call = choose (Selected.kind (selected call))
        (Replay.writerInput (Selected.writer (selected call)) (Creating.Call.token call))

  -- The creating prefix is assembled here with the fixed concrete body.
  -- Neither an operation nor its business goal is a public request field.
  module PublicWrites (environment : ReviewEnvironment) (preparation : Creating.Environment) where
    private
      module Implementation where
        module Selection = WriterSelection environment using (choice; Selected; module Selected; selected)
        module Replay where
          module Fixed = Catalogue.Run.Cached library format databaseSum calculator arithmetic unicode vectors configuration
            textBefore allocateOwner database postgres serverTime utcTimestamp sourcePostgres sweepObservation
            reviewDependencies reviewCodec reviewBackend environment using (Writer; writerName; savedValue; bodyReplay)
          open Fixed public
          module Laws = Journal.Run.Cached library format databaseSum calculator arithmetic unicode vectors configuration
            textBefore allocateOwner database postgres serverTime utcTimestamp sourcePostgres sweepObservation
            reviewDependencies reviewCodec reviewBackend environment using (MetadataFrame; bodyMetadata; bodyReadback; pendingSweepUnchanged)
          open Laws public
          module Read = Controls.Readback library postgres using
            (ExecutionContext; ResumableOrCompleted; admission; admissionCompletedAnswer; admissionCompletedLookup
            ; admitted; admittedHasPending; completed; pending; returned)
        choice : Creating.Context → Choice
        choice scope = Selection.choice (Creating.Context.call scope)
        bodyKind : Creating.Context → Kind
        bodyKind scope = Choice.kind (choice scope)
        bodyInput : (scope : Creating.Context) → Input (bodyKind scope)
        bodyInput scope = Choice.input (choice scope)
        bodyWriter : (scope : Creating.Context) → Replay.Writer (bodyKind scope)
        bodyWriter scope = Selection.Selected.writer (Selection.selected (Creating.Context.call scope))
        bodyName : ∀ scope → Replay.writerName (bodyWriter scope) ≡ Creating.Call.name (Creating.Context.call scope)
        bodyName scope = Selection.Selected.operationName (Selection.selected (Creating.Context.call scope))
        bodyCertificate : (scope : Creating.Context) → Certificate (bodyKind scope)
        bodyCertificate scope = certificate environment (bodyKind scope)
        bodyOperation : (scope : Creating.Context) → Recovery.RecoverableFor Store.World
          (Input (bodyKind scope)) (Result (bodyKind scope)) (Goal (bodyKind scope))
        bodyOperation scope = executable (bodyKind scope) (bodyCertificate scope)
        module Body (scope : Creating.Context) = Recovery.RecoverableFor (bodyOperation scope)
          using (Effect; Reply; Atomic; module X; module E; script; progress; completedMeetsGoal; converges)

        data Response : Set where
          needsInput : Validation.Fault → Response
          returned : Creating.Read.Result → Response
          executed : (scope : Creating.Context) → Result (bodyKind scope) → Response

        data Effect : Set where
          prepare : Creating.Effect → Effect
          publish : (scope : Creating.Context) → Body.Effect scope → Effect
        Reply : Effect → Set
        Reply (prepare effect) = Creating.Reply effect
        Reply (publish scope effect) = Body.Reply scope effect
        Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
        Atomic before (prepare effect) reply after = Creating.Atomic before effect reply after
        Atomic before (publish scope effect) reply after = Body.Atomic scope before effect reply after
        module X = Recovery.Execution Store.World Effect Reply Atomic
        module E = X.E

        liftPrefix : ∀ {R} → Creating.E.Script R → E.Script R
        liftPrefix (Creating.E.done reply) = E.done reply
        liftPrefix (Creating.E.ask effect next) = E.ask (prepare effect) (λ reply → liftPrefix (next reply))
        liftBody : ∀ scope → Body.E.Script scope (Result (bodyKind scope)) → E.Script Response
        liftBody scope (Body.E.done reply) = E.done (executed scope reply)
        liftBody scope (Body.E.ask effect next) = E.ask (publish scope effect) (λ reply → liftBody scope (next reply))
        afterPreparation : Creating.Result → E.Script Response
        afterPreparation (Creating.needsInput fault) = E.done (needsInput fault)
        afterPreparation (Creating.returned outcome) = E.done (returned outcome)
        afterPreparation (Creating.ready scope) = liftBody scope (Body.script scope (bodyInput scope))
        script : Creating.Request → E.Script Response
        script requested = E._>>=_ (liftPrefix (Creating.script requested)) afterPreparation

        prefixEvent : Creating.E.Event → E.Event
        prefixEvent (effect , reply) = prepare effect , reply
        bodyEvent : ∀ scope → Body.E.Event scope → E.Event
        bodyEvent scope (effect , reply) = publish scope effect , reply
        prefixRuns : ∀ {R} {program : Creating.E.Script R} {events reply} →
          Creating.E.Runs program events reply → E.Runs (liftPrefix program) (Data.List.map prefixEvent events) reply
        prefixRuns (Creating.E.returned reply) = E.returned reply
        prefixRuns (Creating.E.replied effect next reply later) =
          E.replied (prepare effect) (λ observed → liftPrefix (next observed)) reply (prefixRuns later)
        bodyRuns : ∀ scope {program : Body.E.Script scope (Result (bodyKind scope))} {events reply} →
          Body.E.Runs scope program events reply →
          E.Runs (liftBody scope program) (Data.List.map (bodyEvent scope) events) (executed scope reply)
        bodyRuns scope (Body.E.returned reply) = E.returned (executed scope reply)
        bodyRuns scope (Body.E.replied effect next reply later) =
          E.replied (publish scope effect) (λ observed → liftBody scope (next observed)) reply (bodyRuns scope later)
        prefixChanges : ∀ {before events after} → Creating.X.Changes before events after →
          X.Changes before (Data.List.map prefixEvent events) after
        prefixChanges (Creating.X.unchanged before) = X.unchanged before
        prefixChanges (Creating.X.changed before effect reply middle physical later) =
          X.changed before (prepare effect) reply middle physical (prefixChanges later)
        bodyChanges : ∀ scope {before events after} → Body.X.Changes scope before events after →
          X.Changes before (Data.List.map (bodyEvent scope) events) after
        bodyChanges scope (Body.X.unchanged before) = X.unchanged before
        bodyChanges scope (Body.X.changed before effect reply middle physical later) =
          X.changed before (publish scope effect) reply middle physical (bodyChanges scope later)

        afterPreparationProgress : ∀ prepared before → Σ Store.World (λ after → Σ Response
          (λ reply → X.Completed (afterPreparation prepared) before after reply))
        afterPreparationProgress (Creating.needsInput fault) before =
          before , needsInput fault , X.completed [] (E.returned _) (X.unchanged before)
        afterPreparationProgress (Creating.returned outcome) before =
          before , returned outcome , X.completed [] (E.returned _) (X.unchanged before)
        afterPreparationProgress (Creating.ready scope) before with Body.progress scope (bodyInput scope) before
        ... | after , reply , Body.X.completed events execution changes = after , executed scope reply ,
          X.completed (Data.List.map (bodyEvent scope) events) (bodyRuns scope execution) (bodyChanges scope changes)
        progress : ∀ requested before → Σ Store.World (λ after → Σ Response
          (λ reply → X.Completed (script requested) before after reply))
        progress requested before with Creating.progress preparation requested before
        ... | middle , prepared , Creating.X.completed prefixEvents prefixExecution prefixPhysical
          with afterPreparationProgress prepared middle
        ... | after , reply , X.completed bodyEvents bodyExecution bodyPhysical = after , reply , X.completed _
          (E.bindRuns (prefixRuns prefixExecution) bodyExecution) (X.changesAppend (prefixChanges prefixPhysical) bodyPhysical)

        -- Prefix-only outcomes preserve the whole business World. A body result
        -- owes its independently specified business outcome from the original
        -- prepared baseline, including on a retry after any committed boundary.
        data Meaning (requested : Creating.Request) (before after : Store.World) : Response → Set where
          preparationDialogue : ∀ fault → Creating.Goal requested before after (Creating.needsInput fault) →
            Meaning requested before after (needsInput fault)
          preparationReadback : ∀ outcome → Creating.Goal requested before after (Creating.returned outcome) →
            Meaning requested before after (returned outcome)
          businessOutcome : ∀ baseline scope reply →
            Creating.Goal requested before baseline (Creating.ready scope) →
            Goal (bodyKind scope) (bodyInput scope) baseline after reply →
            Meaning requested before after (executed scope reply)
          cachedBusinessOutcome : ∀ baseline scope reply original raw →
            Creating.Goal requested before baseline (Creating.ready scope) →
            Goal (bodyKind scope) (bodyInput scope) baseline after reply →
            Replay.savedValue (bodyWriter scope) reply ≡ just raw →
            Creating.Read.answer (Creating.Call.token (Creating.Context.call scope)) after ≡ Creating.Read.completed original raw →
            Meaning requested before after (returned (Creating.Read.completed original raw))

        splitPrefixRun : ∀ (program : Creating.E.Script Creating.Result) before after reply {events} →
          E.Runs (E._>>=_ (liftPrefix program) afterPreparation) events reply → X.Changes before events after →
          Σ Store.World (λ middle → Σ Creating.Result (λ prepared →
            Creating.X.Completed program before middle prepared × X.Completed (afterPreparation prepared) middle after reply))
        splitPrefixRun (Creating.E.done prepared) before after reply execution changes = before , prepared ,
          Creating.X.completed [] (Creating.E.returned prepared) (Creating.X.unchanged before) , X.completed _ execution changes
        splitPrefixRun (Creating.E.ask effect next) before after reply
          (E.replied .(prepare effect) _ observed execution)
          (X.changed .before .(prepare effect) .observed middle physical changes)
          with splitPrefixRun (next observed) middle after reply execution changes
        ... | baseline , prepared , Creating.X.completed events prefixExecution prefixPhysical , completedBody =
          baseline , prepared , Creating.X.completed ((effect , observed) Data.List.∷ events)
            (Creating.E.replied effect next observed prefixExecution)
            (Creating.X.changed before effect observed middle physical prefixPhysical) , completedBody

        unliftBodyRun : ∀ scope (program : Body.E.Script scope (Result (bodyKind scope))) before after reply {events} →
          E.Runs (liftBody scope program) events reply → X.Changes before events after →
          Σ (Result (bodyKind scope)) (λ actual → reply ≡ executed scope actual × Body.X.Completed scope program before after actual)
        unliftBodyRun scope (Body.E.done actual) before .before .(executed scope actual)
          (E.returned _) (X.unchanged _) = actual , refl , Body.X.completed {scope = scope} []
            (Body.E.returned {scope = scope} actual) (Body.X.unchanged {scope = scope} before)
        unliftBodyRun scope (Body.E.ask effect next) before after reply
          (E.replied .(publish scope effect) _ observed execution)
          (X.changed .before .(publish scope effect) .observed middle physical changes)
          with unliftBodyRun scope (next observed) middle after reply execution changes
        ... | actual , same , Body.X.completed events bodyExecution bodyPhysical = actual , same ,
          Body.X.completed {scope = scope} ((effect , observed) Data.List.∷ events)
            (Body.E.replied {scope = scope} effect next observed bodyExecution)
            (Body.X.changed {scope = scope} before effect observed middle physical bodyPhysical)

        prependPrefixInterruption : ∀ before effect (continuation : Creating.Reply effect → Creating.E.Script Creating.Result) reply middle after →
          Creating.Atomic before effect reply middle → Creating.X.Interrupted (continuation reply) middle after →
          Creating.X.Interrupted (Creating.E.ask effect continuation) before after
        prependPrefixInterruption before effect continuation reply middle after physical
          (Creating.X.atPrefix events residual .after prefix changes) =
          Creating.X.atPrefix ((effect , reply) ∷ events) residual after (Creating.E.replied effect continuation reply prefix)
            (Creating.X.changed before effect reply middle physical changes)
        prependPrefixInterruption before effect continuation reply middle after physical
          (Creating.X.beforeReply events active next current observed .after prefix changes activePhysical) =
          Creating.X.beforeReply ((effect , reply) ∷ events) active next current observed after
            (Creating.E.replied effect continuation reply prefix) (Creating.X.changed before effect reply middle physical changes) activePhysical

        prependBodyInterruption : ∀ scope before effect (continuation : Body.Reply scope effect → Body.E.Script scope (Result (bodyKind scope))) reply middle after →
          Body.Atomic scope before effect reply middle → Body.X.Interrupted scope (continuation reply) middle after →
          Body.X.Interrupted scope (Body.E.ask {scope = scope} effect continuation) before after
        prependBodyInterruption scope before effect continuation reply middle after physical
          (Body.X.atPrefix events residual .after prefix changes) =
          Body.X.atPrefix {scope = scope} ((effect , reply) ∷ events) residual after
            (Body.E.replied {scope = scope} effect continuation reply prefix)
            (Body.X.changed {scope = scope} before effect reply middle physical changes)
        prependBodyInterruption scope before effect continuation reply middle after physical
          (Body.X.beforeReply events active next current observed .after prefix changes activePhysical) =
          Body.X.beforeReply {scope = scope} ((effect , reply) ∷ events) active next current observed after
            (Body.E.replied {scope = scope} effect continuation reply prefix)
            (Body.X.changed {scope = scope} before effect reply middle physical changes) activePhysical

        doneInterruptedSameWorld : ∀ (value : Response) before after → X.Interrupted (E.done value) before after → after ≡ before
        doneInterruptedSameWorld value before .before
          (X.atPrefix .[] .(E.done value) .before (E.stopped _) (X.unchanged .before)) = refl
        doneInterruptedSameWorld value before after (X.beforeReply events effect continuation current reply .after () changes physical)

        unliftBodyInterrupted : ∀ scope (program : Body.E.Script scope (Result (bodyKind scope))) before after →
          X.Interrupted (liftBody scope program) before after → Body.X.Interrupted scope program before after
        unliftBodyInterrupted scope (Body.E.done value) before after interrupted
          rewrite doneInterruptedSameWorld (executed scope value) before after interrupted =
          Body.X.atPrefix {scope = scope} [] (Body.E.done {scope = scope} value) before
            (Body.E.stopped {scope = scope} _) (Body.X.unchanged {scope = scope} before)
        unliftBodyInterrupted scope (Body.E.ask effect continuation) before .before
          (X.atPrefix .[] ._ .before (E.stopped _) (X.unchanged .before)) =
          Body.X.atPrefix {scope = scope} [] (Body.E.ask {scope = scope} effect continuation) before
            (Body.E.stopped {scope = scope} _) (Body.X.unchanged {scope = scope} before)
        unliftBodyInterrupted scope (Body.E.ask effect continuation) before after
          (X.atPrefix ._ residual .after (E.replied .(publish scope effect) _ reply prefix)
            (X.changed .before .(publish scope effect) .reply middle physical changes)) =
          prependBodyInterruption scope before effect continuation reply middle after physical
            (unliftBodyInterrupted scope (continuation reply) middle after (X.atPrefix _ residual after prefix changes))
        unliftBodyInterrupted scope (Body.E.ask effect continuation) before after
          (X.beforeReply .[] .(publish scope effect) ._ .before reply .after (E.stopped _) (X.unchanged .before) physical) =
          Body.X.beforeReply {scope = scope} [] effect continuation before reply after
            (Body.E.stopped {scope = scope} _) (Body.X.unchanged {scope = scope} before) physical
        unliftBodyInterrupted scope (Body.E.ask effect continuation) before after
          (X.beforeReply ._ active next current observed .after (E.replied .(publish scope effect) _ reply prefix)
            (X.changed .before .(publish scope effect) .reply middle physical changes) activePhysical) =
          prependBodyInterruption scope before effect continuation reply middle after physical
            (unliftBodyInterrupted scope (continuation reply) middle after
              (X.beforeReply _ active next current observed after prefix changes activePhysical))

        data InterruptedPhase (program : Creating.E.Script Creating.Result) (before after : Store.World) : Set where
          preparing : Creating.X.Interrupted program before after → InterruptedPhase program before after
          publishing : ∀ baseline scope → Creating.X.Completed program before baseline (Creating.ready scope) →
            Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline after → InterruptedPhase program before after

        prependPhase : ∀ before effect continuation reply middle after → Creating.Atomic before effect reply middle →
          InterruptedPhase (continuation reply) middle after → InterruptedPhase (Creating.E.ask effect continuation) before after
        prependPhase before effect continuation reply middle after physical (preparing interrupted) =
          preparing (prependPrefixInterruption before effect continuation reply middle after physical interrupted)
        prependPhase before effect continuation reply middle after physical
          (publishing baseline scope (Creating.X.completed events execution changes) interrupted) =
          publishing baseline scope (Creating.X.completed ((effect , reply) ∷ events)
            (Creating.E.replied effect continuation reply execution) (Creating.X.changed before effect reply middle physical changes)) interrupted

        splitInterruptedPrefix : ∀ (program : Creating.E.Script Creating.Result) before after →
          X.Interrupted (E._>>=_ (liftPrefix program) afterPreparation) before after → InterruptedPhase program before after
        splitInterruptedPrefix (Creating.E.done (Creating.ready scope)) before after interrupted =
          publishing before scope (Creating.X.completed [] (Creating.E.returned (Creating.ready scope)) (Creating.X.unchanged before))
            (unliftBodyInterrupted scope (Body.script scope (bodyInput scope)) before after interrupted)
        splitInterruptedPrefix (Creating.E.done (Creating.needsInput fault)) before after interrupted
          rewrite doneInterruptedSameWorld (needsInput fault) before after interrupted =
          preparing (Creating.X.atPrefix [] (Creating.E.done (Creating.needsInput fault)) before (Creating.E.stopped _) (Creating.X.unchanged before))
        splitInterruptedPrefix (Creating.E.done (Creating.returned outcome)) before after interrupted
          rewrite doneInterruptedSameWorld (returned outcome) before after interrupted =
          preparing (Creating.X.atPrefix [] (Creating.E.done (Creating.returned outcome)) before (Creating.E.stopped _) (Creating.X.unchanged before))
        splitInterruptedPrefix (Creating.E.ask effect continuation) before .before
          (X.atPrefix .[] ._ .before (E.stopped _) (X.unchanged .before)) =
          preparing (Creating.X.atPrefix [] (Creating.E.ask effect continuation) before (Creating.E.stopped _) (Creating.X.unchanged before))
        splitInterruptedPrefix (Creating.E.ask effect continuation) before after
          (X.atPrefix ._ residual .after (E.replied .(prepare effect) _ reply prefix)
            (X.changed .before .(prepare effect) .reply middle physical changes)) =
          prependPhase before effect continuation reply middle after physical
            (splitInterruptedPrefix (continuation reply) middle after (X.atPrefix _ residual after prefix changes))
        splitInterruptedPrefix (Creating.E.ask effect continuation) before after
          (X.beforeReply .[] .(prepare effect) ._ .before reply .after (E.stopped _) (X.unchanged .before) physical) =
          preparing (Creating.X.beforeReply [] effect continuation before reply after (Creating.E.stopped _) (Creating.X.unchanged before) physical)
        splitInterruptedPrefix (Creating.E.ask effect continuation) before after
          (X.beforeReply ._ active next current observed .after (E.replied .(prepare effect) _ reply prefix)
            (X.changed .before .(prepare effect) .reply middle physical changes) activePhysical) =
          prependPhase before effect continuation reply middle after physical
            (splitInterruptedPrefix (continuation reply) middle after
              (X.beforeReply _ active next current observed after prefix changes activePhysical))

        prefixThenBodyMeaning : ∀ requested before baseline after prepared reply →
          Creating.Goal requested before baseline prepared → X.Completed (afterPreparation prepared) baseline after reply →
          Meaning requested before after reply
        prefixThenBodyMeaning requested before baseline .baseline (Creating.needsInput fault) .(needsInput fault) certified
          (X.completed [] (E.returned _) (X.unchanged _)) = preparationDialogue fault certified
        prefixThenBodyMeaning requested before baseline .baseline (Creating.returned outcome) .(returned outcome) certified
          (X.completed [] (E.returned _) (X.unchanged _)) = preparationReadback outcome certified
        prefixThenBodyMeaning requested before baseline after (Creating.ready scope) reply certified
          (X.completed events execution changes)
          with unliftBodyRun scope (Body.script scope (bodyInput scope)) baseline after reply execution changes
        ... | actual , refl , completedBody = businessOutcome baseline scope actual certified
          (Body.completedMeetsGoal scope (bodyInput scope) baseline after actual completedBody)


        initialReady : ∀ requested before baseline scope →
          Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
          Creating.decode requested ≡ inj₂ (Creating.Context.call scope) ×
          Creating.ReadyMeaning (Creating.Context.call scope) baseline scope
        initialReady requested before baseline scope prefix with Creating.completedReady requested before baseline scope prefix
        ... | call , decoded , known =
          trans decoded (cong inj₂ (sym (Creating.ReadyMeaning.actualCall known))) ,
          subst (λ actual → Creating.ReadyMeaning actual baseline scope) (sym (Creating.ReadyMeaning.actualCall known)) known

        relabelAdmission : ∀ first second token current → first ≡ second →
          (Σ (Replay.Read.ExecutionContext first token current) (λ actual → Replay.Read.admission first token current ≡ Replay.Read.admitted actual)) →
          Σ (Replay.Read.ExecutionContext second token current) (λ actual → Replay.Read.admission second token current ≡ Replay.Read.admitted actual)
        relabelAdmission first .first token current refl actual = actual

        initialAdmission : ∀ requested before baseline scope →
          Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
          Σ (Replay.Read.ExecutionContext (Replay.writerName (bodyWriter scope))
            (Creating.Call.token (Creating.Context.call scope)) baseline) (λ actual →
            Replay.Read.admission (Replay.writerName (bodyWriter scope))
              (Creating.Call.token (Creating.Context.call scope)) baseline ≡ Replay.Read.admitted actual)
        initialAdmission requested before baseline scope prefix = relabelAdmission
          (Creating.Call.name (Creating.Context.call scope)) (Replay.writerName (bodyWriter scope))
          (Creating.Call.token (Creating.Context.call scope)) baseline (sym (bodyName scope))
          (Creating.completedReadyAdmission requested (Creating.Context.call scope) before baseline scope
            (proj₁ (initialReady requested before baseline scope prefix)) prefix)

        readbackAtCut : ∀ requested before baseline scope current →
          Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
          Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
          Replay.Read.ResumableOrCompleted (Replay.writerName (bodyWriter scope))
            (Creating.Call.token (Creating.Context.call scope)) current
        readbackAtCut requested before baseline scope current prefix cut with initialAdmission requested before baseline scope prefix
        ... | actual , admitted = Replay.bodyReadback (bodyWriter scope)
          (Creating.Call.token (Creating.Context.call scope)) baseline current actual admitted cut

        readyAtCut : ∀ scope baseline current → Creating.ReadyMeaning (Creating.Context.call scope) baseline scope →
          Replay.MetadataFrame (Creating.Call.token (Creating.Context.call scope)) baseline current →
          Creating.ReadyMeaning (Creating.Context.call scope) current scope
        readyAtCut scope baseline current known (registration , cancellation) =
          Creating.transportReady (Creating.Context.call scope) baseline current scope
            (cong (λ rows → Project.Registered.binding token (proj₁ (proj₂ (proj₂ rows)))) registration)
            (cong (λ rows → Project.Registered.plan token (proj₂ (proj₂ (proj₂ rows)))) registration)
            cancellation known
          where token = Creating.Call.token (Creating.Context.call scope)

        reservationAtCut : ∀ call baseline current → Creating.Reserved call baseline →
          Step.registration current ≡ Step.registration baseline → Creating.Reserved call current
        reservationAtCut call baseline current (row , observed) registration = row ,
          trans (cong (λ rows → Registered.reservation (Creating.Call.token call) (proj₁ rows)) registration) observed

        allowedReadback : ∀ operation token current → Replay.Read.ResumableOrCompleted operation token current →
          Creating.Resumable (Creating.Read.answer token current) ⊎ Creating.CompletedValue (Creating.Read.answer token current)
        allowedReadback operation token current (inj₁ (entry , admitted)) with Replay.Read.admittedHasPending operation token current entry admitted
        ... | original , next , rows , observed = inj₁ (subst Creating.Resumable (sym observed) tt)
        allowedReadback operation token current (inj₂ (original , raw , completed)) =
          inj₂ (original , raw , Replay.Read.admissionCompletedAnswer operation token current original raw completed)

        completedAdmission : ∀ operation token current original raw → Replay.Read.ResumableOrCompleted operation token current →
          Creating.Read.answer token current ≡ Creating.Read.completed original raw →
          Replay.Read.admission operation token current ≡ Replay.Read.returned (Replay.Read.completed original raw)
        completedAdmission operation token current original raw (inj₁ (entry , admitted)) observed
          with Replay.Read.admittedHasPending operation token current entry admitted
        ... | binding , next , rows , pending = ⊥-elim (impossible (trans (sym pending) observed))
          where
          impossible : Replay.Read.pending binding next rows ≡ Replay.Read.completed original raw → ⊥
          impossible ()
        completedAdmission operation token current original raw (inj₂ (binding , value , completed)) observed
          with trans (sym (Replay.Read.admissionCompletedAnswer operation token current binding value completed)) observed
        ... | refl = completed

        readyDialogueGoal : ∀ requested call before baseline scope fault → Creating.decode requested ≡ inj₂ call →
          Creating.Goal requested before baseline (Creating.ready scope) →
          Creating.Goal requested before baseline (Creating.needsInput fault)
        readyDialogueGoal requested call before baseline scope fault decoded earlier rewrite decoded = proj₁ earlier , Creating.dialogue fault

        policyIsSweep : ∀ tool → Creating.needsPolicy tool ≡ true → tool ≡ Tools.sweepExpiredDefeated
        policyIsSweep Tools.insertBelief ()
        policyIsSweep Tools.deleteBelief ()
        policyIsSweep Tools.deleteProject ()
        policyIsSweep Tools.deletePattern ()
        policyIsSweep Tools.insertPattern ()
        policyIsSweep Tools.recordSupport ()
        policyIsSweep Tools.recordCause ()
        policyIsSweep Tools.recordDefeat ()
        policyIsSweep Tools.recordContradiction ()
        policyIsSweep Tools.getBelief ()
        policyIsSweep Tools.listBeliefs ()
        policyIsSweep Tools.listPatterns ()
        policyIsSweep Tools.getContradictions ()
        policyIsSweep Tools.decayAll ()
        policyIsSweep Tools.sweepExpiredDefeated refl = refl
        policyIsSweep Tools.queryRelevant ()
        policyIsSweep Tools.addEvidence ()
        policyIsSweep Tools.getEvidence ()
        policyIsSweep Tools.propagateFrom ()
        policyIsSweep Tools.queryIntervention ()
        policyIsSweep Tools.loadDocument ()
        policyIsSweep Tools.queryDocument ()
        policyIsSweep Tools.clearDocument ()
        policyIsSweep Tools.getLearningReview ()
        policyIsSweep Tools.learningCapabilities ()
        policyIsSweep Tools.getLessonAssessment ()
        policyIsSweep Tools.lessonAssessmentHistory ()
        policyIsSweep Tools.explainBelief ()
        policyIsSweep Tools.recordExperience ()
        policyIsSweep Tools.pendingExperiences ()
        policyIsSweep Tools.reviewExperience ()
        policyIsSweep Tools.getExperience ()
        policyIsSweep Tools.experienceHistory ()
        policyIsSweep Tools.queryLearningContext ()
        policyIsSweep Tools.reserveOperation ()
        policyIsSweep Tools.operationOutcome ()
        policyIsSweep Tools.cancelOperation ()

        policyBeforeUnchanged : ∀ requested before baseline scope current →
          Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
          Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
          Creating.needsPolicy (Creating.Call.tool (Creating.Context.call scope)) ≡ true →
          Creating.Resumable (Creating.Read.answer (Creating.Call.token (Creating.Context.call scope)) current) → current ≡ baseline
        policyBeforeUnchanged requested before baseline scope@(Creating.preparedWrite (Creating.admittedWrite tool submitted writer inputView) original model raw)
          current prefix cut policy possible with policyIsSweep tool policy
        ... | refl with initialAdmission requested before baseline scope prefix
        ... | entry , admitted = Replay.pendingSweepUnchanged (Creating.Call.request (Creating.Context.call scope))
          (Creating.Call.token (Creating.Context.call scope)) baseline current entry admitted cut possible


        cachedCutMeaning : ∀ requested before baseline scope current original raw →
          Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
          Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
          Creating.decode requested ≡ inj₂ (Creating.Context.call scope) →
          Replay.Read.ResumableOrCompleted (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope)) current →
          Creating.Read.answer (Creating.Call.token (Creating.Context.call scope)) current ≡ Creating.Read.completed original raw →
          Meaning requested before current (returned (Creating.Read.completed original raw))
        cachedCutMeaning requested before baseline scope current original raw prefix cut decoded readState observed
          with Replay.bodyReplay (bodyWriter scope) (Creating.Call.token (Creating.Context.call scope)) baseline current original raw
            (Creating.completedReadyResultAbsent requested (Creating.Context.call scope) before baseline scope decoded prefix)
            (Replay.Read.admissionCompletedLookup (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope))
              current original raw (completedAdmission (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope))
                current original raw readState observed))
            (completedAdmission (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope))
              current original raw readState observed) cut
        ... | actual , completedBody , same = cachedBusinessOutcome baseline scope actual original raw
          (Creating.completedGoal requested before baseline (Creating.ready scope) prefix)
          (Body.converges scope (bodyInput scope) baseline current current actual cut completedBody) same observed

        policyCutMeaning : ∀ requested before baseline scope current fault →
          Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
          Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
          Creating.decode requested ≡ inj₂ (Creating.Context.call scope) →
          Creating.needsPolicy (Creating.Call.tool (Creating.Context.call scope)) ≡ true →
          Creating.Resumable (Creating.Read.answer (Creating.Call.token (Creating.Context.call scope)) current) →
          Meaning requested before current (needsInput fault)
        policyCutMeaning requested before baseline scope current fault prefix cut decoded policy possible
          with policyBeforeUnchanged requested before baseline scope current prefix cut policy possible
        ... | refl = preparationDialogue fault (readyDialogueGoal requested (Creating.Context.call scope) before baseline scope fault decoded
          (Creating.completedGoal requested before baseline (Creating.ready scope) prefix))

        joinKnown : ∀ requested before baseline scope current after reply →
          Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
          Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
          Creating.decode requested ≡ inj₂ (Creating.Context.call scope) →
          Creating.Reserved (Creating.Context.call scope) current → Creating.ReadyMeaning (Creating.Context.call scope) current scope →
          Replay.Read.ResumableOrCompleted (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope)) current →
          X.Completed (script requested) current after reply → Meaning requested before after reply
        joinKnown requested before baseline scope current after reply prefix cut decoded reserved known readState retry
          with splitPrefixRun (Creating.script requested) current after reply (X.Completed.returned retry) (X.Completed.changes retry)
        ... | middle , prepared , prefixRetry , remainder
          with Creating.completedKnownResult requested (Creating.Context.call scope) current scope middle prepared decoded reserved known
            (allowedReadback (Replay.writerName (bodyWriter scope)) (Creating.Call.token (Creating.Context.call scope)) current readState) prefixRetry
        ... | Creating.knownReady nextScope
          with Creating.readyRetrySameContext requested (Creating.Context.call scope) current middle scope nextScope decoded known prefixRetry
        ... | refl , refl with remainder
        ... | X.completed events execution physical
          with unliftBodyRun scope (Body.script scope (bodyInput scope)) current after reply execution physical
        ... | actual , refl , completedBody = businessOutcome baseline scope actual
          (Creating.completedGoal requested before baseline (Creating.ready scope) prefix)
          (Body.converges scope (bodyInput scope) baseline current after actual cut completedBody)
        joinKnown requested before baseline scope current after reply prefix cut decoded reserved known readState retry
          | middle , prepared , prefixRetry , remainder | Creating.knownCompleted original raw observed
          with Creating.completedDecodedExistingUnchanged requested (Creating.Context.call scope) current middle
            (Creating.returned (Creating.Read.completed original raw)) (Creating.Context.original scope) (Creating.Context.raw scope)
            decoded (Creating.ReadyMeaning.boundRequest known) (Creating.ReadyMeaning.savedPlan known) prefixRetry
        ... | refl with remainder
        ... | X.completed [] (E.returned _) (X.unchanged _) = cachedCutMeaning requested before baseline scope current original raw
          prefix cut decoded readState observed
        joinKnown requested before baseline scope current after reply prefix cut decoded reserved known readState retry
          | middle , prepared , prefixRetry , remainder | Creating.knownPolicyDialogue fault policy possible
          with Creating.completedDecodedExistingUnchanged requested (Creating.Context.call scope) current middle
            (Creating.needsInput fault) (Creating.Context.original scope) (Creating.Context.raw scope)
            decoded (Creating.ReadyMeaning.boundRequest known) (Creating.ReadyMeaning.savedPlan known) prefixRetry
        ... | refl with remainder
        ... | X.completed [] (E.returned _) (X.unchanged _) = policyCutMeaning requested before baseline scope current fault
          prefix cut decoded policy possible

        joinPublishing : ∀ requested before baseline scope current after reply →
          Creating.X.Completed (Creating.script requested) before baseline (Creating.ready scope) →
          Body.X.Interrupted scope (Body.script scope (bodyInput scope)) baseline current →
          X.Completed (script requested) current after reply → Meaning requested before after reply
        joinPublishing requested before baseline scope current after reply prefix cut retry =
          joinKnown requested before baseline scope current after reply prefix cut (proj₁ original)
            (reservationAtCut (Creating.Context.call scope) baseline current
              (Creating.completedReadyReservation requested (Creating.Context.call scope) before baseline scope (proj₁ original) prefix)
              (proj₁ metadata))
            (readyAtCut scope baseline current (proj₂ original) metadata)
            (readbackAtCut requested before baseline scope current prefix cut) retry
          where
          original = initialReady requested before baseline scope prefix
          metadata = Replay.bodyMetadata (bodyWriter scope) (Creating.Call.token (Creating.Context.call scope)) baseline current cut

        converges : ∀ requested before current after reply → X.Interrupted (script requested) before current →
          X.Completed (script requested) current after reply → Meaning requested before after reply
        converges requested before current after reply cut retry
          with splitInterruptedPrefix (Creating.script requested) before current cut
        ... | preparing prefixCut with splitPrefixRun (Creating.script requested) current after reply
          (X.Completed.returned retry) (X.Completed.changes retry)
        ... | baseline , prepared , prefixRetry , remainder = prefixThenBodyMeaning requested before baseline after prepared reply
          (Creating.converges requested before current baseline prepared prefixCut prefixRetry) remainder
        converges requested before current after reply cut retry | publishing baseline scope prefix bodyCut =
          joinPublishing requested before baseline scope current after reply prefix bodyCut retry

        recoverable : Recovery.RecoverableFor Store.World Creating.Request Response Meaning
        recoverable = record { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic; converges = converges; progress = progress }

        Succeeded : Response → Set
        Succeeded (needsInput _) = ⊥
        Succeeded (returned (Creating.Read.completed _ _)) = ⊤
        Succeeded (returned _) = ⊥
        Succeeded (executed scope reply) = Success (bodyKind scope) reply
    open Implementation public using (Response; needsInput; returned; executed; Meaning; preparationDialogue; preparationReadback; businessOutcome; cachedBusinessOutcome; Effect; prepare; publish; Reply; Atomic; module X; module E; script; progress; converges; recoverable; Succeeded; bodyKind; bodyInput; bodyWriter; bodyName; bodyCertificate; bodyOperation; module Body)

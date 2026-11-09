{-# OPTIONS --safe #-}
-- The real registered backfill is assembled from its actual metadata prefix
-- and its checked repeated vector publications. Neither branch admits a raw
-- application script or an operation-selected physical interpretation.
module Mimir.BackfillOperationRecovery where

open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import Mimir.ApplicationStore as Store
import Mimir.BackfillRecovery as Backfill
import Mimir.BackfillPreparationRecovery as Prefix
import Mimir.OperationControls as Controls
import Mimir.PublicEncoding as Public
import Mimir.RecoverableStoreStep as Step
import Mimir.Recovery as Recovery
import Mimir.StandardLibrary as Library
import Mimir.Validation as Validation

module Registered (library : Library.Contract) (format : Public.Formatting)
  (prefixPostgres : Prefix.PostgreSQL library format)
  (bodyPostgres : Controls.PostgreSQL) (encoding : Backfill.JournalEncoding library) where
  module A = Backfill.Admission library
  module P = Prefix.Registered library format prefixPostgres
  module B (scope : A.Context) = Backfill.Body library bodyPostgres encoding scope

  Input = Prefix.Input
  Result = Step.Result Validation.Fault

  data Effect : Set where
    prepare : P.Effect → Effect
    publish : (scope : A.Context) → B.Effect scope → Effect

  Reply : Effect → Set
  Reply (prepare effect) = P.Reply effect
  Reply (publish scope effect) = B.Reply scope effect

  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before (prepare effect) reply after = P.Atomic before effect reply after
  Atomic before (publish scope effect) reply after = B.Atomic scope before effect reply after

  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  liftPrefix : ∀ {R} → P.E.Script R → E.Script R
  liftPrefix (P.E.done result) = E.done result
  liftPrefix (P.E.ask effect continuation) = E.ask (prepare effect) (λ reply → liftPrefix (continuation reply))

  liftBody : ∀ scope {R} → B.E.Script scope R → E.Script R
  liftBody scope (B.E.done result) = E.done result
  liftBody scope (B.E.ask effect continuation) =
    E.ask (publish scope effect) (λ reply → liftBody scope (continuation reply))

  prefixEvent : P.E.Event → E.Event
  prefixEvent (effect , reply) = prepare effect , reply

  bodyEvent : ∀ scope → B.E.Event scope → E.Event
  bodyEvent scope (effect , reply) = publish scope effect , reply

  prefixRuns : ∀ {R} {program : P.E.Script R} {events result} →
    P.E.Runs program events result → E.Runs (liftPrefix program) (map prefixEvent events) result
  prefixRuns (P.E.returned result) = E.returned result
  prefixRuns (P.E.replied effect continuation reply rest) =
    E.replied (prepare effect) (λ observed → liftPrefix (continuation observed)) reply (prefixRuns rest)

  bodyRuns : ∀ scope {R} {program : B.E.Script scope R} {events result} →
    B.E.Runs scope program events result → E.Runs (liftBody scope program) (map (bodyEvent scope) events) result
  bodyRuns scope (B.E.returned result) = E.returned result
  bodyRuns scope (B.E.replied effect continuation reply rest) =
    E.replied (publish scope effect) (λ observed → liftBody scope (continuation observed)) reply (bodyRuns scope rest)

  prefixChanges : ∀ {before events after} → P.X.Changes before events after →
    X.Changes before (map prefixEvent events) after
  prefixChanges (P.X.unchanged before) = X.unchanged before
  prefixChanges (P.X.changed before effect reply middle physical rest) =
    X.changed before (prepare effect) reply middle physical (prefixChanges rest)

  bodyChanges : ∀ scope {before events after} → B.X.Changes scope before events after →
    X.Changes before (map (bodyEvent scope) events) after
  bodyChanges scope (B.X.unchanged before) = X.unchanged before
  bodyChanges scope (B.X.changed before effect reply middle physical rest) =
    X.changed before (publish scope effect) reply middle physical (bodyChanges scope rest)

  afterPreparation : P.Result → E.Script Result
  afterPreparation (P.ready scope) = liftBody scope (B.script scope tt)
  afterPreparation (P.stopped reply) = E.done reply

  script : Input → E.Script Result
  script request = E._>>=_ (liftPrefix (P.script request)) afterPreparation

  -- The complete business condition permits precisely the owned metadata
  -- preparation and the checked vector/answer changes. A stopped preparation
  -- cannot claim successful embedding. Once a durable plan exists, its
  -- canonical readback fixes the body selection and original model.
  data Goal (request : Input) (original final : Store.World) (reply : Result) : Set where
    metadataOnly : P.Frame request original final → P.ReplyMeaning request final (P.stopped reply) → Goal request original final reply
    backfillPublished : ∀ baseline scope → P.Frame request original baseline →
      A.original (Prefix.Input.token request) (Step.registration baseline) ≡ inj₂ scope →
      B.Goal scope tt baseline final reply → Goal request original final reply

  afterPreparationProgress : ∀ prepared before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (afterPreparation prepared) before after reply))
  afterPreparationProgress (P.ready scope) before with B.progress scope tt before
  ... | after , reply , B.X.completed events execution changes =
    after , reply , X.completed (map (bodyEvent scope) events) (bodyRuns scope execution) (bodyChanges scope changes)
  afterPreparationProgress (P.stopped reply) before =
    before , reply , X.completed [] (E.returned reply) (X.unchanged before)

  progress : ∀ request before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (script request) before after reply))
  progress request before with P.progress request before
  ... | middle , prepared , P.X.completed prefixEvents prefixExecution prefixPhysical
    with afterPreparationProgress prepared middle
  ... | after , reply , X.completed bodyEvents bodyExecution bodyPhysical =
    after , reply , X.completed _
      (E.bindRuns (prefixRuns prefixExecution) bodyExecution)
      (X.changesAppend (prefixChanges prefixPhysical) bodyPhysical)

  -- Decompose the actual combined execution at the point where its prefix
  -- returned. Physical changes travel with both halves; a control trace alone
  -- cannot certify either half of the assembled operation.
  splitPrefixRun : ∀ (program : P.E.Script P.Result) before after result {events} →
    E.Runs (E._>>=_ (liftPrefix program) afterPreparation) events result →
    X.Changes before events after →
    Σ Store.World (λ middle → Σ P.Result (λ prepared →
      P.X.Completed program before middle prepared ×
      X.Completed (afterPreparation prepared) middle after result))
  splitPrefixRun (P.E.done prepared) before after result execution changes =
    before , prepared , P.X.completed [] (P.E.returned prepared) (P.X.unchanged before) ,
    X.completed _ execution changes
  splitPrefixRun (P.E.ask effect continuation) before after result
    (E.replied .(prepare effect) _ reply execution)
    (X.changed .before .(prepare effect) .reply next physical changes)
    with splitPrefixRun (continuation reply) next after result execution changes
  ... | middle , prepared , P.X.completed events prefixExecution prefixPhysical , completedBody =
    middle , prepared ,
    P.X.completed ((effect , reply) ∷ events)
      (P.E.replied effect continuation reply prefixExecution)
      (P.X.changed before effect reply next physical prefixPhysical) , completedBody

  unliftBodyRun : ∀ scope {R} (program : B.E.Script scope R) before after result {events} →
    E.Runs (liftBody scope program) events result → X.Changes before events after →
    B.X.Completed scope program before after result
  unliftBodyRun scope (B.E.done value) before .before .value
    (E.returned .value) (X.unchanged .before) = B.X.completed [] (B.E.returned value) (B.X.unchanged before)
  unliftBodyRun scope (B.E.ask effect continuation) before after result
    (E.replied .(publish scope effect) _ reply execution)
    (X.changed .before .(publish scope effect) .reply middle physical changes)
    with unliftBodyRun scope (continuation reply) middle after result execution changes
  ... | B.X.completed events bodyExecution bodyPhysical = B.X.completed ((effect , reply) ∷ events)
    (B.E.replied effect continuation reply bodyExecution)
    (B.X.changed before effect reply middle physical bodyPhysical)

  prependPrefixInterruption : ∀ before effect (continuation : P.Reply effect → P.E.Script P.Result) reply middle after →
    P.Atomic before effect reply middle → P.X.Interrupted (continuation reply) middle after →
    P.X.Interrupted (P.E.ask effect continuation) before after
  prependPrefixInterruption before effect continuation reply middle after physical
    (P.X.atPrefix events residual .after prefix changes) =
    P.X.atPrefix ((effect , reply) ∷ events) residual after (P.E.replied effect continuation reply prefix)
      (P.X.changed before effect reply middle physical changes)
  prependPrefixInterruption before effect continuation reply middle after physical
    (P.X.beforeReply events active next current observed .after prefix changes activePhysical) =
    P.X.beforeReply ((effect , reply) ∷ events) active next current observed after
      (P.E.replied effect continuation reply prefix) (P.X.changed before effect reply middle physical changes) activePhysical

  prependBodyInterruption : ∀ scope before effect (continuation : B.Reply scope effect → B.E.Script scope Result) reply middle after →
    B.Atomic scope before effect reply middle → B.X.Interrupted scope (continuation reply) middle after →
    B.X.Interrupted scope (B.E.ask effect continuation) before after
  prependBodyInterruption scope before effect continuation reply middle after physical
    (B.X.atPrefix events residual .after prefix changes) =
    B.X.atPrefix ((effect , reply) ∷ events) residual after (B.E.replied effect continuation reply prefix)
      (B.X.changed before effect reply middle physical changes)
  prependBodyInterruption scope before effect continuation reply middle after physical
    (B.X.beforeReply events active next current observed .after prefix changes activePhysical) =
    B.X.beforeReply ((effect , reply) ∷ events) active next current observed after
      (B.E.replied effect continuation reply prefix) (B.X.changed before effect reply middle physical changes) activePhysical

  doneInterruptedSameWorld : ∀ (value : Result) before after → X.Interrupted (E.done value) before after → after ≡ before
  doneInterruptedSameWorld value before .before
    (X.atPrefix .[] .(E.done value) .before (E.stopped _) (X.unchanged .before)) = refl
  doneInterruptedSameWorld value before after (X.beforeReply events effect continuation current reply .after () changes physical)

  unliftBodyInterrupted : ∀ scope (program : B.E.Script scope Result) before after →
    X.Interrupted (liftBody scope program) before after → B.X.Interrupted scope program before after
  unliftBodyInterrupted scope (B.E.done value) before after interrupted
    rewrite doneInterruptedSameWorld value before after interrupted =
    B.X.atPrefix [] (B.E.done value) before (B.E.stopped _) (B.X.unchanged before)
  unliftBodyInterrupted scope (B.E.ask effect continuation) before .before
    (X.atPrefix .[] ._ .before (E.stopped _) (X.unchanged .before)) =
    B.X.atPrefix [] (B.E.ask effect continuation) before (B.E.stopped _) (B.X.unchanged before)
  unliftBodyInterrupted scope (B.E.ask effect continuation) before after
    (X.atPrefix ._ residual .after (E.replied .(publish scope effect) _ reply prefix)
      (X.changed .before .(publish scope effect) .reply middle physical changes)) =
    prependBodyInterruption scope before effect continuation reply middle after physical
      (unliftBodyInterrupted scope (continuation reply) middle after (X.atPrefix _ residual after prefix changes))
  unliftBodyInterrupted scope (B.E.ask effect continuation) before after
    (X.beforeReply .[] .(publish scope effect) ._ .before reply .after (E.stopped _) (X.unchanged .before) physical) =
    B.X.beforeReply [] effect continuation before reply after (B.E.stopped _) (B.X.unchanged before) physical
  unliftBodyInterrupted scope (B.E.ask effect continuation) before after
    (X.beforeReply ._ active next current observed .after (E.replied .(publish scope effect) _ reply prefix)
      (X.changed .before .(publish scope effect) .reply middle physical changes) activePhysical) =
    prependBodyInterruption scope before effect continuation reply middle after physical
      (unliftBodyInterrupted scope (continuation reply) middle after
        (X.beforeReply _ active next current observed after prefix changes activePhysical))

  data InterruptedPhase (program : P.E.Script P.Result) (before after : Store.World) : Set where
    preparing : P.X.Interrupted program before after → InterruptedPhase program before after
    publishing : ∀ baseline scope → P.X.Completed program before baseline (P.ready scope) →
      B.X.Interrupted scope (B.script scope tt) baseline after → InterruptedPhase program before after

  prependPhase : ∀ before effect continuation reply middle after → P.Atomic before effect reply middle →
    InterruptedPhase (continuation reply) middle after → InterruptedPhase (P.E.ask effect continuation) before after
  prependPhase before effect continuation reply middle after physical (preparing interrupted) =
    preparing (prependPrefixInterruption before effect continuation reply middle after physical interrupted)
  prependPhase before effect continuation reply middle after physical
    (publishing baseline scope (P.X.completed events execution changes) interrupted) =
    publishing baseline scope (P.X.completed ((effect , reply) ∷ events)
      (P.E.replied effect continuation reply execution) (P.X.changed before effect reply middle physical changes)) interrupted

  splitInterruptedPrefix : ∀ (program : P.E.Script P.Result) before after →
    X.Interrupted (E._>>=_ (liftPrefix program) afterPreparation) before after → InterruptedPhase program before after
  splitInterruptedPrefix (P.E.done (P.ready scope)) before after interrupted =
    publishing before scope (P.X.completed [] (P.E.returned (P.ready scope)) (P.X.unchanged before))
      (unliftBodyInterrupted scope (B.script scope tt) before after interrupted)
  splitInterruptedPrefix (P.E.done (P.stopped reply)) before after interrupted
    rewrite doneInterruptedSameWorld reply before after interrupted =
    preparing (P.X.atPrefix [] (P.E.done (P.stopped reply)) before (P.E.stopped _) (P.X.unchanged before))
  splitInterruptedPrefix (P.E.ask effect continuation) before .before
    (X.atPrefix .[] ._ .before (E.stopped _) (X.unchanged .before)) =
    preparing (P.X.atPrefix [] (P.E.ask effect continuation) before (P.E.stopped _) (P.X.unchanged before))
  splitInterruptedPrefix (P.E.ask effect continuation) before after
    (X.atPrefix ._ residual .after (E.replied .(prepare effect) _ reply prefix)
      (X.changed .before .(prepare effect) .reply middle physical changes)) =
    prependPhase before effect continuation reply middle after physical
      (splitInterruptedPrefix (continuation reply) middle after (X.atPrefix _ residual after prefix changes))
  splitInterruptedPrefix (P.E.ask effect continuation) before after
    (X.beforeReply .[] .(prepare effect) ._ .before reply .after (E.stopped _) (X.unchanged .before) physical) =
    preparing (P.X.beforeReply [] effect continuation before reply after (P.E.stopped _) (P.X.unchanged before) physical)
  splitInterruptedPrefix (P.E.ask effect continuation) before after
    (X.beforeReply ._ active next current observed .after (E.replied .(prepare effect) _ reply prefix)
      (X.changed .before .(prepare effect) .reply middle physical changes) activePhysical) =
    prependPhase before effect continuation reply middle after physical
      (splitInterruptedPrefix (continuation reply) middle after
        (X.beforeReply _ active next current observed after prefix changes activePhysical))

  prefixThenBodyGoal : ∀ request original baseline final prepared reply →
    P.Goal request original baseline prepared → X.Completed (afterPreparation prepared) baseline final reply →
    Goal request original final reply
  prefixThenBodyGoal request original baseline final (P.ready scope) reply (frame , canonical , noCancellation)
    (X.completed events execution changes) = backfillPublished baseline scope frame canonical
      (Recovery.RecoverableFor.completedMeetsGoal (B.operation scope) tt baseline final reply
        (unliftBodyRun scope (B.script scope tt) baseline final reply execution changes))
  prefixThenBodyGoal request original baseline .baseline (P.stopped reply) .reply (frame , certified)
    (X.completed .[] (E.returned .reply) (X.unchanged .baseline)) =
    metadataOnly frame certified

  afterBodyInterruption : ∀ request original baseline scope interrupted middle prepared final reply →
    P.X.Completed (P.script request) original baseline (P.ready scope) →
    B.X.Interrupted scope (B.script scope tt) baseline interrupted →
    P.X.Completed (P.script request) interrupted middle prepared →
    X.Completed (afterPreparation prepared) middle final reply → Goal request original final reply
  afterBodyInterruption request original baseline scope interrupted middle prepared final reply
    preparedOriginal interruptedBody preparedRetry completedRetry
    with P.replayReady request interrupted scope currentCanonical currentNoCancellation preparedRetry
    where
    originalGoal = Recovery.RecoverableFor.completedMeetsGoal P.operation request original baseline (P.ready scope) preparedOriginal
    originalCanonical = proj₁ (proj₂ originalGoal)
    originalNoCancellation = proj₂ (proj₂ originalGoal)
    invariant = B.interruptionsKeepInvariant scope baseline interrupted interruptedBody
    frame = proj₁ invariant
    currentCanonical = trans
      (cong (A.original (Prefix.Input.token request))
        (Backfill.frameKeepsRegistration (A.Context.token scope) (A.keys scope) (A.selected scope) baseline interrupted frame))
      originalCanonical
    currentNoCancellation = trans
      (cong (λ world → Store.lookupCancellation world (Prefix.Input.token request)) (Backfill.Frame.otherFields frame))
      originalNoCancellation
  ... | refl , refl = backfillPublished baseline scope
    (proj₁ (Recovery.RecoverableFor.completedMeetsGoal P.operation request original baseline (P.ready scope) preparedOriginal))
    (proj₁ (proj₂ (Recovery.RecoverableFor.completedMeetsGoal P.operation request original baseline (P.ready scope) preparedOriginal)))
    (B.converges scope tt baseline interrupted final reply interruptedBody
      (unliftBodyRun scope (B.script scope tt) interrupted final reply
        (X.Completed.returned completedRetry) (X.Completed.changes completedRetry)))

  converges : ∀ request original interrupted final reply → X.Interrupted (script request) original interrupted →
    X.Completed (script request) interrupted final reply → Goal request original final reply
  converges request original interrupted final reply interruptedRun completedRun
    with splitInterruptedPrefix (P.script request) original interrupted interruptedRun |
      splitPrefixRun (P.script request) interrupted final reply (X.Completed.returned completedRun) (X.Completed.changes completedRun)
  ... | preparing preparingCut | baseline , prepared , preparedRetry , completedBody =
    prefixThenBodyGoal request original baseline final prepared reply
      (P.converges request original interrupted baseline prepared preparingCut preparedRetry) completedBody
  ... | publishing baseline scope preparedOriginal interruptedBody | middle , prepared , preparedRetry , completedBody =
    afterBodyInterruption request original baseline scope interrupted middle prepared final reply
      preparedOriginal interruptedBody preparedRetry completedBody

  operation : Recovery.RecoverableFor Store.World Input Result Goal
  operation = record
    { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic
    ; converges = converges; progress = progress }

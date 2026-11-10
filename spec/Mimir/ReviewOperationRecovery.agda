{-# OPTIONS --safe #-}
-- The registered review is assembled from its original owner journal,
-- complete required preparation and one atomic business publication.
-- Physical effects retain their concrete database and provider semantics.
module Mimir.ReviewOperationRecovery where

open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Integer using (ℤ)
import Data.List.Properties as Lists
import Mimir.LearningInput as LearningInput
import Mimir.StructuredValue as Wire
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.Float.Base using (Float)
open import Mimir.Text using (Text)
import Mimir.PosteriorComputation as Posterior
import Mimir.LearningOperations as Operations
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import Mimir.ApplicationStore as Store
import Mimir.ReviewPublicationRecovery as Review
import Mimir.ReviewPreparationRecovery as Prefix
import Mimir.OperationControls as Controls
import Mimir.PublicEncoding as Encoding
import Mimir.RecoverableStoreStep as Step
import Mimir.Recovery as Recovery
import Mimir.StandardLibrary as Library
import Mimir.Validation as Validation

module Registered (library : Library.Contract) (format : Encoding.Formatting)
  (database : ℕ) (databaseSum : List Float → Float)
  (calculator : Posterior.Calculator) (dependencies : Review.Dependencies)
  (codec : Prefix.AllocationEncoding.Codec format) (postgres : Controls.PostgreSQL)
  (backend : Store.World → Review.Preparing.Claim → Text ⊎ List Store.Vector) where
  module Raw = Prefix.Registered library format database databaseSum calculator dependencies codec postgres
  module P where
    open Raw public

    record ReadyMeaning (identity : ℕ) (after : Store.World) (scope : Context) : Set where
      field ownToken : Context.token scope ≡ identity
            originalTime : ℤ
            originalRequest : Final.original identity (Step.registration after) ≡ inj₂ (Context.request scope , originalTime)
            originalRows : Recorded identity after (Context.allocations scope)
            allDeclarations : map proj₁ (Context.allocations scope) ≡ keys (LearningInput.Review.candidates (Review.Request.original (Context.request scope)))
            completeJournal : J.Complete identity after (Final.ownerSteps (LearningInput.Review.candidates (Review.Request.original (Context.request scope))))
            completeCursor : J.Cursor identity after (Final.ownerSteps (LearningInput.Review.candidates (Review.Request.original (Context.request scope)))) []
            distinctAddresses : Controls.Addressing (Final.ownerSteps (LearningInput.Review.candidates (Review.Request.original (Context.request scope))))

    data ReplyMeaning (identity : ℕ) (after : Store.World) : Result → Set where
      readyOwners : ∀ scope → ReadyMeaning identity after scope → ReplyMeaning identity after (ready scope)
      inspectionStopped : ∀ current reply → inspect current identity after ≡ stop reply → ReplyMeaning identity after (stopped reply)
      ownerStopped : ∀ requested observed reply → OwnerPause identity requested observed after reply → ReplyMeaning identity after (stopped reply)

    Goal : ℕ → Store.World → Store.World → Result → Set
    Goal identity before after reply = Frame identity before after × ReplyMeaning identity after reply

    allSteps : Review.Request → List Controls.Plan.Step
    allSteps requested = Final.ownerSteps (LearningInput.Review.candidates (Review.Request.original requested))

    sameKeys : ∀ {first second : List Text} → first ≡ second → map declared first ≡ map declared second
    sameKeys refl = refl

    advanceKeys : ∀ (earlier : List (Text × Store.EmbeddingOwnerRow)) (key : Text) (row : Store.EmbeddingOwnerRow) (remaining complete : List Text) →
      map proj₁ earlier ++ (key ∷ remaining) ≡ complete →
      map proj₁ (earlier ++ ((key , row) ∷ [])) ++ remaining ≡ complete
    advanceKeys earlier key row remaining complete previous = trans
      (cong (_++ remaining) (Lists.map-++ proj₁ earlier ((key , row) ∷ [])))
      (trans (Lists.++-assoc (map proj₁ earlier) (key ∷ []) remaining) previous)

    walkMeaning : ∀ identity requested time remaining earlier before after reply →
      Final.original identity (Step.registration before) ≡ inj₂ (requested , time) →
      J.Complete identity before (allSteps requested) → Controls.Addressing (allSteps requested) →
      J.Cursor identity before (allSteps requested) (map declared remaining) →
      Recorded identity before earlier →
      map proj₁ earlier ++ remaining ≡ keys (LearningInput.Review.candidates (Review.Request.original requested)) →
      X.Completed (walk identity requested remaining earlier) before after reply → ReplyMeaning identity after reply

    afterLegal : ∀ identity requested time candidateKey remaining earlier observed before after reply final result →
      Final.original identity (Step.registration before) ≡ inj₂ (requested , time) →
      J.Complete identity before (allSteps requested) → Controls.Addressing (allSteps requested) →
      J.Cursor identity before (allSteps requested) (declared candidateKey ∷ map declared remaining) →
      Recorded identity before earlier →
      map proj₁ earlier ++ (candidateKey ∷ remaining) ≡ keys (LearningInput.Review.candidates (Review.Request.original requested)) →
      Frame identity before after → OwnerLegal identity requested candidateKey observed before after reply →
      X.Completed (afterOwner identity requested candidateKey remaining earlier (observed , reply)) after final result →
      ReplyMeaning identity final result

    walkMeaning identity requested time [] earlier before .before .(ready (context identity requested earlier))
      original journal addresses cursor priorRows earlierKeys (X.completed [] (E.returned _) (X.unchanged _)) =
      readyOwners _ record
        { ownToken = refl; originalTime = time; originalRequest = original; originalRows = priorRows
        ; allDeclarations = trans (sym (Lists.++-identityʳ (map proj₁ earlier))) earlierKeys
        ; completeJournal = journal; completeCursor = cursor; distinctAddresses = addresses }
    walkMeaning identity requested time (candidateKey ∷ remaining) earlier before final result
      original journal addresses cursor priorRows earlierKeys
      (X.completed _ (E.replied _ _ (observed , reply) execution) (X.changed _ _ _ after physical changes)) =
      afterLegal identity requested time candidateKey remaining earlier observed before after reply final result
        original journal addresses cursor priorRows earlierKeys (atomicFrame before (reserve identity candidateKey) (observed , reply) after physical)
        (subst (λ outcome → OwnerLegal identity requested candidateKey observed before (proj₁ outcome) (proj₂ outcome))
          (sym (ownerObservation identity candidateKey observed reply before after physical))
          (executeLegal observed identity candidateKey requested time before original journal addresses (map declared remaining) cursor))
        (X.completed _ execution changes)

    afterLegal identity requested time candidateKey remaining earlier observed before after .(Step.done raw) final result
      original journal addresses cursor priorRows earlierKeys frame (readable raw value .after known decoded) completion
      rewrite decoded = walkMeaning identity requested time remaining (earlier ++ ((candidateKey , Prefix.owner identity value) ∷ []))
        after final result nextOriginal nextJournal addresses nextCursor nextRecorded
        (advanceKeys earlier candidateKey (Prefix.owner identity value) remaining _ earlierKeys) completion
      where
      nextOriginal = trans (cong (Final.original identity) (Frame.originalRegistration frame)) original
      nextJournal = Frame.validPrefix frame requested time original journal
      kept = Frame.originalAnswers frame identity
      nextCursor = J.advanceCursor identity after (allSteps requested) (declared candidateKey) (map declared remaining) raw
        (J.transportCursor identity before after (allSteps requested) (declared candidateKey ∷ map declared remaining) kept cursor) known
      nextRecorded = appendRecorded identity after earlier ((candidateKey , Prefix.owner identity value) ∷ [])
        (keepRecorded identity before after earlier kept priorRows) (recorded candidateKey value raw [] known decoded noOwners)
    afterLegal identity requested time candidateKey remaining earlier observed before .before reply .before .(stopped reply)
      original journal addresses cursor priorRows earlierKeys frame (paused .reply cause@(cancellationObserved receipt known))
      (X.completed [] (E.returned _) (X.unchanged _)) = ownerStopped requested observed reply cause
    afterLegal identity requested time candidateKey remaining earlier observed before .before reply .before .(stopped reply)
      original journal addresses cursor priorRows earlierKeys frame (paused .reply cause@(sourceRefused fault known))
      (X.completed [] (E.returned _) (X.unchanged _)) = ownerStopped requested observed reply cause
    afterLegal identity requested time candidateKey remaining earlier observed before .before reply .before .(stopped reply)
      original journal addresses cursor priorRows earlierKeys frame (paused .reply cause@(allocationUnavailable fault known))
      (X.completed [] (E.returned _) (X.unchanged _)) = ownerStopped requested observed reply cause
    afterLegal identity requested time candidateKey remaining earlier observed before .before reply .before .(stopped reply)
      original journal addresses cursor priorRows earlierKeys frame (paused .reply cause@(projectRefused receipt project observedEq source different))
      (X.completed [] (E.returned _) (X.unchanged _)) = ownerStopped requested observed reply cause

    inspectionMeaning : ∀ identity current before after reply →
      X.Completed (afterInspection identity (current , before)) before after reply → ReplyMeaning identity after reply
    inspectionMeaning identity current before after reply completion with inspect current identity before in decision
    ... | stop reply₀ with completion
    ... | X.completed [] (E.returned _) (X.unchanged _) = inspectionStopped current reply₀ decision
    inspectionMeaning identity current before after reply completion | run requested =
      walkMeaning identity requested (Admitted.time admission) (keys candidates) [] before after reply
        (Admitted.original admission) (Admitted.journal admission) (Admitted.addresses admission)
        (subst (J.Cursor identity before (allSteps requested)) (ownerStepsAsKeys candidates) (J.here (allSteps requested)))
        noOwners refl completion
      where
      admission = inspectAdmitted current identity before requested decision
      candidates = LearningInput.Review.candidates (Review.Request.original requested)

    completedMeaning : ∀ identity before after reply → X.Completed (script identity) before after reply → ReplyMeaning identity after reply
    completedMeaning identity before after reply
      (X.completed _ (E.replied _ _ (current , .before) execution) (X.changed _ _ _ .before (refl , refl) changes)) =
      inspectionMeaning identity current before after reply (X.completed _ execution changes)

    completedGoal : ∀ identity before after reply → X.Completed (script identity) before after reply → Goal identity before after reply
    completedGoal identity before after reply completion = completedFrame identity before after reply completion , completedMeaning identity before after reply completion

    converges : ∀ identity before interrupted after reply → X.Interrupted (script identity) before interrupted →
      X.Completed (script identity) interrupted after reply → Goal identity before after reply
    converges identity before interrupted after reply interruption completion =
      composeFrame identity before interrupted after (interruptedFrame identity before interrupted interruption)
        (completedFrame identity interrupted after reply completion) , completedMeaning identity interrupted after reply completion

    operation : Environment → Recovery.RecoverableFor Store.World ℕ Result Goal
    operation environment = record
      { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic
      ; converges = converges; progress = progress environment }

  module B (scope : P.Context) = Review.AfterOwners library format database databaseSum calculator dependencies
    (P.Context.token scope) (P.Context.request scope) (P.Context.allocations scope) backend

  module F = Review.FinalBody library format database databaseSum calculator dependencies
  Input = ℕ
  Result = F.Saved.Reply

  data Effect : Set where
    prepare : P.Effect → Effect
    publish : (scope : P.Context) → B.Effect scope → Effect

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

  mapStopped : Step.Result Validation.Fault → Result
  mapStopped (Step.done value) = Step.done value
  mapStopped (Step.needsInput fault) = Step.needsInput (inj₁ fault)
  mapStopped Step.needsRecovery = Step.needsRecovery
  mapStopped (Step.cancelled cancellation) = Step.cancelled cancellation

  afterPreparation : P.Result → E.Script Result
  afterPreparation (P.ready scope) = liftBody scope (B.script scope)
  afterPreparation (P.stopped reply) = E.done (mapStopped reply)

  script : Input → E.Script Result
  script request = E._>>=_ (liftPrefix (P.script request)) afterPreparation

  -- An owner prefix may change only its owned metadata. A review outcome is
  -- then governed by the fixed full-store publication meaning, including every
  -- required prepared belief, its indexed support and numerical consequences.
  data Goal (request : Input) (original final : Store.World) (reply : Result) : Set where
    metadataOnly : ∀ stopped → P.Goal request original final (P.stopped stopped) →
      reply ≡ mapStopped stopped → Goal request original final reply
    reviewPublished : ∀ baseline scope → P.Goal request original baseline (P.ready scope) →
      B.Goal scope baseline final reply → Goal request original final reply

  afterPreparationProgress : ∀ prepared before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (afterPreparation prepared) before after reply))
  afterPreparationProgress (P.ready scope) before with B.progress scope before
  ... | after , reply , B.X.completed events execution changes =
    after , reply , X.completed (map (bodyEvent scope) events) (bodyRuns scope execution) (bodyChanges scope changes)
  afterPreparationProgress (P.stopped reply) before =
    before , mapStopped reply , X.completed [] (E.returned (mapStopped reply)) (X.unchanged before)

  progress : P.Environment → ∀ request before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (script request) before after reply))
  progress environment request before with P.progress environment request before
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
      B.X.Interrupted scope (B.script scope) baseline after → InterruptedPhase program before after

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
      (unliftBodyInterrupted scope (B.script scope) before after interrupted)
  splitInterruptedPrefix (P.E.done (P.stopped reply)) before after interrupted
    rewrite doneInterruptedSameWorld (mapStopped reply) before after interrupted =
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
  prefixThenBodyGoal request original baseline final (P.ready scope) reply ownerGoal
    (X.completed events execution changes) = reviewPublished baseline scope ownerGoal
      (B.completedGoal scope baseline final reply
        (unliftBodyRun scope (B.script scope) baseline final reply execution changes))
  prefixThenBodyGoal request original baseline .baseline (P.stopped raw) .(mapStopped raw) ownerGoal
    (X.completed [] (E.returned _) (X.unchanged _)) = metadataOnly raw ownerGoal refl

  afterUnpublishedPreparation : ∀ request original baseline scope middle prepared final reply →
    P.X.Completed (P.script request) original baseline (P.ready scope) →
    P.X.Completed (P.script request) baseline middle prepared →
    X.Completed (afterPreparation prepared) middle final reply → Goal request original final reply
  afterUnpublishedPreparation request original baseline scope middle prepared final reply originalOwners retryOwners retryBody =
    prefixThenBodyGoal request original middle final prepared reply
      (P.converges request original baseline middle prepared
        (P.X.completedRunMayLoseFinalReply (P.script request) original baseline (P.ready scope) originalOwners) retryOwners)
      retryBody

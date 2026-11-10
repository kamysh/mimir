{-# OPTIONS --safe #-}
-- The registered review is assembled from its original owner journal,
-- complete required preparation and one atomic business publication.
-- Physical effects retain their concrete database and provider semantics.
module Mimir.ReviewOperationRecovery where

open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Integer using (ℤ)
import Data.List.Properties as Lists
import Data.List.Relation.Unary.All
import Mimir.LearningInput as LearningInput
import Mimir.StructuredValue as Wire
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.Float.Base using (Float)
open import Mimir.Text using (Text)
open import Data.String using (toList)
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

  -- Cached completion uses only the real owner-prefix inspection. The
  -- observed host settings cannot restart owners, embedding or publication.
  cachedReplay : ∀ (environment : P.Environment) token current binding raw →
    P.Readback.admission (toList "review_experience") token current ≡
      P.Readback.returned (P.Readback.completed binding raw) →
    X.Completed (script token) current current (Step.done raw)
  cachedReplay environment token current binding raw known = X.completed
    ((prepare (P.inspectOwners token) , (settings , current)) ∷ [])
    (E.bindRuns (prefixRuns prefixRun) (E.returned _))
    (X.changed current _ _ current (refl , refl) (X.unchanged current))
    where
    settings = P.Environment.currentSettings environment token current
    cachedOwners : P.E.Runs (P.afterInspection token (settings , current)) [] (P.stopped (Step.done raw))
    cachedOwners = subst (λ program → P.E.Runs program [] (P.stopped (Step.done raw)))
      (sym (P.afterCompletedReadback token settings current binding raw known)) (P.E.returned _)
    prefixRun : P.E.Runs (P.script token) ((P.inspectOwners token , (settings , current)) ∷ [])
      (P.stopped (Step.done raw))
    prefixRun = P.E.replied _ _ _ cachedOwners

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

  afterCompletedPublication : ∀ request original baseline scope interrupted middle prepared final reply value →
    P.X.Completed (P.script request) original baseline (P.ready scope) →
    B.Goal scope baseline interrupted (Step.done value) →
    middle ≡ interrupted → prepared ≡ P.stopped (Step.done value) →
    X.Completed (afterPreparation prepared) middle final reply → Goal request original final reply
  afterCompletedPublication request original baseline scope interrupted .interrupted .(P.stopped (Step.done value))
    .interrupted .(Step.done value) value originalOwners business refl refl
    (X.completed [] (E.returned _) (X.unchanged _)) = reviewPublished baseline scope
      (P.completedGoal request original baseline (P.ready scope) originalOwners) business

  afterSavedReadback : ∀ request original baseline scope interrupted middle prepared final reply value binding →
    P.X.Completed (P.script request) original baseline (P.ready scope) →
    B.Goal scope baseline interrupted (Step.done value) →
    P.Readback.admission (toList "review_experience") request interrupted ≡
      P.Readback.returned (P.Readback.completed binding value) →
    P.X.Completed (P.script request) interrupted middle prepared →
    X.Completed (afterPreparation prepared) middle final reply → Goal request original final reply
  afterSavedReadback request original baseline scope interrupted middle prepared final reply value binding
    originalOwners business saved retryOwners retryBody
    with P.completedReadback request interrupted binding value saved middle prepared retryOwners
  ... | sameWorld , sameReply = afterCompletedPublication request original baseline scope interrupted middle prepared final reply value
    originalOwners business sameWorld sameReply retryBody

  interruptedKeepsRegistration : ∀ request original interrupted →
    X.Interrupted (script request) original interrupted → Step.registration interrupted ≡ Step.registration original
  interruptedKeepsRegistration request original interrupted cut
    with splitInterruptedPrefix (P.script request) original interrupted cut
  ... | preparing partial = P.Frame.originalRegistration (P.interruptedFrame request original interrupted partial)
  ... | publishing baseline scope owners partial with B.interruptionCut scope baseline interrupted partial
  ... | B.noPublication unchanged = trans (cong Step.registration unchanged)
    (P.Frame.originalRegistration (P.completedFrame request original baseline (P.ready scope) owners))

  ... | B.published prepared packets metadata value captured ready observed = trans
    (trans (cong Step.registration (cong proj₁ observed))
      (F.executeKeepsRegistration (P.Context.token scope) (B.supplied scope packets metadata) baseline))
    (P.Frame.originalRegistration (P.completedFrame request original baseline (P.ready scope) owners))

  interruptedKeepsCancellation : ∀ wanted request original interrupted →
    X.Interrupted (script request) original interrupted →
    Store.lookupCancellation interrupted wanted ≡ Store.lookupCancellation original wanted
  interruptedKeepsCancellation wanted request original interrupted cut
    with splitInterruptedPrefix (P.script request) original interrupted cut
  ... | preparing partial = cong (λ world → Store.lookupCancellation world wanted)
    (P.Frame.business (P.interruptedFrame request original interrupted partial))
  ... | publishing baseline scope owners partial with B.interruptionCut scope baseline interrupted partial
  ... | B.noPublication unchanged = trans (cong (λ world → Store.lookupCancellation world wanted) unchanged)
    (cong (λ world → Store.lookupCancellation world wanted)
      (P.Frame.business (P.completedFrame request original baseline (P.ready scope) owners)))

  ... | B.published prepared packets metadata value captured ready observed = trans
    (trans (cong (λ world → Store.lookupCancellation world wanted) (cong proj₁ observed))
      (F.Saved.cancellationUnchanged wanted (P.Context.token scope , B.supplied scope packets metadata) baseline))
    (cong (λ world → Store.lookupCancellation world wanted)
      (P.Frame.business (P.completedFrame request original baseline (P.ready scope) owners)))

  PendingContext : ℕ → Store.World → Set
  PendingContext token current = Σ (P.Readback.ExecutionContext (toList "review_experience") token current) λ entry →
    Σ Controls.Plan.Step λ next → Controls.OpaqueJournal.next
      (Controls.OpaqueJournal.Complete.prefix (P.Readback.ExecutionContext.journal entry)) ≡ just next

  ContextProgress : ℕ → Store.World → Store.World → Set
  ContextProgress token before current = current ≡ before ⊎ PendingContext token current

  contextAt : ∀ token before current → P.Readback.ExecutionContext (toList "review_experience") token before →
    ContextProgress token before current → P.Readback.ExecutionContext (toList "review_experience") token current
  contextAt token before current entry (inj₁ same) =
    subst (P.Readback.ExecutionContext (toList "review_experience") token) (sym same) entry
  contextAt token before current entry (inj₂ (currentEntry , _)) = currentEntry

  composeContextProgress : ∀ token before middle current → ContextProgress token before middle →
    ContextProgress token middle current → ContextProgress token before current
  composeContextProgress token before middle .middle earlier (inj₁ refl) = earlier
  composeContextProgress token before middle current earlier (inj₂ pendingContext) = inj₂ pendingContext

  ownerChangeProgress : ∀ token before current → P.Readback.ExecutionContext (toList "review_experience") token before →
    P.Change token before current → ContextProgress token before current
  ownerChangeProgress token before .before entry P.stayed = inj₁ refl
  ownerChangeProgress token before current entry change@(P.added requested time original journal addresses next selected receipt source) =
    inj₂ (P.ownerJournalContext token before current entry frame requested time
      (trans (cong (P.Final.original token) (P.Frame.originalRegistration frame)) original)
      (P.Frame.validPrefix frame requested time original journal))
    where frame = P.changeFrame token before current change

  ownerAtomicProgress : ∀ token before effect reply current → P.effectToken effect ≡ token →
    P.Readback.ExecutionContext (toList "review_experience") token before → P.Atomic before effect reply current →
    ContextProgress token before current
  ownerAtomicProgress token before (P.inspectOwners .token) (settings , .before) .before refl entry (refl , refl) = inj₁ refl
  ownerAtomicProgress token before (P.reserve .token candidateKey) (observed , reply) current refl entry physical =
    subst (ContextProgress token before)
      (sym (cong proj₁ (P.ownerObservation token candidateKey observed reply before current physical)))
      (ownerChangeProgress token before _ entry (P.executeChange observed token candidateKey before))

  ownerChangesProgress : ∀ token before events current →
    Data.List.Relation.Unary.All.All (λ event → P.effectToken (proj₁ event) ≡ token) events →
    P.Readback.ExecutionContext (toList "review_experience") token before → P.X.Changes before events current →
    ContextProgress token before current
  ownerChangesProgress token before [] .before Data.List.Relation.Unary.All.[] entry (P.X.unchanged _) = inj₁ refl
  ownerChangesProgress token before ((effect , reply) ∷ events) current (Data.List.Relation.Unary.All._∷_ owned owners) entry
    (P.X.changed .before .effect .reply middle physical later) = composeContextProgress token before middle current first
      (ownerChangesProgress token middle events current owners (contextAt token before middle entry first) later)
    where first = ownerAtomicProgress token before effect reply middle owned entry physical

  ownerPrefixProgress : ∀ token before current → P.Readback.ExecutionContext (toList "review_experience") token before →
    P.X.Interrupted (P.script token) before current → ContextProgress token before current
  ownerPrefixProgress token before current entry (P.X.atPrefix events residual .current prefix changes)
    with P.prefixScoped token (P.script token) events residual (P.scriptScoped token) prefix
  ... | owners , _ = ownerChangesProgress token before events current owners entry changes
  ownerPrefixProgress token before current entry (P.X.beforeReply events effect continuation middle reply .current prefix changes physical)
    with P.prefixScoped token (P.script token) events (P.E.ask effect continuation) (P.scriptScoped token) prefix
  ... | owners , P.asked .effect .continuation owned later = composeContextProgress token before middle current first
    (ownerAtomicProgress token middle effect reply current owned (contextAt token before middle entry first) physical)
    where first = ownerChangesProgress token before events middle owners entry changes

  ownerPrefixAdmission : ∀ token before current (entry : P.Readback.ExecutionContext (toList "review_experience") token before) →
    P.Readback.admission (toList "review_experience") token before ≡ P.Readback.admitted entry →
    P.X.Interrupted (P.script token) before current →
    Σ (P.Readback.ExecutionContext (toList "review_experience") token current) λ actual →
      P.Readback.admission (toList "review_experience") token current ≡ P.Readback.admitted actual
  ownerPrefixAdmission token before current entry known cut with ownerPrefixProgress token before current entry cut
  ... | inj₁ refl = entry , known
  ... | inj₂ (derived , next , selected) = P.Readback.admissionFromPending (toList "review_experience") token current
    derived next (proj₁ pending) (proj₂ pending)
    where
    active = trans (cong (λ world → Store.lookupCancellation world token)
      (P.Frame.business (P.interruptedFrame token before current cut))) (P.entryActive token before entry known)
    pending = P.Readback.pendingAnswer (toList "review_experience") token current derived next selected active

  CompletedReadback : ℕ → Store.World → Set
  CompletedReadback token current = Σ Store.BindingRow λ binding → Σ Wire.Value λ value →
    P.Readback.admission (toList "review_experience") token current ≡ P.Readback.returned (P.Readback.completed binding value)

  interruptedReadback : ∀ token before current (entry : P.Readback.ExecutionContext (toList "review_experience") token before) →
    P.Readback.admission (toList "review_experience") token before ≡ P.Readback.admitted entry →
    X.Interrupted (script token) before current →
    (Σ (P.Readback.ExecutionContext (toList "review_experience") token current) λ actual →
      P.Readback.admission (toList "review_experience") token current ≡ P.Readback.admitted actual) ⊎ CompletedReadback token current
  interruptedReadback token before current entry known cut
    with splitInterruptedPrefix (P.script token) before current cut
  ... | preparing partial = inj₁ (ownerPrefixAdmission token before current entry known partial)
  ... | publishing baseline scope owners partial with B.interruptionCut scope baseline current partial
  ... | B.noPublication refl = inj₁ (ownerPrefixAdmission token before baseline entry known
    (P.X.completedRunMayLoseFinalReply (P.script token) before baseline (P.ready scope) owners))
  ... | B.published prepared packets metadata value captured ready observed
    with P.completedMeaning token before baseline (P.ready scope) owners
  ... | P.readyOwners .scope facts = inj₂ (proj₁ completed , value , proj₂ completed)
    where
    fixedTokenObservation = trans observed
      (cong (λ identity → F.Saved.execute (identity , B.supplied scope packets metadata) baseline) (P.ReadyMeaning.ownToken facts))
    completed = P.readyThenPublicationReadback token before baseline scope (B.supplied scope packets metadata) current value
      owners (P.ReadyMeaning.originalTime facts) (P.ReadyMeaning.originalRequest facts)
      (P.ReadyMeaning.completeJournal facts) (P.ReadyMeaning.completeCursor facts) fixedTokenObservation
  afterPublishedPreparation : ∀ request original baseline scope interrupted middle prepared final reply
    preparedBusiness packets metadata value →
    P.X.Completed (P.script request) original baseline (P.ready scope) →
    B.P.Captured scope baseline preparedBusiness → B.Ready scope preparedBusiness packets →
    (interrupted , Step.done value) ≡ F.Saved.execute (P.Context.token scope , B.supplied scope packets metadata) baseline →
    P.X.Completed (P.script request) interrupted middle prepared →
    X.Completed (afterPreparation prepared) middle final reply → Goal request original final reply
  afterPublishedPreparation request original baseline scope interrupted middle prepared final reply
    preparedBusiness packets metadata value originalOwners captured preparedReady observed retryOwners retryBody
    with P.completedMeaning request original baseline (P.ready scope) originalOwners
  ... | P.readyOwners .scope facts = afterSavedReadback request original baseline scope interrupted middle prepared final reply
    value (proj₁ completed) originalOwners
    (B.publishedGoal scope preparedBusiness packets metadata value baseline interrupted captured preparedReady observed)
    (proj₂ completed) retryOwners retryBody
    where
    fixedTokenObservation = trans observed
      (cong (λ identity → F.Saved.execute (identity , B.supplied scope packets metadata) baseline) (P.ReadyMeaning.ownToken facts))
    completed = P.readyThenPublicationReadback request original baseline scope (B.supplied scope packets metadata)
      interrupted value originalOwners (P.ReadyMeaning.originalTime facts) (P.ReadyMeaning.originalRequest facts)
      (P.ReadyMeaning.completeJournal facts) (P.ReadyMeaning.completeCursor facts) fixedTokenObservation

  converges : ∀ request original interrupted final reply → X.Interrupted (script request) original interrupted →
    X.Completed (script request) interrupted final reply → Goal request original final reply
  converges request original interrupted final reply interruptedRun completedRun
    with splitInterruptedPrefix (P.script request) original interrupted interruptedRun |
      splitPrefixRun (P.script request) interrupted final reply (X.Completed.returned completedRun) (X.Completed.changes completedRun)
  ... | preparing partial | baseline , prepared , retryOwners , retryBody =
    prefixThenBodyGoal request original baseline final prepared reply
      (P.converges request original interrupted baseline prepared partial retryOwners) retryBody
  ... | publishing baseline scope originalOwners bodyCut | middle , prepared , retryOwners , retryBody
    with B.interruptionCut scope baseline interrupted bodyCut
  ... | B.noPublication refl = afterUnpublishedPreparation request original baseline scope middle prepared final reply
    originalOwners retryOwners retryBody
  ... | B.published preparedBusiness packets metadata value captured preparedReady observed =
    afterPublishedPreparation request original baseline scope interrupted middle prepared final reply
      preparedBusiness packets metadata value originalOwners captured preparedReady observed retryOwners retryBody

  operation : P.Environment → Recovery.RecoverableFor Store.World Input Result Goal
  operation environment = record
    { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic
    ; converges = converges; progress = progress environment }

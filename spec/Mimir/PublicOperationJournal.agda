{-# OPTIONS --safe #-}
-- Actual interrupted writer traces preserve computed journal admission and
-- original registration. These laws cover the closed concrete writer families.
module Mimir.PublicOperationJournal where

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
import Mimir.PublicOperationBinding as Binding
import Mimir.RegisteredStoreAdmission as Registered
import Data.Maybe.Properties as Maybes
import Mimir.ProjectDeletion as Project
import Mimir.DirectGraphRecovery as Edges
import Mimir.GroundingRecovery as Ground
import Mimir.Validation as Validation
import Mimir.RecoverableStoreStep as Step
import Mimir.IndependentPublicationRecovery as Independent
import Mimir.IndependentBeliefRecovery as IndependentIntent
import Mimir.DefeatRecovery as Defeat
import Mimir.SweepRecovery as Sweep
import Mimir.ExperienceSourceRecovery as Source
import Mimir.ReviewPublicationRecovery as ReviewPublication
import Mimir.ReviewPreparationRecovery as ReviewPreparation
import Mimir.OperationControls as Controls

import Mimir.PublicOperationCatalogue as Catalogue

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
    module C = Catalogue.Run library format databaseSum calculator arithmetic unicode vectors configuration
        textBefore allocateOwner database postgres serverTime utcTimestamp sourcePostgres sweepObservation
        reviewDependencies reviewCodec reviewBackend using
      (Kind; sweep; documentLoading; ReviewEnvironment; module PatternWrite; module PatternRemoval; module Relationship; module BeliefRemoval; module Grounding; module Propagate; module Decaying; module DocumentRemoval; module IndependentGuard; module PatternGuard; module PatternRemovalGuard; module RelationshipGuard; module BeliefRemovalGuard; module GroundingGuard; module PropagationGuard; module DecayGuard; module ClearGuard; module Reviewing; module Recording; module DocumentEntry)
  open C using (Kind; sweep; documentLoading; ReviewEnvironment; module PatternWrite; module PatternRemoval; module Relationship; module BeliefRemoval; module Grounding; module Propagate; module Decaying; module DocumentRemoval; module IndependentGuard; module PatternGuard; module PatternRemovalGuard; module RelationshipGuard; module BeliefRemovalGuard; module GroundingGuard; module PropagationGuard; module DecayGuard; module ClearGuard; module Reviewing; module Recording; module DocumentEntry)

  module Cached (environment : ReviewEnvironment) where
    private
      module Implementation where
        module Base = Catalogue.Run.Cached library format databaseSum calculator arithmetic unicode vectors configuration
          textBefore allocateOwner database postgres serverTime utcTimestamp sourcePostgres sweepObservation
          reviewDependencies reviewCodec reviewBackend environment using
          (Writer; projectWriter; patternWriter; independentWriter; patternRemover; beliefRemover; relationshipWriter
          ; groundingWriter; propagator; decayer; documentRemover; defeater; sweeper; sourceWriter; reviewer; documentLoader
          ; writerInput; writerName; module Body)
        open Base public
        module Read = Controls.Readback library postgres using
          (ExecutionContext; Result; ResumableOrCompleted
          ; admission; admissionCompletedAnswer; admissionCompletedLookup; admitted; admittedHasPending
          ; answer; completed; pending; returned; undeclaredAbsent; unknownToken)
        module ProjectJournal = Controls.Readback.ProjectJournal library postgres using (interruptedReadback; interruptedFrame)
        Resolved : Registered.Descriptor → ℕ → Step.Registration → Set
        Resolved shape token registration = Σ (Store.ReservationRow × Store.BindingRow)
          (λ returned → Registered.resolve shape token registration ≡ inj₂ returned)

        module SinglePlan shape = Controls.Plan.SingletonProjection shape using (finalStep; decodedSingle)

        resolvedSingleton : ∀ shape operation token before (entry : Read.ExecutionContext operation token before) →
          Resolved shape token (Step.registration before) →
          Controls.Plan.Saved.steps (Read.ExecutionContext.plan entry) ≡ (SinglePlan.finalStep shape ∷ [])
        resolvedSingleton shape operation token before entry (returned , accepted)
          with Registered.resolveMatched shape token (Step.registration before) returned accepted
        ... | raw , stored , matched = SinglePlan.decodedSingle shape
          (Read.ExecutionContext.rawPlan entry) (Read.ExecutionContext.plan entry)
          (subst (λ actual → Registered.Plan.matches shape actual ≡ true) (sym sameRaw) matched)
          (Read.ExecutionContext.decoded entry)
          where
          sameRaw = Maybes.just-injective (trans (sym (Read.ExecutionContext.originalPlan entry)) stored)

        patternResolved : ∀ (input : PatternWrite.Internal) registration → PatternWrite.admit input registration ≡ nothing →
          Resolved (PatternWrite.descriptor) (proj₁ input) registration
        patternResolved input registration admitted
          with Registered.resolve (PatternWrite.descriptor) (proj₁ input) registration in resolved
        ... | inj₁ fault with admitted
        ... | ()
        patternResolved input registration admitted | inj₂ returned = returned , refl

        patternRemovalResolved : ∀ (token : ℕ) registration → PatternRemoval.admit token registration ≡ nothing →
          Resolved (PatternRemoval.descriptor) (token) registration
        patternRemovalResolved token registration admitted
          with Registered.resolve (PatternRemoval.descriptor) (token) registration in resolved
        ... | inj₁ fault with admitted
        ... | ()
        patternRemovalResolved token registration admitted | inj₂ returned = returned , refl

        relationshipResolved : ∀ (kind : Edges.Kind) (token : ℕ) registration → Relationship.admit kind token registration ≡ nothing →
          Resolved (Edges.descriptor kind) (token) registration
        relationshipResolved kind token registration admitted
          with Registered.resolve (Edges.descriptor kind) (token) registration in resolved
        ... | inj₁ fault with admitted
        ... | ()
        relationshipResolved kind token registration admitted | inj₂ returned = returned , refl

        beliefRemovalResolved : ∀ (token : ℕ) registration → BeliefRemoval.admit token registration ≡ nothing →
          Resolved (BeliefRemoval.descriptor) (token) registration
        beliefRemovalResolved token registration admitted
          with Registered.resolve (BeliefRemoval.descriptor) (token) registration in resolved
        ... | inj₁ fault with admitted
        ... | ()
        beliefRemovalResolved token registration admitted | inj₂ returned = returned , refl

        groundingResolved : ∀ (kind : Ground.Kind) (token : ℕ) registration → Grounding.admit kind token registration ≡ nothing →
          Resolved (Grounding.descriptor kind) (token) registration
        groundingResolved kind token registration admitted
          with Registered.resolve (Grounding.descriptor kind) (token) registration in resolved
        ... | inj₁ fault with admitted
        ... | ()
        groundingResolved kind token registration admitted | inj₂ returned = returned , refl

        propagationResolved : ∀ (token : ℕ) registration → Propagate.admit token registration ≡ nothing →
          Resolved (Propagate.descriptor) (token) registration
        propagationResolved token registration admitted
          with Registered.resolve (Propagate.descriptor) (token) registration in resolved
        ... | inj₁ fault with admitted
        ... | ()
        propagationResolved token registration admitted | inj₂ returned = returned , refl

        decayResolved : ∀ (token : ℕ) registration → Decaying.admit token registration ≡ nothing →
          Resolved (Decaying.descriptor) (token) registration
        decayResolved token registration admitted
          with Registered.resolve (Decaying.descriptor) (token) registration in resolved
        ... | inj₁ fault with admitted
        ... | ()
        decayResolved token registration admitted | inj₂ returned = returned , refl

        clearResolved : ∀ (token : ℕ) registration → DocumentRemoval.admit token registration ≡ nothing →
          Resolved (DocumentRemoval.descriptor) (token) registration
        clearResolved token registration admitted
          with Registered.resolve (DocumentRemoval.descriptor) (token) registration in resolved
        ... | inj₁ fault with admitted
        ... | ()
        clearResolved token registration admitted | inj₂ returned = returned , refl

        sourceResolved : ∀ (input : Recording.Internal) registration → Recording.admit input registration ≡ nothing →
          Resolved (Recording.descriptor) (proj₁ input) registration
        sourceResolved input registration admitted
          with Registered.resolve (Recording.descriptor) (proj₁ input) registration in resolved
        ... | inj₁ fault with admitted
        ... | ()
        sourceResolved input registration admitted | inj₂ returned = returned , refl


        module PatternKernel = Controls.Readback.SingleKernel library postgres (PatternWrite.Internal) _ proj₁ (λ input → PatternWrite.key (proj₁ input)) (λ input → PatternWrite.distinct (proj₁ input))
          (PatternWrite.decide) (PatternWrite.keepsJournal) (PatternWrite.admit)
          using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

        patternPublishedReadback : ∀ operation (input : PatternWrite.Internal) before current
          (entry : Read.ExecutionContext operation (proj₁ input) before) value →
          Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
          (current , Step.done value) ≡ PatternKernel.Saved.execute input before →
          Read.ResumableOrCompleted operation (proj₁ input) current
        patternPublishedReadback operation input before current entry value admitted observed =
          PatternKernel.executeReadback operation input before current entry
            (SinglePlan.finalStep (PatternWrite.descriptor)) value admitted
            (resolvedSingleton (PatternWrite.descriptor) operation (proj₁ input) before entry
              (patternResolved input (Step.registration before)
                (PatternKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

        module PatternRemovalKernel = Controls.Readback.SingleKernel library postgres (ℕ) _ (λ input → input) (PatternRemoval.key) (PatternRemoval.distinct)
          (PatternRemoval.decide) (PatternRemoval.keepsJournal) (PatternRemoval.admit)
          using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

        patternRemovalPublishedReadback : ∀ operation (input : ℕ) before current
          (entry : Read.ExecutionContext operation (input) before) value →
          Read.admission operation (input) before ≡ Read.admitted entry →
          (current , Step.done value) ≡ PatternRemovalKernel.Saved.execute input before →
          Read.ResumableOrCompleted operation (input) current
        patternRemovalPublishedReadback operation input before current entry value admitted observed =
          PatternRemovalKernel.executeReadback operation input before current entry
            (SinglePlan.finalStep (PatternRemoval.descriptor)) value admitted
            (resolvedSingleton (PatternRemoval.descriptor) operation (input) before entry
              (patternRemovalResolved input (Step.registration before)
                (PatternRemovalKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

        module RelationshipKernel kind = Controls.Readback.SingleKernel library postgres (ℕ) _ (λ input → input) (Relationship.key kind) (Relationship.distinct kind)
          (Relationship.decide kind) (Relationship.keepsJournal kind) (Relationship.admit kind)
          using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

        relationshipPublishedReadback : ∀ (kind : Edges.Kind) operation (input : ℕ) before current
          (entry : Read.ExecutionContext operation (input) before) value →
          Read.admission operation (input) before ≡ Read.admitted entry →
          (current , Step.done value) ≡ RelationshipKernel.Saved.execute kind input before →
          Read.ResumableOrCompleted operation (input) current
        relationshipPublishedReadback kind operation input before current entry value admitted observed =
          RelationshipKernel.executeReadback kind operation input before current entry
            (SinglePlan.finalStep (Edges.descriptor kind)) value admitted
            (resolvedSingleton (Edges.descriptor kind) operation (input) before entry
              (relationshipResolved kind input (Step.registration before)
                (RelationshipKernel.Saved.doneIsAdmitted kind input before current value (sym observed)))) refl observed

        module BeliefRemovalKernel = Controls.Readback.SingleKernel library postgres (ℕ × ℤ) _ proj₁ (λ input → BeliefRemoval.key (proj₁ input)) (λ input → BeliefRemoval.distinct (proj₁ input))
          (BeliefRemoval.decide) (BeliefRemoval.keepsJournal) (λ input → BeliefRemoval.admit (proj₁ input))
          using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

        beliefRemovalPublishedReadback : ∀ operation (input : ℕ × ℤ) before current
          (entry : Read.ExecutionContext operation (proj₁ input) before) value →
          Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
          (current , Step.done value) ≡ BeliefRemovalKernel.Saved.execute input before →
          Read.ResumableOrCompleted operation (proj₁ input) current
        beliefRemovalPublishedReadback operation input before current entry value admitted observed =
          BeliefRemovalKernel.executeReadback operation input before current entry
            (SinglePlan.finalStep (BeliefRemoval.descriptor)) value admitted
            (resolvedSingleton (BeliefRemoval.descriptor) operation (proj₁ input) before entry
              (beliefRemovalResolved (proj₁ input) (Step.registration before)
                (BeliefRemovalKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

        module GroundingKernel kind = Controls.Readback.SingleKernel library postgres (ℕ × ℤ) _ proj₁ (λ input → Grounding.key kind (proj₁ input)) (λ input → Grounding.distinct kind (proj₁ input))
          (Grounding.decide kind) (Grounding.keepsJournal kind) (λ input → Grounding.admit kind (proj₁ input))
          using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

        groundingPublishedReadback : ∀ (kind : Ground.Kind) operation (input : ℕ × ℤ) before current
          (entry : Read.ExecutionContext operation (proj₁ input) before) value →
          Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
          (current , Step.done value) ≡ GroundingKernel.Saved.execute kind input before →
          Read.ResumableOrCompleted operation (proj₁ input) current
        groundingPublishedReadback kind operation input before current entry value admitted observed =
          GroundingKernel.executeReadback kind operation input before current entry
            (SinglePlan.finalStep (Grounding.descriptor kind)) value admitted
            (resolvedSingleton (Grounding.descriptor kind) operation (proj₁ input) before entry
              (groundingResolved kind (proj₁ input) (Step.registration before)
                (GroundingKernel.Saved.doneIsAdmitted kind input before current value (sym observed)))) refl observed

        module PropagationKernel = Controls.Readback.SingleKernel library postgres (ℕ × ℤ) _ proj₁ (λ input → Propagate.key (proj₁ input)) (λ input → Propagate.distinct (proj₁ input))
          (Propagate.decide) (Propagate.keepsJournal) (λ input → Propagate.admit (proj₁ input))
          using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

        propagationPublishedReadback : ∀ operation (input : ℕ × ℤ) before current
          (entry : Read.ExecutionContext operation (proj₁ input) before) value →
          Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
          (current , Step.done value) ≡ PropagationKernel.Saved.execute input before →
          Read.ResumableOrCompleted operation (proj₁ input) current
        propagationPublishedReadback operation input before current entry value admitted observed =
          PropagationKernel.executeReadback operation input before current entry
            (SinglePlan.finalStep (Propagate.descriptor)) value admitted
            (resolvedSingleton (Propagate.descriptor) operation (proj₁ input) before entry
              (propagationResolved (proj₁ input) (Step.registration before)
                (PropagationKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

        module DecayKernel = Controls.Readback.SingleKernel library postgres (ℕ × ℤ) _ proj₁ (λ input → Decaying.key (proj₁ input)) (λ input → Decaying.distinct (proj₁ input))
          (Decaying.decide) (Decaying.keepsJournal) (λ input → Decaying.admit (proj₁ input))
          using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

        decayPublishedReadback : ∀ operation (input : ℕ × ℤ) before current
          (entry : Read.ExecutionContext operation (proj₁ input) before) value →
          Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
          (current , Step.done value) ≡ DecayKernel.Saved.execute input before →
          Read.ResumableOrCompleted operation (proj₁ input) current
        decayPublishedReadback operation input before current entry value admitted observed =
          DecayKernel.executeReadback operation input before current entry
            (SinglePlan.finalStep (Decaying.descriptor)) value admitted
            (resolvedSingleton (Decaying.descriptor) operation (proj₁ input) before entry
              (decayResolved (proj₁ input) (Step.registration before)
                (DecayKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

        module ClearKernel = Controls.Readback.SingleKernel library postgres (ℕ × ℤ) _ proj₁ (λ input → DocumentRemoval.key (proj₁ input)) (λ input → DocumentRemoval.distinct (proj₁ input))
          (DocumentRemoval.decide) (DocumentRemoval.keepsJournal) (λ input → DocumentRemoval.admit (proj₁ input))
          using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

        clearPublishedReadback : ∀ operation (input : ℕ × ℤ) before current
          (entry : Read.ExecutionContext operation (proj₁ input) before) value →
          Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
          (current , Step.done value) ≡ ClearKernel.Saved.execute input before →
          Read.ResumableOrCompleted operation (proj₁ input) current
        clearPublishedReadback operation input before current entry value admitted observed =
          ClearKernel.executeReadback operation input before current entry
            (SinglePlan.finalStep (DocumentRemoval.descriptor)) value admitted
            (resolvedSingleton (DocumentRemoval.descriptor) operation (proj₁ input) before entry
              (clearResolved (proj₁ input) (Step.registration before)
                (ClearKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

        module SourceKernel = Controls.Readback.SingleKernel library postgres (Recording.Internal) _ proj₁ (λ input → Recording.key (proj₁ input)) (λ input → Recording.distinct (proj₁ input))
          (Recording.decide) (Recording.keepsJournal) (Recording.admit)
          using (executeReadback; executeStateOutcome; executeStateReadback; module Saved)

        sourcePublishedReadback : ∀ operation (input : Recording.Internal) before current
          (entry : Read.ExecutionContext operation (proj₁ input) before) value →
          Read.admission operation (proj₁ input) before ≡ Read.admitted entry →
          (current , Step.done value) ≡ SourceKernel.Saved.execute input before →
          Read.ResumableOrCompleted operation (proj₁ input) current
        sourcePublishedReadback operation input before current entry value admitted observed =
          SourceKernel.executeReadback operation input before current entry
            (SinglePlan.finalStep (Recording.descriptor)) value admitted
            (resolvedSingleton (Recording.descriptor) operation (proj₁ input) before entry
              (sourceResolved input (Step.registration before)
                (SourceKernel.Saved.doneIsAdmitted input before current value (sym observed)))) refl observed

        patternReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          PatternWrite.X.Interrupted (PatternWrite.script token) before current → Read.ResumableOrCompleted operation token current
        patternReadback operation token before current entry admitted cut with PatternWrite.interruptionState token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (metadata , physical) with PatternKernel.executeStateOutcome (token , metadata) before current physical
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (value , observed) = patternPublishedReadback operation (token , metadata) before current entry value admitted observed

        patternRemovalReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          PatternRemovalKernel.Saved.X.Interrupted (PatternRemovalKernel.Saved.script token) before current →
          Read.ResumableOrCompleted operation token current
        patternRemovalReadback operation token before current entry admitted cut
          with PatternRemovalKernel.Saved.interruptedDoneOrUnchanged token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (value , observed) = patternRemovalPublishedReadback operation token before current entry value admitted observed

        relationshipReadback : ∀ kind operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          RelationshipKernel.Saved.X.Interrupted kind (RelationshipKernel.Saved.script kind token) before current →
          Read.ResumableOrCompleted operation token current
        relationshipReadback kind operation token before current entry admitted cut
          with RelationshipKernel.Saved.interruptedDoneOrUnchanged kind token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (value , observed) = relationshipPublishedReadback kind operation token before current entry value admitted observed

        beliefRemovalReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          BeliefRemoval.X.Interrupted (BeliefRemoval.script token) before current → Read.ResumableOrCompleted operation token current
        beliefRemovalReadback operation token before current entry admitted cut with BeliefRemoval.interruptionState token before current cut
        ... | Step.Observed.unchanged refl = inj₁ (entry , admitted)
        ... | Step.Observed.published time value observed = beliefRemovalPublishedReadback operation (token , time) before current entry value admitted observed

        groundingReadback : ∀ kind operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          Grounding.X.Interrupted kind (Grounding.script kind token) before current → Read.ResumableOrCompleted operation token current
        groundingReadback kind operation token before current entry admitted cut with Grounding.interruptionState kind token before current cut
        ... | Step.Observed.unchanged refl = inj₁ (entry , admitted)
        ... | Step.Observed.published time value observed = groundingPublishedReadback kind operation (token , time) before current entry value admitted observed

        propagationReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          Propagate.X.Interrupted (Propagate.script token) before current → Read.ResumableOrCompleted operation token current
        propagationReadback operation token before current entry admitted cut with Propagate.interruptionState token before current cut
        ... | Step.Observed.unchanged refl = inj₁ (entry , admitted)
        ... | Step.Observed.published time value observed = propagationPublishedReadback operation (token , time) before current entry value admitted observed

        decayReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          Decaying.X.Interrupted (Decaying.script token) before current → Read.ResumableOrCompleted operation token current
        decayReadback operation token before current entry admitted cut with Decaying.interruptionState token before current cut
        ... | Step.Observed.unchanged refl = inj₁ (entry , admitted)
        ... | Step.Observed.published time value observed = decayPublishedReadback operation (token , time) before current entry value admitted observed

        clearReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          DocumentRemoval.X.Interrupted (DocumentRemoval.script token) before current → Read.ResumableOrCompleted operation token current
        clearReadback operation token before current entry admitted cut with DocumentRemoval.interruptionState token before current cut
        ... | Step.Observed.unchanged refl = inj₁ (entry , admitted)
        ... | Step.Observed.published time value observed = clearPublishedReadback operation (token , time) before current entry value admitted observed

        sourceReadback : ∀ operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          Recording.X.Interrupted (Recording.script token) before current → Read.ResumableOrCompleted operation token current
        sourceReadback operation token before current entry admitted cut with Recording.interruptionState token before current cut
        ... | Recording.unchanged refl = inj₁ (entry , admitted)
        ... | Recording.published metadata value valid observed = sourcePublishedReadback operation (token , metadata) before current entry value admitted observed


        MetadataFrame : ℕ → Store.World → Store.World → Set
        MetadataFrame token before current = Step.registration current ≡ Step.registration before ×
          Store.lookupCancellation current token ≡ Store.lookupCancellation before token

        patternMetadata : ∀ token before current → PatternWrite.X.Interrupted (PatternWrite.script token) before current →
          MetadataFrame token before current
        patternMetadata token before current cut with PatternWrite.interruptionState token before current cut
        ... | inj₁ refl = refl , refl
        ... | inj₂ (metadata , physical) =
          trans (cong Step.registration physical) (PatternKernel.Saved.registrationUnchanged (token , metadata) before) ,
          trans (cong (λ world → Store.lookupCancellation world token) physical)
            (PatternKernel.Saved.cancellationUnchanged token (token , metadata) before)

        patternRemovalMetadata : ∀ token before current →
          PatternRemovalKernel.Saved.X.Interrupted (PatternRemovalKernel.Saved.script token) before current → MetadataFrame token before current
        patternRemovalMetadata token before current cut = PatternRemovalKernel.Saved.interruptedKeepsRegistration token before current cut ,
          PatternRemovalKernel.Saved.interruptedKeepsCancellation token token before current cut

        relationshipMetadata : ∀ kind token before current →
          RelationshipKernel.Saved.X.Interrupted kind (RelationshipKernel.Saved.script kind token) before current → MetadataFrame token before current
        relationshipMetadata kind token before current cut = RelationshipKernel.Saved.interruptedKeepsRegistration kind token before current cut ,
          RelationshipKernel.Saved.interruptedKeepsCancellation kind token token before current cut

        sourceMetadata : ∀ token before current → Recording.X.Interrupted (Recording.script token) before current →
          MetadataFrame token before current
        sourceMetadata token before current cut with Recording.interruptionState token before current cut
        ... | Recording.unchanged refl = refl , refl
        ... | Recording.published metadata value valid physical =
          trans (cong Step.registration (cong proj₁ physical)) (SourceKernel.Saved.registrationUnchanged (token , metadata) before) ,
          trans (cong (λ world → Store.lookupCancellation world token) (cong proj₁ physical))
            (SourceKernel.Saved.cancellationUnchanged token (token , metadata) before)

        patternGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          PatternGuard.X.Interrupted expected (PatternGuard.script expected token) before current →
          Read.ResumableOrCompleted operation token current
        patternGuardedReadback expected operation token before current entry admitted cut
          with PatternGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (matched , actualCut) = patternReadback operation token before current entry admitted actualCut

        patternGuardedMetadata : ∀ expected token before current →
          PatternGuard.X.Interrupted expected (PatternGuard.script expected token) before current → MetadataFrame token before current
        patternGuardedMetadata expected token before current cut
          with PatternGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = refl , refl
        ... | inj₂ (matched , actualCut) = patternMetadata token before current actualCut

        patternRemovalGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          PatternRemovalGuard.X.Interrupted expected (PatternRemovalGuard.script expected token) before current →
          Read.ResumableOrCompleted operation token current
        patternRemovalGuardedReadback expected operation token before current entry admitted cut
          with PatternRemovalGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (matched , actualCut) = patternRemovalReadback operation token before current entry admitted actualCut

        patternRemovalGuardedMetadata : ∀ expected token before current →
          PatternRemovalGuard.X.Interrupted expected (PatternRemovalGuard.script expected token) before current → MetadataFrame token before current
        patternRemovalGuardedMetadata expected token before current cut
          with PatternRemovalGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = refl , refl
        ... | inj₂ (matched , actualCut) = patternRemovalMetadata token before current actualCut

        relationshipGuardedReadback : ∀ kind expected operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          RelationshipGuard.X.Interrupted kind expected (RelationshipGuard.script kind expected token) before current →
          Read.ResumableOrCompleted operation token current
        relationshipGuardedReadback kind expected operation token before current entry admitted cut
          with RelationshipGuard.interruptionMeaning kind expected token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (matched , actualCut) = relationshipReadback kind operation token before current entry admitted actualCut

        relationshipGuardedMetadata : ∀ kind expected token before current →
          RelationshipGuard.X.Interrupted kind expected (RelationshipGuard.script kind expected token) before current → MetadataFrame token before current
        relationshipGuardedMetadata kind expected token before current cut
          with RelationshipGuard.interruptionMeaning kind expected token before current cut
        ... | inj₁ refl = refl , refl
        ... | inj₂ (matched , actualCut) = relationshipMetadata kind token before current actualCut

        beliefRemovalGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          BeliefRemovalGuard.X.Interrupted expected (BeliefRemovalGuard.script expected token) before current →
          Read.ResumableOrCompleted operation token current
        beliefRemovalGuardedReadback expected operation token before current entry admitted cut
          with BeliefRemovalGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (matched , actualCut) = beliefRemovalReadback operation token before current entry admitted actualCut

        beliefRemovalGuardedMetadata : ∀ expected token before current →
          BeliefRemovalGuard.X.Interrupted expected (BeliefRemovalGuard.script expected token) before current → MetadataFrame token before current
        beliefRemovalGuardedMetadata expected token before current cut
          with BeliefRemovalGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = refl , refl
        ... | inj₂ (matched , actualCut) = BeliefRemoval.interruptedKeepsRegistration token before current actualCut ,
          BeliefRemoval.interruptedKeepsCancellation token token before current actualCut

        groundingGuardedReadback : ∀ kind expected operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          GroundingGuard.X.Interrupted kind expected (GroundingGuard.script kind expected token) before current →
          Read.ResumableOrCompleted operation token current
        groundingGuardedReadback kind expected operation token before current entry admitted cut
          with GroundingGuard.interruptionMeaning kind expected token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (matched , actualCut) = groundingReadback kind operation token before current entry admitted actualCut

        groundingGuardedMetadata : ∀ kind expected token before current →
          GroundingGuard.X.Interrupted kind expected (GroundingGuard.script kind expected token) before current → MetadataFrame token before current
        groundingGuardedMetadata kind expected token before current cut
          with GroundingGuard.interruptionMeaning kind expected token before current cut
        ... | inj₁ refl = refl , refl
        ... | inj₂ (matched , actualCut) = Grounding.interruptedKeepsRegistration kind token before current actualCut ,
          Grounding.interruptedKeepsCancellation kind token token before current actualCut

        propagationGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          PropagationGuard.X.Interrupted expected (PropagationGuard.script expected token) before current →
          Read.ResumableOrCompleted operation token current
        propagationGuardedReadback expected operation token before current entry admitted cut
          with PropagationGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (matched , actualCut) = propagationReadback operation token before current entry admitted actualCut

        propagationGuardedMetadata : ∀ expected token before current →
          PropagationGuard.X.Interrupted expected (PropagationGuard.script expected token) before current → MetadataFrame token before current
        propagationGuardedMetadata expected token before current cut
          with PropagationGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = refl , refl
        ... | inj₂ (matched , actualCut) = Propagate.interruptedKeepsRegistration token before current actualCut ,
          Propagate.interruptedKeepsCancellation token token before current actualCut

        decayGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          DecayGuard.X.Interrupted expected (DecayGuard.script expected token) before current →
          Read.ResumableOrCompleted operation token current
        decayGuardedReadback expected operation token before current entry admitted cut
          with DecayGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (matched , actualCut) = decayReadback operation token before current entry admitted actualCut

        decayGuardedMetadata : ∀ expected token before current →
          DecayGuard.X.Interrupted expected (DecayGuard.script expected token) before current → MetadataFrame token before current
        decayGuardedMetadata expected token before current cut
          with DecayGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = refl , refl
        ... | inj₂ (matched , actualCut) = Decaying.interruptedKeepsRegistration token before current actualCut ,
          Decaying.interruptedKeepsCancellation token token before current actualCut

        clearGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
          Read.admission operation token before ≡ Read.admitted entry →
          ClearGuard.X.Interrupted expected (ClearGuard.script expected token) before current →
          Read.ResumableOrCompleted operation token current
        clearGuardedReadback expected operation token before current entry admitted cut
          with ClearGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (matched , actualCut) = clearReadback operation token before current entry admitted actualCut

        clearGuardedMetadata : ∀ expected token before current →
          ClearGuard.X.Interrupted expected (ClearGuard.script expected token) before current → MetadataFrame token before current
        clearGuardedMetadata expected token before current cut
          with ClearGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = refl , refl
        ... | inj₂ (matched , actualCut) = DocumentRemoval.interruptedKeepsRegistration token before current actualCut ,
          DocumentRemoval.interruptedKeepsCancellation token token before current actualCut


        module IndependentJournal = Independent.Registered.Public.Journal format library databaseSum calculator
          allocateOwner configuration postgres using (interruptedReadback; interruptedFrame)
        module DefeatJournal = Defeat.Registered.Journal library databaseSum calculator serverTime postgres
          using (interruptedReadback; interruptedFrame)
        module SweepJournal = Sweep.Registered.Journal library format databaseSum calculator sweepObservation postgres
          using (interruptedReadback; interruptedAdmission; interruptedFrame)

        independentGuardedReadback : ∀ expected operation token before current (entry : Read.ExecutionContext operation token before) →
          operation ≡ toList "insert_belief" → Read.admission operation token before ≡ Read.admitted entry →
          IndependentGuard.X.Interrupted expected (IndependentGuard.script expected token) before current →
          Read.ResumableOrCompleted operation token current
        independentGuardedReadback expected .(toList "insert_belief") token before current entry refl admitted cut
          with IndependentGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = inj₁ (entry , admitted)
        ... | inj₂ (matched , actualCut) = IndependentJournal.interruptedReadback token before current entry admitted actualCut

        independentGuardedMetadata : ∀ expected token before current →
          IndependentGuard.X.Interrupted expected (IndependentGuard.script expected token) before current → MetadataFrame token before current
        independentGuardedMetadata expected token before current cut
          with IndependentGuard.interruptionMeaning expected token before current cut
        ... | inj₁ refl = refl , refl
        ... | inj₂ (matched , actualCut) = IndependentJournal.interruptedFrame token before current actualCut

        documentReadback : ∀ expected token before current (entry : Read.ExecutionContext (toList "load_document") token before) →
          Read.admission (toList "load_document") token before ≡ Read.admitted entry →
          Body.X.Interrupted (documentLoading expected) (Body.script (documentLoading expected) token) before current →
          Read.ResumableOrCompleted (toList "load_document") token current
        documentReadback expected token before current entry admitted cut with DocumentEntry.interruptedHasJournal token before current entry admitted cut
        ... | DocumentEntry.pending actual known = inj₁ (actual , known)
        ... | DocumentEntry.completed binding raw known replay = inj₂ (binding , raw , known)


        pendingSweepUnchanged : ∀ expected token before current (entry : Read.ExecutionContext (toList "sweep_expired_defeated") token before) →
          Read.admission (toList "sweep_expired_defeated") token before ≡ Read.admitted entry →
          Body.X.Interrupted (sweep expected) (Body.script (sweep expected) token) before current →
          Binding.Creating.Resumable library postgres (Read.answer token current) → current ≡ before
        pendingSweepUnchanged expected token before current entry admitted cut possible
          with SweepJournal.interruptedReadback token before current entry admitted cut
        ... | inj₁ unchanged = unchanged
        ... | inj₂ (binding , raw , completed) = ⊥-elim
          (subst (Binding.Creating.Resumable library postgres)
            (Read.admissionCompletedAnswer (toList "sweep_expired_defeated") token current binding raw completed) possible)


        bodyReadback : ∀ {kind} (writer : Writer kind) token before current
          (entry : Read.ExecutionContext (writerName writer) token before) →
          Read.admission (writerName writer) token before ≡ Read.admitted entry →
          Body.X.Interrupted kind (Body.script kind (writerInput writer token)) before current →
          Read.ResumableOrCompleted (writerName writer) token current
        bodyReadback (projectWriter {project}) token before current entry admitted cut =
          ProjectJournal.interruptedReadback (Project.Registered.input token project) before current entry admitted cut
        bodyReadback (patternWriter {expected}) token before current entry admitted cut =
          patternGuardedReadback expected _ token before current entry admitted cut
        bodyReadback (independentWriter {expected}) token before current entry admitted cut =
          independentGuardedReadback expected _ token before current entry refl admitted cut
        bodyReadback (patternRemover {expected}) token before current entry admitted cut =
          patternRemovalGuardedReadback expected _ token before current entry admitted cut
        bodyReadback (beliefRemover {expected}) token before current entry admitted cut =
          beliefRemovalGuardedReadback expected _ token before current entry admitted cut
        bodyReadback (relationshipWriter {kind} {expected}) token before current entry admitted cut =
          relationshipGuardedReadback kind expected _ token before current entry admitted cut
        bodyReadback (groundingWriter {kind} {expected}) token before current entry admitted cut =
          groundingGuardedReadback kind expected _ token before current entry admitted cut
        bodyReadback (propagator {expected}) token before current entry admitted cut =
          propagationGuardedReadback expected _ token before current entry admitted cut
        bodyReadback (decayer {expected}) token before current entry admitted cut =
          decayGuardedReadback expected _ token before current entry admitted cut
        bodyReadback (documentRemover {expected}) token before current entry admitted cut =
          clearGuardedReadback expected _ token before current entry admitted cut
        bodyReadback defeater token before current entry admitted cut = DefeatJournal.interruptedReadback token before current entry admitted cut
        bodyReadback sweeper token before current entry admitted cut = SweepJournal.interruptedAdmission token before current entry admitted cut
        bodyReadback sourceWriter token before current entry admitted cut = sourceReadback _ token before current entry admitted cut
        bodyReadback reviewer token before current entry admitted cut = Reviewing.interruptedReadback token before current entry admitted cut
        bodyReadback (documentLoader {expected}) token before current entry admitted cut = documentReadback expected token before current entry admitted cut

        bodyMetadata : ∀ {kind} (writer : Writer kind) token before current →
          Body.X.Interrupted kind (Body.script kind (writerInput writer token)) before current → MetadataFrame token before current
        bodyMetadata (projectWriter {project}) token before current cut =
          ProjectJournal.interruptedFrame (Project.Registered.input token project) before current cut
        bodyMetadata (patternWriter {expected}) token before current cut = patternGuardedMetadata expected token before current cut
        bodyMetadata (independentWriter {expected}) token before current cut = independentGuardedMetadata expected token before current cut
        bodyMetadata (patternRemover {expected}) token before current cut = patternRemovalGuardedMetadata expected token before current cut
        bodyMetadata (beliefRemover {expected}) token before current cut = beliefRemovalGuardedMetadata expected token before current cut
        bodyMetadata (relationshipWriter {kind} {expected}) token before current cut = relationshipGuardedMetadata kind expected token before current cut
        bodyMetadata (groundingWriter {kind} {expected}) token before current cut = groundingGuardedMetadata kind expected token before current cut
        bodyMetadata (propagator {expected}) token before current cut = propagationGuardedMetadata expected token before current cut
        bodyMetadata (decayer {expected}) token before current cut = decayGuardedMetadata expected token before current cut
        bodyMetadata (documentRemover {expected}) token before current cut = clearGuardedMetadata expected token before current cut
        bodyMetadata defeater token before current cut = DefeatJournal.interruptedFrame token before current cut
        bodyMetadata sweeper token before current cut = SweepJournal.interruptedFrame token before current cut
        bodyMetadata sourceWriter token before current cut = sourceMetadata token before current cut
        bodyMetadata reviewer token before current cut = Reviewing.interruptedKeepsRegistration token before current cut ,
          Reviewing.interruptedKeepsCancellation token token before current cut
        bodyMetadata documentLoader token before current cut = DocumentEntry.interruptedMetadataFrame token before current cut
    open Implementation public using (MetadataFrame; pendingSweepUnchanged; bodyReadback; bodyMetadata)

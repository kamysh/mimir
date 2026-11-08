{-# OPTIONS --safe #-}
-- Instantiate the transaction protocol with concrete Mimir plans and state.
-- Every successful fresh operation includes source/review history, ownership,
-- assessments, edges and numerical graph writes in its one proposed world.
module Mimir.LearningOperations where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
import Data.String
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (does; yes; no)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.ExperienceSchema using (Experience)
open import Mimir.ReviewSchema using (Review)
open import Mimir.LearningCandidates using (Candidate)
import Mimir.ExperienceSchema as ExperienceSchema
import Mimir.ReviewSchema as ReviewSchema
import Mimir.LearningStore as Store
import Mimir.ExperienceRecord as Recording
import Mimir.ReviewRecord as Reviewing
import Mimir.ReviewObservation as Observation
import Mimir.LearningTransaction as Transaction
import Mimir.LearningTransactionReceipt as Receipt
import Mimir.RevisionBounds as Bounds
import Mimir.Validation as Validation
import Mimir.LearningInput as Input
import Mimir.LearningNormalization as Normalization
import Mimir.Effects as Effects
import Mimir.ApplicationStore as Application
import Mimir.BeliefEmbedding as Embedding
import Mimir.McpErrors as Errors
open import Mimir.Bits using (Byte)

data Request : Set where
  recordExperience : Input.Experience → ℤ → Request
  reviewExperience : Input.Review → ℤ → Request

data Payload : Set where
  experiencePayload : Input.Experience → Payload
  reviewPayload : Input.Review → Payload

payload : Request → Payload
payload (recordExperience value expected) = experiencePayload value
payload (reviewExperience value expected) = reviewPayload value

data Failure : Set where
  recordFailure : Recording.Failure → Failure
  reviewFailure : Reviewing.Failure → Failure
  externalFailure : Text → Failure
  allocationFailure : Validation.Fault → Failure
  preparationFailure : Errors.AgentCorrection.Claim → Failure

module Correction = Errors.AgentCorrection

recordReadback : Text
recordReadback = Data.String.toList "Call get_experience with the same experience ID to read its current revision, and experience_history if the changes need inspection. Compare the stored content with the intended correction before resubmitting with the current expected_revision. Keep the same incident ID; do not blindly overwrite newer work or invent a revision."

reviewReadback : Text
reviewReadback = Data.String.toList "Call get_experience and get_learning_review with the same experience ID to read the current source, source revision and review revision. Inspect experience_history if needed. Re-evaluate the review against that source before resubmitting review.experience_revision and expected_review_revision. Do not blindly overwrite another review or invent revision values."

-- Only the two identified public revision fields are correctable here. A
-- similarly coded internal snapshot-integrity fault stays an ordinary error.
reviewRevisionCorrection : Validation.Fault → Maybe Correction.Claim
reviewRevisionCorrection detail@(Validation.problem (Validation.fieldKey name ∷ []) Validation.staleRevision reason)
  with name ≟Text Data.String.toList "expected_review_revision"
... | no _ = nothing
... | yes _ = just (Correction.claim
  (Correction.staleRevisionItem (Validation.Fault.path detail) (Validation.Fault.explanation detail) reviewReadback) [])
reviewRevisionCorrection detail@(Validation.problem (Validation.fieldKey outer ∷ Validation.fieldKey inner ∷ []) Validation.staleRevision reason)
  with outer ≟Text Data.String.toList "review" | inner ≟Text Data.String.toList "experience_revision"
... | yes _ | yes _ = just (Correction.claim
  (Correction.staleRevisionItem (Validation.Fault.path detail) (Validation.Fault.explanation detail) reviewReadback) [])
... | _ | _ = nothing
reviewRevisionCorrection _ = nothing

revisionCorrection : Failure → Maybe Correction.Claim
revisionCorrection (recordFailure Recording.staleRevision) = just (Correction.claim
  (Correction.staleRevisionItem (Validation.key "expected_revision" ∷ [])
    (Data.String.toList "The supplied experience revision is no longer current.") recordReadback) [])
revisionCorrection (reviewFailure (Reviewing.invalid detail)) = reviewRevisionCorrection detail
revisionCorrection _ = nothing

beliefReferenceCorrection : Validation.Fault → Maybe Correction.Claim
beliefReferenceCorrection detail with Validation.Fault.code detail
... | Validation.missingReference = just (Correction.claim (Correction.beliefReferenceItem detail) [])
... | Validation.wrongIdentity = just (Correction.claim (Correction.beliefReferenceItem detail) [])
... | Validation.unsupportedCombination = just (Correction.claim (Correction.beliefReferenceItem detail) [])
... | _ = nothing

referenceCorrection : Failure → Maybe Correction.Claim
referenceCorrection (recordFailure Recording.missingPattern) = just (Correction.claim
  (Correction.patternReferenceItem (Validation.fault (Validation.key "experience" ∷ Validation.key "pattern_id" ∷ [])
    Validation.missingReference "The requested pattern was not found in Mimir.")) [])
referenceCorrection (recordFailure Recording.foreignPattern) = just (Correction.claim
  (Correction.patternReferenceItem (Validation.fault (Validation.key "experience" ∷ Validation.key "pattern_id" ∷ [])
    Validation.wrongIdentity "The requested pattern belongs to another project.")) [])
referenceCorrection (recordFailure (Recording.invalid detail@(Validation.problem
  (Validation.fieldKey outer ∷ Validation.fieldKey inner ∷ rest) code reason)))
  with outer ≟Text Data.String.toList "experience" | inner ≟Text Data.String.toList "belief_ids"
... | yes _ | yes _ = beliefReferenceCorrection detail
... | _ | _ = nothing
referenceCorrection (reviewFailure (Reviewing.invalid detail@(Validation.problem
  (Validation.fieldKey outer ∷ Validation.fieldKey inner ∷ rest) code reason)))
  with outer ≟Text Data.String.toList "review"
... | no _ = nothing
... | yes _ = beliefReferenceCorrection detail
referenceCorrection _ = nothing

expectedValid : ℤ → Data.Bool.Bool
expectedValid expected = does ((+ 0) Integer.≤? expected) ∧ does (expected Integer.<? (+ Bounds.i64Maximum))

admit : Request → Maybe Failure
admit (recordExperience sourceValue expected) with expectedValid expected
... | false = just (recordFailure Recording.invalidExpected)
... | true = nothing
admit (reviewExperience reviewValue expected) with expectedValid expected
... | false = just (reviewFailure Reviewing.invalidExpected)
... | true = nothing

module Protocol (database : ℕ) (request : Request)
  (clock : Candidate → ℤ) (now : ℤ) (identities : Candidate → ℕ) where

  module T = Transaction.Over Store.World Observation.Snapshot Failure database 671942183
  module Receipts = Receipt.Over Store.World Observation.Snapshot Failure database 671942183
  module Normalize = Normalization.For Failure allocationFailure database
  module Full = Transaction.Over Application.World Observation.Snapshot Failure database 671942183

  missingPreparation : Errors.AgentCorrection.Claim
  missingPreparation = Embedding.preparationDecision Errors.AgentCorrection.arguments
    (Validation.key "review" ∷ Validation.key "candidates" ∷ [])
    (Data.String.toList "Every new belief candidate requires complete embedding and current indexed document support before this review is committed.")

  module CompleteReview (input : Input.Review) (expected : ℤ)
    (prepared : List Reviewing.PreparedCandidate) where

    module Meaning (canonical : Review) = Reviewing.PreparedReview canonical expected clock now identities prepared

    convert : (canonical : Review) → Meaning.Result canonical → Full.Decision
    convert canonical (Meaning.refused failure) = Full.reject (reviewFailure failure)
    convert canonical Meaning.needsPreparation = Full.reject (preparationFailure missingPreparation)
    convert canonical (Meaning.replayed value) = Full.replay value
    convert canonical (Meaning.published after value limit) = Full.replace after value

    normalized : Application.World → Failure ⊎ (Store.World × Review) → Full.Allocation Full.Decision
    normalized before (inj₁ failure) = Full.resolved (Full.reject failure)
    normalized before (inj₂ (staged , canonical)) = Full.resolved
      (convert canonical (Meaning.intended canonical (record before { learning = staged })))

    liftAllocation : ∀ {A : Set} → Normalize.T.Allocation A → Full.Allocation A
    liftAllocation (Normalize.T.resolved value) = Full.resolved value
    liftAllocation (Normalize.T.reserve experience name source actor next) =
      Full.reserve experience name source actor (λ reply → liftAllocation (next reply))

    decideFull : Application.World → Full.Allocation Full.Decision
    decideFull before = Full.bindAllocation (liftAllocation (Normalize.review input (Application.learningView before))) (normalized before)

    module Plan = Full.PreparedPlan decideFull
    module CommitEvidence = Receipt.Over Application.World Observation.Snapshot Failure database 671942183
    module Confirmation = CommitEvidence.WithPreparedPlan decideFull

  recorded : Recording.Decision → T.Decision
  recorded (Recording.rejected failure) = T.reject (recordFailure failure)
  recorded (Recording.replay value) = T.replay value
  recorded (Recording.fresh after value limit) = T.replace after value

  reviewed : Reviewing.Decision → T.Decision
  reviewed (Reviewing.rejected failure) = T.reject (reviewFailure failure)
  reviewed (Reviewing.replay value) = T.replay value
  reviewed (Reviewing.fresh after value limit) = T.replace after value

  reviewReady : ℤ → Failure ⊎ (Store.World × Review) → T.Allocation T.Decision
  reviewReady expected (inj₁ failure) = T.resolved (T.reject failure)
  reviewReady expected (inj₂ (staged , canonical)) =
    T.resolved (reviewed (Reviewing.plan staged canonical expected clock now identities))

  decide : Request → Store.World → T.Allocation T.Decision
  decide (recordExperience sourceValue expected) before = T.bindAllocation (Normalize.experience sourceValue before) λ where
    (inj₁ failure) → T.resolved (T.reject failure)
    (inj₂ (staged , canonical)) → T.resolved (recorded (Recording.plan staged canonical expected now))
  decide (reviewExperience reviewValue expected) before =
    T.bindAllocation (Normalize.review reviewValue before) (reviewReady expected)

  module Plan = T.PreparedPlan (decide request)
  module CommitEvidence = Receipts.WithPreparedPlan (decide request)
  module ScopeEvidence = T.PreparedLaws (decide request)

  operationUsesLockedHandle : ∀ events outcome → T.E.Runs Plan.start events outcome →
    T.Trace T.outside events T.finished
  operationUsesLockedHandle = ScopeEvidence.completedScope

  operationSuccessRequiresCommit : ∀ events value →
    T.E.Runs Plan.start events (T.applied value) → Receipts.Receipt events
  operationSuccessRequiresCommit = CommitEvidence.successRequiresCommit

  -- A replay of this complete raw-request plan has no allocation or write
  -- effect after its locked read, regardless of the rollback acknowledgement.
  exactRetryOnlyRollsBack : ∀ tx before value events outcome →
    decide request before ≡ T.resolved (T.replay value) →
    T.E.Runs (Plan.afterRead tx (inj₂ before)) events outcome →
    Σ T.Cleanup (λ cleanup → events ≡ ((T.rollback tx , cleanup) Data.List.∷ Data.List.[]) ×
      outcome ≡ T.replayed value cleanup)
  exactRetryOnlyRollsBack tx before value events outcome unchanged rewrite unchanged =
    T.exactReplayOnlyRollback tx value events outcome

  recordedExperienceRetry : ∀ input expected before assigned value →
    Normalize.RecordedItems (Input.Experience.identity input) before (Input.Experience.items input) assigned →
    Recording.plan before (Input.canonicalExperience input assigned) expected now ≡ Recording.replay value →
    decide (recordExperience input expected) before ≡ T.resolved (T.replay value)
  recordedExperienceRetry input expected before assigned value recorded replay
    rewrite Normalize.recordedExperienceNeedsNoAllocation input before assigned recorded | replay = refl

  recordedReviewRetry : ∀ input expected before assigned resolved supported value →
    Normalize.RecordedItems (Input.Review.experienceID input) before (Input.Review.extracted input) assigned →
    Normalize.assessments (Store.World.itemKeys before) (Input.Review.experienceID input) (Input.Review.assessments input)
      ≡ inj₂ (resolved , supported) →
    Reviewing.plan before (Input.canonicalReview input assigned resolved) expected clock now identities ≡ Reviewing.replay value →
    decide (reviewExperience input expected) before ≡ T.resolved (T.replay value)
  recordedReviewRetry input expected before assigned resolved supported value recorded references replay
    rewrite Normalize.recordedReviewNeedsNoAllocation input before assigned resolved supported recorded references | replay = refl

  -- These whole-request retry laws take saved key/owner observations for
  -- every raw item. They do not assume the normalizer already returned the
  -- desired result and do not request a second PostgreSQL identity.
  namedExperienceRetry : ∀ input expected before assigned value →
    Normalize.NamedItems (Input.Experience.identity input) before (Input.Experience.items input) assigned →
    Recording.plan before (Input.canonicalExperience input assigned) expected now ≡ Recording.replay value →
    decide (recordExperience input expected) before ≡ T.resolved (T.replay value)
  namedExperienceRetry input expected before assigned value saved replay =
    recordedExperienceRetry input expected before assigned value
      (Normalize.namedItemsRecorded (Input.Experience.identity input) before (Input.Experience.items input) assigned saved) replay

  namedReviewRetry : ∀ input expected before assigned resolved supported value →
    Normalize.NamedItems (Input.Review.experienceID input) before (Input.Review.extracted input) assigned →
    Normalize.assessments (Store.World.itemKeys before) (Input.Review.experienceID input) (Input.Review.assessments input)
      ≡ inj₂ (resolved , supported) →
    Reviewing.plan before (Input.canonicalReview input assigned resolved) expected clock now identities ≡ Reviewing.replay value →
    decide (reviewExperience input expected) before ≡ T.resolved (T.replay value)
  namedReviewRetry input expected before assigned resolved supported value saved references replay =
    recordedReviewRetry input expected before assigned resolved supported value
      (Normalize.namedItemsRecorded (Input.Review.experienceID input) before (Input.Review.extracted input) assigned saved) references replay

  data Outcome : Set where
    invalidRequest : Failure → Outcome
    transacted : T.Outcome → Outcome
    reviewTransacted : Full.Outcome → Outcome
    preparationDecision : Errors.AgentCorrection.Claim → Outcome

  -- Standard serialization is external. Its failure is reported before any
  -- transaction. Successful encoding imposes no payload-size limit;
  -- allocation and canonical validation remain in Plan.start.
  data Serialization : Set where
    encoded : List Byte → Serialization
    serializationFailed : Text → Serialization

  data Effect : Set where
    serializePayload : Payload → Effect
    transaction : T.Effect → Effect
    prepareReview : Input.Review → ℤ → Effect
    reviewTransaction : Full.Effect → Effect

  Reply : Effect → Set
  Reply (serializePayload _) = Serialization
  Reply (transaction operation) = T.Reply operation
  Reply (prepareReview input expected) = Errors.AgentCorrection.Claim ⊎ List Reviewing.PreparedCandidate
  Reply (reviewTransaction operation) = Full.Reply operation

  module E = Effects.Protocol Effect Reply

  transact : T.E.Script T.Outcome → E.Script Outcome
  transact (T.E.done value) = E.done (transacted value)
  transact (T.E.ask operation next) = E.ask (transaction operation) (λ reply → transact (next reply))

  transactReview : Full.E.Script Full.Outcome → E.Script Outcome
  transactReview (Full.E.done value) = E.done (reviewTransacted value)
  transactReview (Full.E.ask operation next) = E.ask (reviewTransaction operation) (λ reply → transactReview (next reply))

  afterPreparation : (input : Input.Review) (expected : ℤ) → Reply (prepareReview input expected) → E.Script Outcome
  afterPreparation input expected (inj₁ report) = E.done (preparationDecision report)
  afterPreparation input expected (inj₂ values) = transactReview (CompleteReview.Plan.start input expected values)

  admittedStart : Request → E.Script Outcome
  admittedStart submitted@(recordExperience input expected) = transact (T.PreparedPlan.start (decide submitted))
  admittedStart (reviewExperience input expected) = E.ask (prepareReview input expected) (afterPreparation input expected)

  afterAdmission : E.Script Outcome
  afterAdmission with admit request
  ... | just failure = E.done (invalidRequest failure)
  ... | nothing = admittedStart request

  afterSerialization : Serialization → E.Script Outcome
  afterSerialization (serializationFailed message) = E.done (invalidRequest (externalFailure message))
  afterSerialization (encoded bytes) = afterAdmission

  start : E.Script Outcome
  start = E.ask (serializePayload (payload request)) afterSerialization

  publicEvent : T.E.Event → E.Event
  publicEvent (operation , reply) = transaction operation , reply

  transactRun : ∀ program events value → E.Runs (transact program) events (transacted value) →
    Σ (List T.E.Event) (λ original → T.E.Runs program original value × events ≡ map publicEvent original)
  transactRun (T.E.done value) .[] .value (E.returned .(transacted value)) = [] , T.E.returned value , refl
  transactRun (T.E.ask operation next) events value (E.replied _ _ reply execution)
    with transactRun (next reply) _ value execution
  ... | original , run , refl = (operation , reply) ∷ original , T.E.replied operation next reply run , refl

  PublicCommitReceipt : List E.Event → Set
  PublicCommitReceipt events = Σ T.Transaction
    (λ tx → Any (_≡ (transaction (T.commit tx) , T.committed)) events)

  liftCommitMember : ∀ tx {events} → Any (_≡ (T.commit tx , T.committed)) events →
    Any (_≡ (transaction (T.commit tx) , T.committed)) (map publicEvent events)
  liftCommitMember tx (here refl) = here refl
  liftCommitMember tx (there remaining) = there (liftCommitMember tx remaining)

  reviewCannotReturnRecorded : ∀ program events value →
    E.Runs (transactReview program) events (transacted value) → ⊥
  reviewCannotReturnRecorded (Full.E.done result) events value ()
  reviewCannotReturnRecorded (Full.E.ask operation next) events value (E.replied _ _ reply remaining) =
    reviewCannotReturnRecorded (next reply) _ value remaining

  preparationCannotReturnRecorded : ∀ input expected reply events value →
    E.Runs (afterPreparation input expected reply) events (transacted value) → ⊥
  preparationCannotReturnRecorded input expected (inj₁ report) events value ()
  preparationCannotReturnRecorded input expected (inj₂ prepared) events value execution =
    reviewCannotReturnRecorded (CompleteReview.Plan.start input expected prepared) events value execution

  admittedRecordRequiresCommit : ∀ submitted events value →
    E.Runs (admittedStart submitted) events (transacted (T.applied value)) → PublicCommitReceipt events
  admittedRecordRequiresCommit submitted@(recordExperience input expected) events value execution
    with transactRun (T.PreparedPlan.start (decide submitted)) events (T.applied value) execution
  ... | original , run , refl with Checks.successRequiresCommit original value run
    where module Checks = Receipts.WithPreparedPlan (decide submitted)
  ... | tx , observed = tx , liftCommitMember tx observed
  admittedRecordRequiresCommit (reviewExperience input expected) events value (E.replied _ _ reply execution) =
    ⊥-elim (preparationCannotReturnRecorded input expected reply _ (T.applied value) execution)

  admissionRequiresCommit : ∀ events value →
    E.Runs afterAdmission events (transacted (T.applied value)) → PublicCommitReceipt events
  admissionRequiresCommit events value execution with admit request
  ... | just failure with execution
  ...   | ()
  admissionRequiresCommit events value execution | nothing = admittedRecordRequiresCommit request events value execution

  completeReviewRequiresCommit : ∀ input expected prepared events value →
    Full.E.Runs (CompleteReview.Plan.start input expected prepared) events (Full.applied value) →
    CompleteReview.CommitEvidence.Receipt input expected prepared events
  completeReviewRequiresCommit input expected prepared =
    CompleteReview.Confirmation.successRequiresCommit input expected prepared

  preparationFailureStartsNoTransaction : ∀ input expected report events outcome →
    E.Runs (afterPreparation input expected (inj₁ report)) events outcome →
    events ≡ [] × outcome ≡ preparationDecision report
  preparationFailureStartsNoTransaction input expected report events outcome = E.completedCannotProduceEffects

  serializationRequiresCommit : ∀ reply events value →
    E.Runs (afterSerialization reply) events (transacted (T.applied value)) → PublicCommitReceipt events
  serializationRequiresCommit (serializationFailed message) events value ()
  serializationRequiresCommit (encoded bytes) events value execution = admissionRequiresCommit events value execution

  -- This is the complete public operation, including raw serialization,
  -- expected-revision admission, locked allocation and canonical validation.
  publicSuccessRequiresCommit : ∀ events value →
    E.Runs start events (transacted (T.applied value)) → PublicCommitReceipt events
  publicSuccessRequiresCommit events value (E.replied _ _ reply execution)
    with serializationRequiresCommit reply _ value execution
  ... | tx , observed = tx , there observed

  -- For every pair of successful encodings, including arbitrary lengths,
  -- the same transaction requests, replies and outcome remain possible.
  encodedLengthCannotChangeExecution : ∀ first second events outcome →
    E.Runs (afterSerialization (encoded first)) events outcome →
    E.Runs (afterSerialization (encoded second)) events outcome
  encodedLengthCannotChangeExecution first second events outcome execution = execution

  encodingFailureStartsNoTransaction : ∀ message events outcome →
    E.Runs (afterSerialization (serializationFailed message)) events outcome →
    events ≡ [] × outcome ≡ invalidRequest (externalFailure message)
  encodingFailureStartsNoTransaction message events outcome (E.returned _) = refl , refl

  invalidAdmissionStartsNoTransaction : ∀ bytes failure events outcome → admit request ≡ just failure →
    E.Runs (afterSerialization (encoded bytes)) events outcome →
    events ≡ [] × outcome ≡ invalidRequest failure
  invalidAdmissionStartsNoTransaction bytes failure events outcome rejected execution rewrite rejected =
    E.completedCannotProduceEffects execution

  -- CommitEvidence.successRequiresCommit is instantiated with decide request,
  -- so it applies to these actual plans rather than an arbitrary application
  -- callback. Replay and refusal have no write effect; uncertain commit is a
  -- distinct outcome and cannot produce an applied receipt.

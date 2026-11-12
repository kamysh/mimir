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
open import Mimir.UUIDGroups using (UUID)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (does; yes; no)
open import Mimir.Text using (Text)
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
import Mimir.PosteriorComputation as Posterior
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
  (clock : Candidate → ℤ) (now : ℤ) (identities : Candidate → UUID)
  (calculation : Posterior.Calculation) where

  module T = Transaction.Over Store.World Observation.Snapshot Failure database 671942183
  module Receipts = Receipt.Over Store.World Observation.Snapshot Failure database 671942183
  module Normalize = Normalization.For Failure allocationFailure database

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
    T.resolved (reviewed (Reviewing.plan calculation staged canonical expected clock now identities))

  decide : Request → Store.World → T.Allocation T.Decision
  decide (recordExperience sourceValue expected) before = T.bindAllocation (Normalize.experience sourceValue before) λ where
    (inj₁ failure) → T.resolved (T.reject failure)
    (inj₂ (staged , canonical)) → T.resolved (recorded (Recording.plan calculation staged canonical expected now))
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
    Recording.plan calculation before (Input.canonicalExperience input assigned) expected now ≡ Recording.replay value →
    decide (recordExperience input expected) before ≡ T.resolved (T.replay value)
  recordedExperienceRetry input expected before assigned value recorded replay
    rewrite Normalize.recordedExperienceNeedsNoAllocation input before assigned recorded | replay = refl

  recordedReviewRetry : ∀ input expected before assigned resolved supported value →
    Normalize.RecordedItems (Input.Review.experienceID input) before (Input.Review.extracted input) assigned →
    Normalize.assessments (Store.World.itemKeys before) (Input.Review.experienceID input) (Input.Review.assessments input)
      ≡ inj₂ (resolved , supported) →
    Reviewing.plan calculation before (Input.canonicalReview input assigned resolved) expected clock now identities ≡ Reviewing.replay value →
    decide (reviewExperience input expected) before ≡ T.resolved (T.replay value)
  recordedReviewRetry input expected before assigned resolved supported value recorded references replay
    rewrite Normalize.recordedReviewNeedsNoAllocation input before assigned resolved supported recorded references | replay = refl

  -- These whole-request retry laws take saved key/owner observations for
  -- every raw item. They do not assume the normalizer already returned the
  -- desired result and do not request a second PostgreSQL identity.
  namedExperienceRetry : ∀ input expected before assigned value →
    Normalize.NamedItems (Input.Experience.identity input) before (Input.Experience.items input) assigned →
    Recording.plan calculation before (Input.canonicalExperience input assigned) expected now ≡ Recording.replay value →
    decide (recordExperience input expected) before ≡ T.resolved (T.replay value)
  namedExperienceRetry input expected before assigned value saved replay =
    recordedExperienceRetry input expected before assigned value
      (Normalize.namedItemsRecorded (Input.Experience.identity input) before (Input.Experience.items input) assigned saved) replay

  namedReviewRetry : ∀ input expected before assigned resolved supported value →
    Normalize.NamedItems (Input.Review.experienceID input) before (Input.Review.extracted input) assigned →
    Normalize.assessments (Store.World.itemKeys before) (Input.Review.experienceID input) (Input.Review.assessments input)
      ≡ inj₂ (resolved , supported) →
    Reviewing.plan calculation before (Input.canonicalReview input assigned resolved) expected clock now identities ≡ Reviewing.replay value →
    decide (reviewExperience input expected) before ≡ T.resolved (T.replay value)
  namedReviewRetry input expected before assigned resolved supported value saved references replay =
    recordedReviewRetry input expected before assigned resolved supported value
      (Normalize.namedItemsRecorded (Input.Review.experienceID input) before (Input.Review.extracted input) assigned saved) references replay

  data Outcome : Set where
    invalidRequest : Failure → Outcome
    transacted : T.Outcome → Outcome

  -- Standard serialization is external. Its failure is reported before any
  -- transaction. Successful encoding imposes no payload-size limit;
  -- allocation and canonical validation remain in Plan.start.
  data Serialization : Set where
    encoded : List Byte → Serialization
    serializationFailed : Text → Serialization

  data Effect : Set where
    serializePayload : Payload → Effect
    transaction : T.Effect → Effect

  Reply : Effect → Set
  Reply (serializePayload _) = Serialization
  Reply (transaction operation) = T.Reply operation

  module E = Effects.Protocol Effect Reply

  transact : T.E.Script T.Outcome → E.Script Outcome
  transact (T.E.done value) = E.done (transacted value)
  transact (T.E.ask operation next) = E.ask (transaction operation) (λ reply → transact (next reply))

  afterAdmission : E.Script Outcome
  afterAdmission with admit request
  ... | just failure = E.done (invalidRequest failure)
  ... | nothing = transact Plan.start

  afterSerialization : Serialization → E.Script Outcome
  afterSerialization (serializationFailed message) = E.done (invalidRequest (externalFailure message))
  afterSerialization (encoded bytes) = afterAdmission

  start : E.Script Outcome
  start = E.ask (serializePayload (payload request)) afterSerialization

  -- Private preparation has an owned transaction. Its control carries the
  -- scope proof, so a rejected request cannot return with that handle open.
  -- Only a prepared transaction may proceed to the final commit.
  module Stage = T.Staging (decide request)

  data PreparationResult : Set where
    invalidPreparation : Failure → PreparationResult
    transactionPrepared : Stage.Result → PreparationResult

  data PreparationEffect : Set where
    encode : Payload → PreparationEffect
    stage : Stage.PreparationEffect → PreparationEffect

  PreparationReply : PreparationEffect → Set
  PreparationReply (encode _) = Serialization
  PreparationReply (stage effect) = Stage.PreparationReply effect

  module PreparationProtocol = Effects.Protocol PreparationEffect PreparationReply

  privatePreparation : ∀ {scope program} → Stage.StagedScope scope program →
    PreparationProtocol.Script PreparationResult
  privatePreparation {program = Stage.P.done result} proof = PreparationProtocol.done (transactionPrepared result)
  privatePreparation {program = Stage.P.ask effect continuation} (Stage.step transitions) =
    PreparationProtocol.ask (stage effect)
      (λ reply → privatePreparation (proj₂ (proj₂ (transitions reply))))

  encodedPreparation : Serialization → PreparationProtocol.Script PreparationResult
  encodedPreparation (serializationFailed detail) = PreparationProtocol.done (invalidPreparation (externalFailure detail))
  encodedPreparation (encoded bytes) with admit request
  ... | just failure = PreparationProtocol.done (invalidPreparation failure)
  ... | nothing = privatePreparation Stage.startScoped

  prepare : PreparationProtocol.Script PreparationResult
  prepare = PreparationProtocol.ask (encode (payload request)) encodedPreparation

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

  admissionRequiresCommit : ∀ events value →
    E.Runs afterAdmission events (transacted (T.applied value)) → PublicCommitReceipt events
  admissionRequiresCommit events value execution with admit request
  ... | just failure with execution
  ...   | ()
  admissionRequiresCommit events value execution | nothing with transactRun Plan.start events (T.applied value) execution
  ... | original , run , refl with operationSuccessRequiresCommit original value run
  ... | tx , observed = tx , liftCommitMember tx observed

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
  -- callback. Replay and refusal have no write effect; a failed commit cannot
  -- produce an applied receipt.

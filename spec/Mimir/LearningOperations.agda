{-# OPTIONS --safe #-}
-- Instantiate the transaction protocol with concrete Mimir plans and state.
-- Every successful fresh operation includes source/review history, ownership,
-- assessments, edges and numerical graph writes in its one proposed world.
module Mimir.LearningOperations where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Integer using (ℤ; +_)
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
import Mimir.Effects as Effects
open import Mimir.Bits using (Byte)

data Request : Set where
  recordExperience : Experience → ℤ → Request
  reviewExperience : Review → ℤ → Request

data Payload : Set where
  experiencePayload : Experience → Payload
  reviewPayload : Review → Payload

payload : Request → Payload
payload (recordExperience value expected) = experiencePayload value
payload (reviewExperience value expected) = reviewPayload value

data Failure : Set where
  recordFailure : Recording.Failure → Failure
  reviewFailure : Reviewing.Failure → Failure
  externalFailure : Text → Failure
  oversizedPayload : Failure

structure : Request → Maybe Failure
structure (recordExperience value expected) with ExperienceSchema.validate value
... | Validation.rejected failure refutation = just (recordFailure (Recording.invalid failure))
... | Validation.accepted valid = nothing
structure (reviewExperience value expected) with ReviewSchema.validateReview value
... | Validation.rejected failure refutation = just (reviewFailure (Reviewing.invalid failure))
... | Validation.accepted valid = nothing

expectedValid : ℤ → Data.Bool.Bool
expectedValid expected = does ((+ 0) Integer.≤? expected) ∧ does (expected Integer.<? (+ Bounds.i64Maximum))

admit : Request → Maybe Failure
admit (recordExperience sourceValue expected) with ExperienceSchema.validate sourceValue
... | Validation.rejected failure refutation = just (recordFailure (Recording.invalid failure))
... | Validation.accepted valid with expectedValid expected
...   | false = just (recordFailure Recording.invalidExpected)
...   | true = nothing
admit (reviewExperience reviewValue expected) with ReviewSchema.validateReview reviewValue
... | Validation.rejected failure refutation = just (reviewFailure (Reviewing.invalid failure))
... | Validation.accepted valid with expectedValid expected
...   | false = just (reviewFailure Reviewing.invalidExpected)
...   | true = nothing

module Protocol (database : ℕ) (request : Request)
  (clock : Candidate → ℤ) (now : ℤ) (identities : Candidate → ℕ) where

  module T = Transaction.Over Store.World Observation.Snapshot Failure database 671942183
  module Receipts = Receipt.Over Store.World Observation.Snapshot Failure database 671942183

  recorded : Recording.Decision → T.Decision
  recorded (Recording.rejected failure) = T.reject (recordFailure failure)
  recorded (Recording.replay value) = T.replay value
  recorded (Recording.fresh after value limit) = T.replace after value

  reviewed : Reviewing.Decision → T.Decision
  reviewed (Reviewing.rejected failure) = T.reject (reviewFailure failure)
  reviewed (Reviewing.replay value) = T.replay value
  reviewed (Reviewing.fresh after value limit) = T.replace after value

  decide : Request → Store.World → T.Decision
  decide (recordExperience sourceValue expected) before = recorded (Recording.plan before sourceValue expected now)
  decide (reviewExperience reviewValue expected) before = reviewed (Reviewing.plan before reviewValue expected clock now identities)

  module Plan = T.Plan (decide request)
  module CommitEvidence = Receipts.WithPlan (decide request)

  data Outcome : Set where
    invalidRequest : Failure → Outcome
    transacted : T.Outcome → Outcome

  afterAdmission : T.E.Script Outcome
  afterAdmission with admit request
  ... | just failure = T.E.done (invalidRequest failure)
  ... | nothing = T.E._>>=_ Plan.start (λ result → T.E.done (transacted result))

  -- Standard serde serialization is an external operation; its exact result
  -- determines Mimir's size admission. The model does not invent a formatter.
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

  lift : T.E.Script Outcome → E.Script Outcome
  lift (T.E.done value) = E.done value
  lift (T.E.ask operation next) = E.ask (transaction operation) (λ reply → lift (next reply))

  afterSerialization : Serialization → E.Script Outcome
  afterSerialization (serializationFailed message) = E.done (invalidRequest (externalFailure message))
  afterSerialization (encoded bytes) with length bytes ≤? 65536
  ... | no oversized = E.done (invalidRequest oversizedPayload)
  ... | yes bounded = lift afterAdmission

  start : E.Script Outcome
  start with structure request
  ... | just failure = E.done (invalidRequest failure)
  ... | nothing = E.ask (serializePayload (payload request)) afterSerialization

  -- CommitEvidence.successRequiresCommit is instantiated with decide request,
  -- so it applies to these actual plans rather than an arbitrary application
  -- callback. Replay and refusal have no write effect; uncertain commit is a
  -- distinct outcome and cannot produce an applied receipt.

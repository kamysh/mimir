{-# OPTIONS --safe #-}
-- Notification delivery owns its resources independently of review work.
-- These are transient process states, not stored recovery checkpoints. The
-- original complete message is the input of every fresh delivery attempt.
-- Configured delivery deadlines and retry delays are clock events. They do
-- not constrain review work. The queue retains failed or exhausted messages;
-- it never preserves a partially executed SMTP/OAuth operation.
-- Daily-report calendar wakes require the user's configured local delivery
-- time. Calendar interpretation is external: a skipped clock time uses the
-- first valid time afterward; a repeated time uses its first occurrence.
-- A successful report's day prevents another delivery for that same day.
module Mimir.NotificationDelivery where

open import Data.Product using (_×_; _,_; proj₁)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID)
import Mimir.NotificationConfig as Configuration

record Policy : Set where
  constructor deliveryPolicy
  field timeoutSeconds retrySeconds maxAttempts : ℕ

configuredPolicy : Configuration.Config → Policy
configuredPolicy settings = deliveryPolicy (Configuration.Config.timeoutSeconds settings)
  (Configuration.Config.retrySeconds settings) (Configuration.Config.maxAttempts settings)

record Message : Set where
  constructor notificationMessage
  field identity : UUID; subject body : Text; policy : Policy

data Delivery : Set where
  idle : Delivery
  starting : Message → ℕ → Delivery
  active : Message → Text → ℕ → Delivery -- transient owner; remaining attempts
  cleaning : Message → Text → Text → Text → Delivery
  needsInput : Message → Text → Text → Delivery
  cleaningRetry : Message → Text → ℕ → Delivery
  waiting : Message → ℕ → Delivery
  exhausted : Message → Delivery

data DeliveryEvent : Set where
  enqueue : Message → DeliveryEvent
  acquired : Text → DeliveryEvent
  failed : Text → Text → DeliveryEvent
  stopped : DeliveryEvent -- confirms all work/resources of the owned attempt stopped
  sentAndStopped : DeliveryEvent
  retryOriginal : DeliveryEvent
  temporaryFailure : DeliveryEvent
  deadlineExpired retryDelayExpired : ℕ → DeliveryEvent

data DeliveryStep : Delivery → DeliveryEvent → Delivery → Set where
  begin : ∀ message → DeliveryStep idle (enqueue message) (starting message (Policy.maxAttempts (Message.policy message)))
  own : ∀ message owner remaining → DeliveryStep (starting message (suc remaining)) (acquired owner) (active message owner remaining)
  noAttempts : ∀ message → DeliveryStep (starting message zero) stopped (exhausted message)
  failureBeforeOwnership : ∀ message remaining reason guidance →
    DeliveryStep (starting message remaining) (failed reason guidance) (needsInput message reason guidance)
  failureOwned : ∀ message owner remaining reason guidance →
    DeliveryStep (active message owner remaining) (failed reason guidance) (cleaning message owner reason guidance)
  cleanupConfirmed : ∀ message owner reason guidance →
    DeliveryStep (cleaning message owner reason guidance) stopped (needsInput message reason guidance)
  sent : ∀ message owner remaining → DeliveryStep (active message owner remaining) sentAndStopped idle
  retryable : ∀ message owner remaining →
    DeliveryStep (active message owner remaining) temporaryFailure (cleaningRetry message owner remaining)
  timedOut : ∀ message owner remaining →
    DeliveryStep (active message owner remaining)
      (deadlineExpired (Policy.timeoutSeconds (Message.policy message))) (cleaningRetry message owner remaining)
  scheduleRetry : ∀ message owner remaining →
    DeliveryStep (cleaningRetry message owner (suc remaining)) stopped (waiting message (suc remaining))
  attemptsUsed : ∀ message owner →
    DeliveryStep (cleaningRetry message owner zero) stopped (exhausted message)
  automaticRetry : ∀ message remaining →
    DeliveryStep (waiting message (suc remaining))
      (retryDelayExpired (Policy.retrySeconds (Message.policy message))) (starting message (suc remaining))
  freshRetry : ∀ message reason guidance →
    DeliveryStep (needsInput message reason guidance) retryOriginal (starting message (Policy.maxAttempts (Message.policy message)))

retryStartsFromOriginalInput : ∀ message reason guidance after →
  DeliveryStep (needsInput message reason guidance) retryOriginal after → after ≡ starting message (Policy.maxAttempts (Message.policy message))
retryStartsFromOriginalInput message reason guidance .(starting message (Policy.maxAttempts (Message.policy message))) (freshRetry .message .reason .guidance) = refl

-- A temporary failure has an automatic restart path after cleanup. No user
-- action, new review, configuration edit or new message is needed.
temporaryFailureSchedulesRetry : ∀ message owner remaining →
  DeliveryStep (cleaningRetry message owner (suc remaining)) stopped (waiting message (suc remaining))
temporaryFailureSchedulesRetry = scheduleRetry

configuredClockRestartsOriginal : ∀ message remaining →
  DeliveryStep (waiting message (suc remaining))
    (retryDelayExpired (Policy.retrySeconds (Message.policy message))) (starting message (suc remaining))
configuredClockRestartsOriginal = automaticRetry

ownedFailureRequiresCleanup : ∀ message owner reason guidance event →
  DeliveryStep (cleaning message owner reason guidance) event (needsInput message reason guidance) → event ≡ stopped
ownedFailureRequiresCleanup message owner reason guidance .stopped (cleanupConfirmed .message .owner .reason .guidance) = refl

-- The review transition is available for every delivery state, including a
-- stalled provider and a delivery waiting for user input. A mail failure can
-- never change the review state or remove a permitted review transition.
module Alongside (Review ReviewEvent : Set) (ReviewStep : Review → ReviewEvent → Review → Set) where
  State = Review × Delivery

  data Event : Set where
    review : ReviewEvent → Event
    delivery : DeliveryEvent → Event

  data Step : State → Event → State → Set where
    reviewProgress : ∀ before after worker event → ReviewStep before event after →
      Step (before , worker) (review event) (after , worker)
    deliveryProgress : ∀ reviewState before event after → DeliveryStep before event after →
      Step (reviewState , before) (delivery event) (reviewState , after)

  reviewNeverWaitsForMail : ∀ before after event worker → ReviewStep before event after →
    Step (before , worker) (review event) (after , worker)
  reviewNeverWaitsForMail before after event worker = reviewProgress before after worker event

  deliveryCannotChangeReview : ∀ before event after → Step before (delivery event) after → proj₁ after ≡ proj₁ before
  deliveryCannotChangeReview before event after (deliveryProgress _ _ _ _ _) = refl

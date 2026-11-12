{-# OPTIONS --safe #-}
-- Notification delivery owns its resources independently of review work.
-- These are transient process states, not stored recovery checkpoints. The
-- original complete message is the input of every fresh delivery attempt;
-- no SMTP/OAuth step, delay or attempt counter is persisted by this contract.
-- Daily-report calendar wakes require the user's configured local delivery
-- time. Calendar interpretation is external: a skipped clock time uses the
-- first valid time afterward; a repeated time uses its first occurrence.
-- A successful report's day prevents another delivery for that same day.
module Mimir.NotificationDelivery where

open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID)

record Message : Set where
  constructor notificationMessage
  field identity : UUID; subject body : Text

data Delivery : Set where
  idle : Delivery
  starting : Message → Delivery
  active : Message → Text → Delivery -- transient owner handle
  cleaning : Message → Text → Text → Text → Delivery
  needsInput : Message → Text → Text → Delivery

data DeliveryEvent : Set where
  enqueue : Message → DeliveryEvent
  acquired : Text → DeliveryEvent
  failed : Text → Text → DeliveryEvent
  stopped : DeliveryEvent -- confirms all work/resources of the owned attempt stopped
  sentAndStopped : DeliveryEvent
  retryOriginal : DeliveryEvent

data DeliveryStep : Delivery → DeliveryEvent → Delivery → Set where
  begin : ∀ message → DeliveryStep idle (enqueue message) (starting message)
  own : ∀ message owner → DeliveryStep (starting message) (acquired owner) (active message owner)
  failureBeforeOwnership : ∀ message reason guidance →
    DeliveryStep (starting message) (failed reason guidance) (needsInput message reason guidance)
  failureOwned : ∀ message owner reason guidance →
    DeliveryStep (active message owner) (failed reason guidance) (cleaning message owner reason guidance)
  cleanupConfirmed : ∀ message owner reason guidance →
    DeliveryStep (cleaning message owner reason guidance) stopped (needsInput message reason guidance)
  sent : ∀ message owner → DeliveryStep (active message owner) sentAndStopped idle
  freshRetry : ∀ message reason guidance →
    DeliveryStep (needsInput message reason guidance) retryOriginal (starting message)

retryStartsFromOriginalInput : ∀ message reason guidance after →
  DeliveryStep (needsInput message reason guidance) retryOriginal after → after ≡ starting message
retryStartsFromOriginalInput message reason guidance .(starting message) (freshRetry .message .reason .guidance) = refl

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

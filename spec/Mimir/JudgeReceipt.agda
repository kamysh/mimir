{-# OPTIONS --safe #-}
-- Only database observation evidence crosses into a confirmed controller
-- result. Malformed observations retain their precise diagnostic separately.
module Mimir.JudgeReceipt where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation using (Fault)
open import Mimir.JudgeAcknowledgement using (Evidence; evidence)
import Mimir.ReviewObservation as Observation
import Mimir.JudgeReview as Review

module Adapter (Payload : Set) (selected : Observation.Pin) where
  module C = Review.Controller Payload selected

  decode : Observation.Receipt selected → C.Receipt × Maybe Fault
  decode Observation.unavailable = C.unavailable , nothing
  decode (Observation.malformed failure) = C.unavailable , just failure
  decode (Observation.found observed valid (Observation.confirmed acknowledgement)) =
    C.acknowledged (evidence observed valid acknowledgement) , nothing
  decode (Observation.found observed valid (Observation.corrected identity changed)) = C.changed , nothing
  decode (Observation.found observed valid (Observation.pending identity same unconfirmed)) = C.pending , nothing

  diagnosticPreserved : ∀ failure → decode (Observation.malformed failure) ≡ (C.unavailable , just failure)
  diagnosticPreserved failure = refl

  -- Stop retains precedence even when a late verified receipt arrives; the
  -- controller's stop transition cancels the owned operations immediately.
  stopWins : ∀ state → C.step state C.stop ≡
    C.next (C.finished C.stopped) (C.cancelOwnedRequests ∷ [])
  stopWins state = C.stopImmediately state

  lateReceiptCannotRestart : ∀ receipt →
    C.step (C.finished C.stopped) (C.receipt receipt) ≡ C.next (C.finished C.stopped) []
  lateReceiptCannotRestart receipt = refl

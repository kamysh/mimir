{-# OPTIONS --safe #-}
-- Complete log entries are appended without rotation, truncation or retention
-- deletion. A failed append restores the previous contents before releasing
-- its owned handle; an acquisition failure owns no handle to clean up.
module Mimir.OperationalLogProtocol where

open import Data.List using (List; []; _∷_; _++_)
import Data.Sum
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte) public

Contents = List Byte

module For (directory : Text) where
  data Event : Set where
    acquired : Text → Text → Event
    lockFailed : Text → Text → Event
    read : Text → Contents → Event
    appended : Text → List Byte → Event
    appendFailed : Text → List Byte → Text → Event
    restored : Text → Contents → Event
    released : Text → Event

  data Outcome : Set where
    written : Contents → Outcome
    failed : Text → Contents → Outcome

  data Attempt (entry : List Byte) : List Event → Outcome → Set where
    acquisitionFailed : ∀ before error →
      Attempt entry (lockFailed directory error ∷ []) (failed error before)
    appendRejected : ∀ handle before error →
      Attempt entry
        (acquired directory handle ∷ read handle before ∷
         appendFailed handle entry error ∷ restored handle before ∷ released handle ∷ [])
        (failed error before)
    appendedComplete : ∀ handle before →
      Attempt entry
        (acquired directory handle ∷ read handle before ∷
         appended handle entry ∷ released handle ∷ [])
        (written (before ++ entry))

  writtenRequiresReceipts : ∀ entry events after → Attempt entry events (written after) →
    Σ Text (λ handle → Σ Contents (λ before →
      events ≡ (acquired directory handle ∷ read handle before ∷ appended handle entry ∷ released handle ∷ []) ×
      after ≡ before ++ entry))
  writtenRequiresReceipts entry events after (appendedComplete handle before) =
    handle , before , refl , refl

  -- The entire previous contents and entire entry remain in order. No file
  -- count, byte quota or clipped-entry operation exists in this contract.
  completeEntryRetained : ∀ entry events after → Attempt entry events (written after) →
    Σ Contents (λ before → after ≡ before ++ entry)
  completeEntryRetained entry events after (appendedComplete handle before) = before , refl

  failureHasReleasedOwnership : ∀ entry events error after → Attempt entry events (failed error after) →
    (events ≡ (lockFailed directory error ∷ [])) Data.Sum.⊎
    Σ Text (λ handle → Σ Contents (λ before →
      events ≡ (acquired directory handle ∷ read handle before ∷ appendFailed handle entry error ∷
        restored handle before ∷ released handle ∷ []) × after ≡ before))
  failureHasReleasedOwnership entry events error after (acquisitionFailed before error) = Data.Sum.inj₁ refl
  failureHasReleasedOwnership entry events error after (appendRejected handle before error) =
    Data.Sum.inj₂ (handle , before , refl , refl)

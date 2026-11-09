{-# OPTIONS --safe #-}
-- Completed native observations for append-only writes under one owned lock.
-- An acknowledgement includes the complete entry, not a clipped substitute.
module Mimir.OperationalLogProtocol where

open import Data.List using (List; []; _∷_; take; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.OperationalLogRetention as Log

module For (directory : Text) where
  data Event : Set where
    acquired : Text → ℕ → Event
    lockFailed : Text → Text → Event
    appended : ℕ → List Log.Byte → Log.State → Event
    appendFailed : ℕ → List Log.Byte → ℕ → Text → Event
    released : ℕ → Event

  data Outcome : Set where
    written : Log.State → Outcome
    failed : Text → Maybe Log.State → Outcome

  -- Prior contents belong to the filesystem observation. Appending does not
  -- require a metadata/read operation. Descriptor close releases the lock.
  data Attempt (entry : List Log.Byte) : List Event → Outcome → Set where
    denied : ∀ error → Attempt entry (lockFailed directory error ∷ []) (failed error nothing)
    writeFailed : ∀ handle before count error → count ≤ length entry →
      Attempt entry (acquired directory handle ∷ appendFailed handle entry count error ∷ released handle ∷ [])
        (failed error (just (Log.append (take count entry) before)))
    saved : ∀ handle before →
      Attempt entry (acquired directory handle ∷ appended handle entry before ∷ released handle ∷ [])
        (written (Log.append entry before))

  writtenRequiresReceipts : ∀ entry events after → Attempt entry events (written after) →
    Σ ℕ (λ handle → Σ Log.State (λ before →
      events ≡ acquired directory handle ∷ appended handle entry before ∷ released handle ∷ [] ×
      after ≡ Log.append entry before))
  writtenRequiresReceipts entry events after (saved handle before) = handle , before , refl , refl

  data Scope : Set where outside : Scope; owned : ℕ → Scope

  data Allowed : Scope → Event → Scope → Set where
    lock : ∀ handle → Allowed outside (acquired directory handle) (owned handle)
    refused : ∀ error → Allowed outside (lockFailed directory error) outside
    wrote : ∀ handle bytes before → Allowed (owned handle) (appended handle bytes before) (owned handle)
    partial : ∀ handle bytes count error → Allowed (owned handle) (appendFailed handle bytes count error) (owned handle)
    closed : ∀ handle → Allowed (owned handle) (released handle) outside

  data Trace : Scope → List Event → Scope → Set where
    empty : ∀ scope → Trace scope [] scope
    more : ∀ {before middle after event events} → Allowed before event middle → Trace middle events after →
      Trace before (event ∷ events) after

  attemptOwnsEveryFileOperation : ∀ entry events outcome → Attempt entry events outcome → Trace outside events outside
  attemptOwnsEveryFileOperation entry events outcome (denied error) = more (refused error) (empty outside)
  attemptOwnsEveryFileOperation entry events outcome (writeFailed handle before count error bounded) =
    more (lock handle) (more (partial handle entry count error) (more (closed handle) (empty outside)))
  attemptOwnsEveryFileOperation entry events outcome (saved handle before) =
    more (lock handle) (more (wrote handle entry before) (more (closed handle) (empty outside)))

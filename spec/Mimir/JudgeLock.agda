{-# OPTIONS --safe #-}
-- Lock lifecycle, including all early closes, contention and destructor order.
-- Permission evidence records the observed inode; it is not an assertion that
-- an external process cannot subsequently mutate the filesystem.
module Mimir.JudgeLock where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.UnixMetadata using (Metadata; UserId; Lock)
import Mimir.UnixMetadata as M
import Mimir.JudgeFilesystem as F
import Mimir.JudgeDirectory as D

module With (Path Handle NativeError : Set) where
  module FS = F.With Path Handle NativeError
  module Directory = D.With Path Handle NativeError
  open FS

  record Locked : Set where
    constructor locked
    field path : Path; handle : Handle; observed : Metadata; user : UserId
          valid : Lock user observed

  afterLock : Locked → IO Data.Unit.⊤ → Script (Result (Maybe Locked))
  afterLock held (inj₂ _) = done (inj₂ (just held))
  afterLock held (inj₁ error) with IOError.kind error
  ... | wouldBlock = finallyClose (Locked.handle held) (inj₂ nothing)
  ... | missing = finallyClose (Locked.handle held) (inj₁ (native error))
  ... | exists = finallyClose (Locked.handle held) (inj₁ (native error))
  ... | other = finallyClose (Locked.handle held) (inj₁ (native error))

  requestLock : Locked → Script (Result (Maybe Locked))
  requestLock held = ask (exclusiveNonblockingLock (Locked.handle held)) (afterLock held)

  checkOwner : Path → Handle → (observed : Metadata) →
    M.IsRegular (Metadata.kind observed) → UserId → Script (Result (Maybe Locked))
  checkOwner path handle observed kind user with M.ownedPrivate? user observed
  ... | no _ = finallyClose handle (inj₁ unsafeLock)
  ... | yes owned = requestLock (locked path handle observed user (kind , owned))

  checkFile : Path → Handle → Metadata → Script (Result (Maybe Locked))
  checkFile path handle observed with M.regular? (Metadata.kind observed)
  ... | no _ = finallyClose handle (inj₁ unsafeLock)
  ... | yes kind = ask effectiveUser (checkOwner path handle observed kind)

  inspectFile : Path → Handle → Script (Result (Maybe Locked))
  inspectFile path handle = ask (fileMetadata handle) λ where
    (inj₁ error) → finallyClose handle (inj₁ (native error))
    (inj₂ observed) → checkFile path handle observed

  openLock : Path → Path → Script (Result (Maybe Locked))
  openLock path lockPath = ask (openFile lockPath lockReadWriteCreate0600NoFollowCloseOnExec) λ where
    (inj₁ error) → done (inj₁ (native error))
    (inj₂ handle) → inspectFile path handle

  acquire : Path → Path → Maybe (List Path) → Script (Result (Maybe Locked))
  acquire path lockPath ancestors = Directory.ensureParents ancestors >>= λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ _) → Directory.ensureDirectory path >>= λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ _) → openLock path lockPath

  release : Locked → Script Data.Unit.⊤
  release held = ask (unlock (Locked.handle held))
    (λ _ → finallyClose (Locked.handle held) tt)

  closeResult : ∀ {A : Set} handle (result final : A) events →
    Runs (finallyClose handle result) events final →
    final ≡ result × events ≡ ((close handle , tt) ∷ [])
  closeResult handle result final events (replied _ _ tt (returned _)) = refl , refl

  -- Unlock failure is ignored, but the descriptor still closes exactly once.
  releaseTrace : ∀ held events result → Runs (release held) events result →
    Data.Product.Σ (IO Data.Unit.⊤) (λ reply →
      events ≡ ((unlock (Locked.handle held) , reply) ∷
        (close (Locked.handle held) , tt) ∷ []))
  releaseTrace held events result (replied _ _ reply (replied _ _ tt (returned _))) = reply , refl

  -- A successful flock reply yields ownership without closing the descriptor.
  successfulLock : ∀ held →
    Runs (requestLock held)
      ((exclusiveNonblockingLock (Locked.handle held) , inj₂ tt) ∷ [])
      (inj₂ (just held))
  successfulLock held = replied _ _ (inj₂ tt) (returned _)

  -- This proves necessity, independently of the success-path construction.
  lockSuccessRequiresReceipt : ∀ held events acquired →
    Runs (requestLock held) events (inj₂ (just acquired)) →
    events ≡ ((exclusiveNonblockingLock (Locked.handle held) , inj₂ tt) ∷ []) ×
      acquired ≡ held
  lockSuccessRequiresReceipt held events acquired (replied _ _ (inj₂ tt) (returned _)) = refl , refl
  lockSuccessRequiresReceipt held events acquired (replied _ _ (inj₁ error) rest)
    with IOError.kind error
  ... | wouldBlock with rest
  ...   | replied _ _ tt ()
  lockSuccessRequiresReceipt held events acquired (replied _ _ (inj₁ error) rest) | missing with rest
  ... | replied _ _ tt ()
  lockSuccessRequiresReceipt held events acquired (replied _ _ (inj₁ error) rest) | exists with rest
  ... | replied _ _ tt ()
  lockSuccessRequiresReceipt held events acquired (replied _ _ (inj₁ error) rest) | other with rest
  ... | replied _ _ tt ()

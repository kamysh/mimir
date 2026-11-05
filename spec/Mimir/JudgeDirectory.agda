{-# OPTIONS --safe #-}
-- Parent and state-directory checks in their native order, with admitted
-- observed retained in successful results. Parent traversal order is supplied
-- by the path layer, not silently normalized here.
module Mimir.JudgeDirectory where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; Σ; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.UnixMetadata using (Metadata; UserId; Parent; Directory)
import Mimir.UnixMetadata as M
import Mimir.JudgeFilesystem as F
import Mimir.EffectsComposition as Composition

module With (Path Handle NativeError : Set) where
  module FS = F.With Path Handle NativeError
  open FS
  module C = Composition.With Operation Reply

  record CheckedDirectory : Set where
    constructor checkedDirectory
    field observed : Metadata; user : UserId; valid : Directory user observed

  record CheckedParent : Set where
    constructor checkedParent
    field path : Path; observed : Metadata; valid : Parent observed

  checkOwnership : (observed : Metadata) → M.IsDirectory (Metadata.kind observed) → UserId →
    Script (Result CheckedDirectory)
  checkOwnership observed kind user with M.ownedPrivate? user observed
  ... | no _ = done (inj₁ directoryOwnership)
  ... | yes owned = done (inj₂ (checkedDirectory observed user (kind , owned)))

  checkDirectory : Metadata → Script (Result CheckedDirectory)
  checkDirectory observed with M.directory? (Metadata.kind observed)
  ... | no _ = done (inj₁ directoryKind)
  ... | yes kind = ask effectiveUser (checkOwnership observed kind)

  verifyDirectory : Path → Script (Result CheckedDirectory)
  verifyDirectory path = ask (symlinkMetadata path) λ where
    (inj₁ _) → done (inj₁ inspectDirectory)
    (inj₂ observed) → checkDirectory observed

  checkParent : Path → Metadata → Result CheckedParent
  checkParent path observed with M.directory? (Metadata.kind observed)
  ... | no _ = inj₁ parentKind
  ... | yes _ with M.parent? observed
  ...   | no _ = inj₁ parentWritable
  ...   | yes valid = inj₂ (checkedParent path observed valid)

  prependParent : CheckedParent → Result (List CheckedParent) → Result (List CheckedParent)
  prependParent checked (inj₁ error) = inj₁ error
  prependParent checked (inj₂ parents) = inj₂ (checked ∷ parents)

  continueParents : Path → List Path →
    (List Path → Script (Result (List CheckedParent))) →
    IO Metadata → Script (Result (List CheckedParent))
  continueParents path remaining next (inj₁ _) = done (inj₁ inspectParent)
  continueParents path remaining next (inj₂ observed) with checkParent path observed
  ... | inj₁ error = done (inj₁ error)
  ... | inj₂ checked = C.mapResult (prependParent checked) (next remaining)

  verifyList : List Path → Script (Result (List CheckedParent))
  verifyList [] = done (inj₂ [])
  verifyList (path ∷ rest) = ask (symlinkMetadata path)
    (continueParents path rest (λ _ → verifyList rest))

  verifyParents : Maybe (List Path) → Script (Result (List CheckedParent))
  verifyParents nothing = done (inj₁ noParent)
  verifyParents (just paths) = verifyList paths

  createAncestors : List Path → Script (Result ⊤)
  createAncestors [] = done (inj₂ tt)
  createAncestors (path ∷ rest) = ask (pathExists path) λ where
    true → createAncestors rest
    false → ask (createDirectory0700 path) λ where
      (inj₁ _) → done (inj₁ createParent)
      (inj₂ _) → createAncestors rest

  ensureParents : Maybe (List Path) → Script (Result (List CheckedParent))
  ensureParents nothing = done (inj₁ noParent)
  ensureParents (just paths) = createAncestors (reverse paths) >>= λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ _) → verifyList paths

  -- AlreadyExists is tolerated for the state directory alone. A parent create
  -- failure, including that same native error kind, terminates the traversal.
  afterCreateDirectory : Path → IO ⊤ → Script (Result CheckedDirectory)
  afterCreateDirectory path (inj₂ _) = verifyDirectory path
  afterCreateDirectory path (inj₁ error) with IOError.kind error
  ... | exists = verifyDirectory path
  ... | missing = done (inj₁ createDirectory)
  ... | wouldBlock = done (inj₁ createDirectory)
  ... | other = done (inj₁ createDirectory)

  ensureDirectory : Path → Script (Result CheckedDirectory)
  ensureDirectory path = ask (pathExists path) λ where
    true → verifyDirectory path
    false → ask (createDirectory0700 path) (afterCreateDirectory path)

  rejectedKindDoesNotReadUser : ∀ observed →
    (M.IsDirectory (Metadata.kind observed) → ⊥) →
    checkDirectory observed ≡ done (inj₁ directoryKind)
  rejectedKindDoesNotReadUser observed rejected with M.directory? (Metadata.kind observed)
  ... | no _ = refl
  ... | yes valid = ⊥-elim (rejected valid)

  ownershipSuccess : ∀ observed kind user events checked →
    Runs (checkOwnership observed kind user) events (inj₂ checked) →
    events ≡ [] × CheckedDirectory.observed checked ≡ observed ×
      CheckedDirectory.user checked ≡ user
  ownershipSuccess observed kind user events checked run with M.ownedPrivate? user observed
  ... | no _ with run
  ...   | ()
  ownershipSuccess observed kind user events checked run | yes owned with run
  ... | returned _ = refl , refl , refl

  directorySuccess : ∀ observed events checked →
    Runs (checkDirectory observed) events (inj₂ checked) →
    events ≡ ((effectiveUser , CheckedDirectory.user checked) ∷ []) ×
      CheckedDirectory.observed checked ≡ observed
  directorySuccess observed events checked run with M.directory? (Metadata.kind observed)
  ... | no _ with run
  ...   | ()
  directorySuccess observed events checked run | yes kind with run
  ... | replied _ _ user rest with ownershipSuccess observed kind user _ checked rest
  ...   | refl , refl , refl = refl , refl

  -- A success contains the exact metadata receipt and the effective-user
  -- receipt that justified it, in native order. No caller-supplied proof can
  -- substitute different metadata for what the filesystem actually replied.
  verifyDirectorySuccess : ∀ path events checked →
    Runs (verifyDirectory path) events (inj₂ checked) →
    events ≡ ((symlinkMetadata path , inj₂ (CheckedDirectory.observed checked)) ∷
      (effectiveUser , CheckedDirectory.user checked) ∷ [])
  verifyDirectorySuccess path events checked (replied _ _ (inj₁ error) ())
  verifyDirectorySuccess path events checked (replied _ _ (inj₂ observed) rest)
    with directorySuccess observed _ checked rest
  ... | refl , refl = refl

  parentSuccess : ∀ path observed checked → checkParent path observed ≡ inj₂ checked →
    CheckedParent.path checked ≡ path × CheckedParent.observed checked ≡ observed
  parentSuccess path observed checked receipt with M.directory? (Metadata.kind observed)
  ... | no _ with receipt
  ...   | ()
  parentSuccess path observed checked receipt | yes _ with M.parent? observed
  ... | no _ with receipt
  ...   | ()
  parentSuccess path observed checked receipt | yes _ | yes valid with receipt
  ... | refl = refl , refl

  data ParentReceipts : List Path → List CheckedParent → List Event → Set where
    empty : ParentReceipts [] [] []
    next : ∀ {path paths checked parents events} → CheckedParent.path checked ≡ path →
      ParentReceipts paths parents events →
      ParentReceipts (path ∷ paths) (checked ∷ parents)
        ((symlinkMetadata path , inj₂ (CheckedParent.observed checked)) ∷ events)

  verifyListSuccess : ∀ paths events parents → Runs (verifyList paths) events (inj₂ parents) →
    ParentReceipts paths parents events
  verifyListSuccess [] events parents (returned _) = empty
  verifyListSuccess (path ∷ paths) events parents (replied _ _ (inj₁ error) ())
  verifyListSuccess (path ∷ paths) events parents (replied _ _ (inj₂ observed) run)
    with checkParent path observed in chosen
  ... | inj₁ error with run
  ...   | ()
  verifyListSuccess (path ∷ paths) events parents (replied _ _ (inj₂ observed) run)
    | inj₂ checked with C.unmap (prependParent checked) (verifyList paths) run
  ... | inj₁ error , prior , ()
  ... | inj₂ remaining , prior , refl with parentSuccess path observed checked chosen
  ...   | pathExact , refl = next pathExact (verifyListSuccess paths _ remaining prior)

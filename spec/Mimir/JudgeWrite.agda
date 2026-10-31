{-# OPTIONS --safe #-}
-- Detailed replacement lifecycle refining the intended AtomicFile protocol.
-- It deliberately corrects the existing Rust cleanup bug: a failed exclusive
-- create owns no temporary file and cannot authorize removal of that path.
module Mimir.JudgeWrite where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.JudgeFilesystem as F

module With (Path Handle NativeError : Set) where
  module FS = F.With Path Handle NativeError
  open FS

  data Failure : Set where creation writing fileSync replacement directoryOpen directorySync : Failure
  data Outcome : Set where
    committed : Outcome
    unchanged uncertain : Failure → IOError → Outcome

  cleanup : Path → Handle → Outcome → Script Outcome
  cleanup temporary handle outcome = ask (close handle) λ _ →
    ask (removeFile temporary) (λ _ → done outcome)

  finishDirectory : Handle → Handle → IO ⊤ → Script Outcome
  finishDirectory file directoryHandle (inj₁ error) =
    ask (close directoryHandle) (λ _ → finallyClose file (uncertain directorySync error))
  finishDirectory file directoryHandle (inj₂ _) =
    ask (close directoryHandle) (λ _ → finallyClose file committed)

  afterDirectoryOpen : Handle → IO Handle → Script Outcome
  afterDirectoryOpen file (inj₁ error) = finallyClose file (uncertain directoryOpen error)
  afterDirectoryOpen file (inj₂ directoryHandle) =
    ask (syncAll directoryHandle) (finishDirectory file directoryHandle)

  afterRename : Path → Handle → Script Outcome
  afterRename directory file = ask (openFile directory readDirectory) (afterDirectoryOpen file)

  replaceName : Path → Path → Path → Handle → Script Outcome
  replaceName temporary target directory file = ask (rename temporary target) λ where
    (inj₁ error) → cleanup temporary file (unchanged replacement error)
    (inj₂ _) → afterRename directory file

  syncTemporary : Path → Path → Path → Handle → Script Outcome
  syncTemporary temporary target directory file = ask (syncAll file) λ where
    (inj₁ error) → cleanup temporary file (unchanged fileSync error)
    (inj₂ _) → replaceName temporary target directory file

  writeTemporary : Path → Path → Path → List Byte → Handle → Script Outcome
  writeTemporary temporary target directory bytes file = ask (writeAll file bytes) λ where
    (inj₁ error) → cleanup temporary file (unchanged writing error)
    (inj₂ _) → syncTemporary temporary target directory file

  replace : Path → Path → Path → List Byte → Script Outcome
  replace temporary target directory bytes = ask (openFile temporary exclusiveWrite0600NoFollowCloseOnExec) λ where
    (inj₁ error) → done (unchanged creation error)
    (inj₂ file) → writeTemporary temporary target directory bytes file

  creationFailure : ∀ temporary target directory bytes error events outcome →
    Runs (replace temporary target directory bytes)
      ((openFile temporary exclusiveWrite0600NoFollowCloseOnExec , inj₁ error) ∷ events) outcome →
    events ≡ [] × outcome ≡ unchanged creation error
  creationFailure temporary target directory bytes error events outcome
    (replied _ _ _ (returned _)) = refl , refl

  data ContainsRemoval : List Event → Set where
    here : ∀ path reply rest → ContainsRemoval ((removeFile path , reply) ∷ rest)
    later : ∀ event {rest} → ContainsRemoval rest → ContainsRemoval (event ∷ rest)

  cleanupRequiresCreation : ∀ temporary target directory bytes events outcome →
    Runs (replace temporary target directory bytes) events outcome → ContainsRemoval events →
    Σ Handle (λ handle → Σ (List Event) (λ rest →
      events ≡ ((openFile temporary exclusiveWrite0600NoFollowCloseOnExec , inj₂ handle) ∷ rest)))
  cleanupRequiresCreation temporary target directory bytes events outcome
    (replied _ _ (inj₂ handle) run) removed = handle , _ , refl
  cleanupRequiresCreation temporary target directory bytes events outcome
    (replied _ _ (inj₁ error) (returned _)) (later _ ())

  successTrace : Path → Path → Path → List Byte → Handle → Handle → List Event
  successTrace temporary target directory bytes file directoryHandle =
    (openFile temporary exclusiveWrite0600NoFollowCloseOnExec , inj₂ file) ∷
    (writeAll file bytes , inj₂ tt) ∷ (syncAll file , inj₂ tt) ∷
    (rename temporary target , inj₂ tt) ∷ (openFile directory readDirectory , inj₂ directoryHandle) ∷
    (syncAll directoryHandle , inj₂ tt) ∷ (close directoryHandle , tt) ∷ (close file , tt) ∷ []

  cleanupCannotCommit : ∀ temporary handle failure error events →
    Runs (cleanup temporary handle (unchanged failure error)) events committed → Data.Empty.⊥
  cleanupCannotCommit temporary handle failure error events (replied _ _ _ (replied _ _ _ ()))

  afterRenameSuccess : ∀ directory file events → Runs (afterRename directory file) events committed →
    Σ Handle (λ directoryHandle → events ≡
      ((openFile directory readDirectory , inj₂ directoryHandle) ∷
        (syncAll directoryHandle , inj₂ tt) ∷ (close directoryHandle , tt) ∷ (close file , tt) ∷ []))
  afterRenameSuccess directory file events (replied _ _ (inj₁ error) (replied _ _ _ ()))
  afterRenameSuccess directory file events
    (replied _ _ (inj₂ directoryHandle) (replied _ _ (inj₁ error) (replied _ _ _ (replied _ _ _ ()))))
  afterRenameSuccess directory file events
    (replied _ _ (inj₂ directoryHandle) (replied _ _ (inj₂ tt) (replied _ _ tt (replied _ _ tt (returned _))))) =
    directoryHandle , refl

  committedRequiresReceipts : ∀ temporary target directory bytes events →
    Runs (replace temporary target directory bytes) events committed →
    Σ Handle (λ file → Σ Handle (λ directoryHandle →
      events ≡ successTrace temporary target directory bytes file directoryHandle))
  committedRequiresReceipts temporary target directory bytes events (replied _ _ (inj₁ error) ())
  committedRequiresReceipts temporary target directory bytes events
    (replied _ _ (inj₂ file) (replied _ _ (inj₁ error) rest)) =
    Data.Empty.⊥-elim (cleanupCannotCommit temporary file writing error _ rest)
  committedRequiresReceipts temporary target directory bytes events
    (replied _ _ (inj₂ file) (replied _ _ (inj₂ tt) (replied _ _ (inj₁ error) rest))) =
    Data.Empty.⊥-elim (cleanupCannotCommit temporary file fileSync error _ rest)
  committedRequiresReceipts temporary target directory bytes events
    (replied _ _ (inj₂ file) (replied _ _ (inj₂ tt) (replied _ _ (inj₂ tt) (replied _ _ (inj₁ error) rest)))) =
    Data.Empty.⊥-elim (cleanupCannotCommit temporary file replacement error _ rest)
  committedRequiresReceipts temporary target directory bytes events
    (replied _ _ (inj₂ file) (replied _ _ (inj₂ tt) (replied _ _ (inj₂ tt) (replied _ _ (inj₂ tt) rest))))
    with afterRenameSuccess directory file _ rest
  ... | directoryHandle , refl = file , directoryHandle , refl

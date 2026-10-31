{-# OPTIONS --safe #-}
-- Public success/error results of the concrete write protocol. Both failure
-- before rename and durability uncertainty remain errors; a success can only
-- originate from the complete sequence of successful persistence receipts.
module Mimir.JudgeWriteReceipt where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.JudgeWrite as W
import Mimir.EffectsComposition as C

module With (Path Handle NativeError : Set) where
  module Write = W.With Path Handle NativeError
  open Write.FS
  module Composition = C.With Operation Reply

  outcome : Write.Outcome → Result ⊤
  outcome Write.committed = inj₂ tt
  outcome (Write.unchanged _ error) = inj₁ (native error)
  outcome (Write.uncertain _ error) = inj₁ (native error)

  write : Path → Path → Path → List Byte → Script (Result ⊤)
  write temporary target directory bytes =
    Composition.mapResult outcome (Write.replace temporary target directory bytes)

  successRequiresReceipts : ∀ temporary target directory bytes events →
    Runs (write temporary target directory bytes) events (inj₂ tt) →
    Σ Handle (λ file → Σ Handle (λ directoryHandle →
      events ≡ Write.successTrace temporary target directory bytes file directoryHandle))
  successRequiresReceipts temporary target directory bytes events run with
    Composition.unmap outcome (Write.replace temporary target directory bytes) run
  ... | Write.committed , executed , refl = Write.committedRequiresReceipts temporary target directory bytes events executed
  ... | Write.unchanged _ error , executed , ()
  ... | Write.uncertain _ error , executed , ()

  creationFailureDoesNotRemove : ∀ temporary target directory bytes error events result →
    Runs (write temporary target directory bytes)
      ((openFile temporary exclusiveWrite0600NoFollowCloseOnExec , inj₁ error) ∷ events) result →
    events ≡ [] × result ≡ inj₁ (native error)
  creationFailureDoesNotRemove temporary target directory bytes error events result run with
    Composition.unmap outcome (Write.replace temporary target directory bytes) run
  ... | reported , executed , same with Write.creationFailure temporary target directory bytes error events reported executed
  ... | refl , refl with same
  ... | refl = refl , refl

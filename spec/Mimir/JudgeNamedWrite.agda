{-# OPTIONS --safe #-}
-- Serialization precedes size admission; entropy precedes filesystem mutation.
-- The filesystem program implements the approved creation-ownership correction.
module Mimir.JudgeNamedWrite where

open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (_≤_; _≤?_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Mimir.Bits using (Byte)
open import Mimir.UnixPath using (Path; join)
open import Mimir.JudgePersistence using (Name; filename; limit; temporaryName)
open import Mimir.UUIDGroups using (UUID)
open import Mimir.UUIDV4 using (Endian; fromRandom)
import Mimir.JudgeWriteReceipt as WriteReceipt
import Mimir.Effects as Effects

module With (Handle NativeError RandomError EncodeError : Set) where
  module W = WriteReceipt.With Path Handle NativeError
  module FS = W.Write.FS

  data Operation : Set where
    filesystem : FS.Operation → Operation
    randomBytes16 : Operation

  Reply : Operation → Set
  Reply (filesystem operation) = FS.Reply operation
  Reply randomBytes16 = RandomError ⊎ UUID

  module P = Effects.Protocol Operation Reply
  open P

  data Outcome : Set where
    encodingFailed : EncodeError → Outcome
    panicked : RandomError → Outcome
    returned : FS.Result ⊤ → Outcome

  event : FS.Event → Event
  event (operation , response) = filesystem operation , response

  embed : FS.Script (FS.Result ⊤) → Script Outcome
  embed (FS.done result) = done (returned result)
  embed (FS.ask operation continue) = ask (filesystem operation) (λ response → embed (continue response))

  reflect : ∀ program {events result} → Runs (embed program) events (returned result) →
    Σ (List FS.Event) (λ original → FS.Runs program original result × events ≡ map event original)
  reflect (FS.done value) (P.returned _) = [] , FS.returned value , refl
  reflect (FS.ask operation continue) (P.replied _ _ response run) with reflect (continue response) run
  ... | original , executed , exact = (operation , response) ∷ original ,
    FS.replied operation continue response executed , cong ((filesystem operation , response) ∷_) exact

  record EmbeddedCommit (temporary target directory : Path) (bytes : List Byte)
    (events : List Event) : Set where
    constructor embeddedCommit
    field
      file directoryHandle : Handle
      exactTrace : events ≡ map event
        (W.Write.successTrace temporary target directory bytes file directoryHandle)

  abstract
    embeddedSuccess : ∀ temporary target directory bytes {events} →
      Runs (embed (W.write temporary target directory bytes)) events (returned (inj₂ tt)) →
      EmbeddedCommit temporary target directory bytes events
    embeddedSuccess temporary target directory bytes run with reflect (W.write temporary target directory bytes) run
    ... | original , executed , exact with W.successRequiresReceipts temporary target directory bytes original executed
    ... | file , directoryHandle , originalExact = embeddedCommit file directoryHandle
      (trans exact (cong (map event) originalExact))

  afterEntropy : Path → Name → Endian → List Byte → Reply randomBytes16 → Script Outcome
  afterEntropy directory name endian bytes (inj₁ error) = done (panicked error)
  afterEntropy directory name endian bytes (inj₂ random) = embed
    (W.write (join directory (temporaryName name (fromRandom endian random)))
      (join directory (filename name)) directory bytes)

  writeBytes : Path → Name → Endian → List Byte → Script Outcome
  writeBytes directory name endian bytes with length bytes ≤? limit name
  ... | no oversized = done (returned (inj₁ FS.oversizedWrite))
  ... | yes admitted = ask randomBytes16 (afterEntropy directory name endian bytes)

  writeEncoded : Path → Name → Endian → EncodeError ⊎ List Byte → Script Outcome
  writeEncoded directory name endian (inj₁ error) = done (encodingFailed error)
  writeEncoded directory name endian (inj₂ bytes) = writeBytes directory name endian bytes

  successRequiresBound : ∀ directory name endian bytes {events} →
    Runs (writeBytes directory name endian bytes) events (returned (inj₂ tt)) →
    length bytes ≤ limit name
  successRequiresBound directory name endian bytes run with length bytes ≤? limit name
  successRequiresBound directory name endian bytes () | no oversized
  ... | yes admitted = admitted

  record Committed (directory : Path) (name : Name) (endian : Endian)
    (bytes : List Byte) (events : List Event) : Set where
    constructor committed
    field
      random : UUID
      file directoryHandle : Handle
      exactTrace : events ≡ (randomBytes16 , inj₂ random) ∷ map event
        (W.Write.successTrace (join directory (temporaryName name (fromRandom endian random)))
          (join directory (filename name)) directory bytes file directoryHandle)

  prependEntropy : ∀ directory name endian bytes random {events} →
    EmbeddedCommit (join directory (temporaryName name (fromRandom endian random)))
      (join directory (filename name)) directory bytes events →
    Committed directory name endian bytes ((randomBytes16 , inj₂ random) ∷ events)
  prependEntropy directory name endian bytes random receipt =
    committed random (EmbeddedCommit.file receipt) (EmbeddedCommit.directoryHandle receipt)
      (cong ((randomBytes16 , inj₂ random) ∷_) (EmbeddedCommit.exactTrace receipt))

  successRequiresReceipts : ∀ directory name endian bytes {events} →
    Runs (writeBytes directory name endian bytes) events (returned (inj₂ tt)) →
    Committed directory name endian bytes events
  successRequiresReceipts directory name endian bytes run with length bytes ≤? limit name
  successRequiresReceipts directory name endian bytes () | no oversized
  successRequiresReceipts directory name endian bytes (P.replied effect continuation (inj₂ random) run) | yes admitted =
    prependEntropy directory name endian bytes random
      (embeddedSuccess (join directory (temporaryName name (fromRandom endian random)))
        (join directory (filename name)) directory bytes run)

  encodingFailureNoEffects : ∀ directory name endian error {events result} →
    Runs (writeEncoded directory name endian (inj₁ error)) events result →
    events ≡ [] × result ≡ encodingFailed error
  encodingFailureNoEffects directory name endian error run = P.completedCannotProduceEffects run

  entropyFailureNoEffects : ∀ directory name endian bytes error {events result} →
    Runs (afterEntropy directory name endian bytes (inj₁ error)) events result →
    events ≡ [] × result ≡ panicked error
  entropyFailureNoEffects directory name endian bytes error run = P.completedCannotProduceEffects run

  oversizedNoEffects : ∀ directory name endian bytes → ¬ (length bytes ≤ limit name) →
    ∀ {events result} → Runs (writeBytes directory name endian bytes) events result →
    events ≡ [] × result ≡ returned (inj₁ FS.oversizedWrite)
  oversizedNoEffects directory name endian bytes oversized run with length bytes ≤? limit name
  ... | yes admitted = ⊥-elim (oversized admitted)
  ... | no rejected = P.completedCannotProduceEffects run

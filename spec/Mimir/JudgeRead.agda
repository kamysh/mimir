{-# OPTIONS --safe #-}
-- Bounded judge-state reads, including metadata guards, missing files, exact
-- decoder input, sanitized decode failure and descriptor lifetime. The decoder
-- is a supplied executable function; no decoder-correctness axiom is assumed.
module Mimir.JudgeRead where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; _≤_; _≤?_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.UnixMetadata using (Metadata; UserId; Report)
import Mimir.UnixMetadata as M
import Mimir.JudgeFilesystem as F
import Mimir.JudgeDirectory as D

module With (Path Handle NativeError Value DecodeError : Set)
  (decode : List Byte → DecodeError ⊎ Value) where
  module FS = F.With Path Handle NativeError
  module Directory = D.With Path Handle NativeError
  open FS

  record Read (limit : ℕ) : Set where
    constructor readValue
    field
      observed : Metadata
      user : UserId
      valid : Report user limit observed
      bytes : List Byte
      bounded : length bytes ≤ limit
      value : Value
      decoded : decode bytes ≡ inj₂ value

  decodedBytes : ∀ limit observed user → Report user limit observed →
    (bytes : List Byte) → length bytes ≤ limit →
    (reply : DecodeError ⊎ Value) → decode bytes ≡ reply → Result (Maybe (Read limit))
  decodedBytes limit observed user valid bytes bounded (inj₁ _) receipt = inj₁ invalidReport
  decodedBytes limit observed user valid bytes bounded (inj₂ value) receipt =
    inj₂ (just (readValue observed user valid bytes bounded value receipt))

  finishBytes : ∀ limit observed user → Report user limit observed →
    List Byte → Result (Maybe (Read limit))
  finishBytes limit observed user valid bytes with length bytes ≤? limit
  ... | no _ = inj₁ oversizedReport
  ... | yes bounded = decodedBytes limit observed user valid bytes bounded (decode bytes) refl

  finishRead : ∀ limit observed user → Report user limit observed →
    IO (List Byte) → Result (Maybe (Read limit))
  finishRead limit observed user valid (inj₁ error) = inj₁ (native error)
  finishRead limit observed user valid (inj₂ bytes) = finishBytes limit observed user valid bytes

  readBytes : ∀ handle limit observed user → Report user limit observed →
    Script (Result (Maybe (Read limit)))
  readBytes handle limit observed user valid = ask (readAtMost handle (suc limit))
    (λ response → ask (close handle)
      (λ _ → done (finishRead limit observed user valid response)))

  checkOwner : ∀ handle limit observed → UserId → Script (Result (Maybe (Read limit)))
  checkOwner handle limit observed user with M.report? user limit observed
  ... | no _ = finallyClose handle (inj₁ unsafeReport)
  ... | yes valid = readBytes handle limit observed user valid

  checkFile : ∀ handle limit → Metadata → Script (Result (Maybe (Read limit)))
  checkFile handle limit observed with M.regular? (Metadata.kind observed)
  ... | no _ = finallyClose handle (inj₁ unsafeReport)
  ... | yes _ = ask effectiveUser (checkOwner handle limit observed)

  inspectFile : ∀ handle limit → Script (Result (Maybe (Read limit)))
  inspectFile handle limit = ask (fileMetadata handle) λ where
    (inj₁ error) → finallyClose handle (inj₁ (native error))
    (inj₂ observed) → checkFile handle limit observed

  afterOpen : ∀ limit → IO Handle → Script (Result (Maybe (Read limit)))
  afterOpen limit (inj₂ handle) = inspectFile handle limit
  afterOpen limit (inj₁ error) with IOError.kind error
  ... | missing = done (inj₂ nothing)
  ... | exists = done (inj₁ (native error))
  ... | wouldBlock = done (inj₁ (native error))
  ... | other = done (inj₁ (native error))

  readNamed : Path → Path → Maybe (List Path) → (limit : ℕ) →
    Script (Result (Maybe (Read limit)))
  readNamed path filePath ancestors limit = ask (pathExists path) λ where
    false → done (inj₂ nothing)
    true → Directory.verifyParents ancestors >>= λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ _) → Directory.verifyDirectory path >>= λ where
        (inj₁ error) → done (inj₁ error)
        (inj₂ _) → ask (openFile filePath readNoFollowCloseOnExec) (afterOpen limit)

  decodedBytesSound : ∀ limit observed user valid bytes bounded reply exact accepted →
    decodedBytes limit observed user valid bytes bounded reply exact ≡ inj₂ (just accepted) →
    Read.bytes accepted ≡ bytes × Read.observed accepted ≡ observed × Read.user accepted ≡ user
  decodedBytesSound limit observed user valid bytes bounded (inj₁ error) exact accepted ()
  decodedBytesSound limit observed user valid bytes bounded (inj₂ value) exact accepted refl = refl , refl , refl

  finishBytesSound : ∀ limit observed user valid bytes accepted →
    finishBytes limit observed user valid bytes ≡ inj₂ (just accepted) →
    Read.bytes accepted ≡ bytes × Read.observed accepted ≡ observed × Read.user accepted ≡ user
  finishBytesSound limit observed user valid bytes accepted receipt with length bytes ≤? limit
  ... | no _ with receipt
  ...   | ()
  finishBytesSound limit observed user valid bytes accepted receipt | yes bounded =
    decodedBytesSound limit observed user valid bytes bounded (decode bytes) refl accepted receipt

  -- Every actual read attempt closes its descriptor before returning, including
  -- native read errors and invalid/oversized serialized data.
  readCloses : ∀ handle limit observed user valid events result →
    Runs (readBytes handle limit observed user valid) events result →
    Σ (IO (List Byte)) (λ response →
      events ≡ ((readAtMost handle (suc limit) , response) ∷ (close handle , tt) ∷ []) ×
      result ≡ finishRead limit observed user valid response)
  readCloses handle limit observed user valid events result
    (replied _ _ response (replied _ _ tt (returned _))) = response , refl , refl

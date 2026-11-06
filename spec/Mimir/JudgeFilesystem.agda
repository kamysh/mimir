{-# OPTIONS --safe #-}
-- Unix filesystem requests used by judge state. Replies are explicit inputs,
-- including failures; no request is treated as an acknowledgement. Paths and
-- descriptor identities are parameters here; native correspondence is separate.
module Mimir.JudgeFilesystem where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)
open import Mimir.Bits using (Byte)
open import Mimir.UnixMetadata using (Metadata; UserId)
import Mimir.Effects as E

module With (Path Handle NativeError : Set) where
  data ErrorKind : Set where missing exists wouldBlock other : ErrorKind

  record IOError : Set where
    constructor ioError
    field kind : ErrorKind; detail : NativeError

  IO : Set → Set
  IO A = IOError ⊎ A

  -- These constructors describe all flags rather than a configurable subset.
  data Open : Set where
    readNoFollowCloseOnExec : Open
    lockReadWriteCreate0600NoFollowCloseOnExec : Open
    exclusiveWrite0600NoFollowCloseOnExec : Open
    readDirectory : Open

  data Operation : Set where
    -- Path::exists maps every metadata error to false and follows symlinks.
    pathExists : Path → Operation
    symlinkMetadata : Path → Operation
    effectiveUser : Operation
    createDirectory0700 : Path → Operation
    openFile : Path → Open → Operation
    fileMetadata : Handle → Operation
    exclusiveNonblockingLock unlock : Handle → Operation
    readComplete : Handle → Operation
    readAtMost : Handle → ℕ → Operation
    writeAll : Handle → List Byte → Operation
    syncAll : Handle → Operation
    rename : Path → Path → Operation
    removeFile : Path → Operation
    -- File::drop ignores the close result. It does not imply a successful sync.
    close : Handle → Operation
    -- Join this already-started job; never issue its operation again. Return
    -- means the job has settled, even when its result cannot be recovered.
    awaitExisting : ℕ → Operation → Operation

  Reply : Operation → Set
  Reply (pathExists _) = Bool
  Reply (symlinkMetadata _) = IO Metadata
  Reply effectiveUser = UserId
  Reply (createDirectory0700 _) = IO ⊤
  Reply (openFile _ _) = IO Handle
  Reply (fileMetadata _) = IO Metadata
  Reply (exclusiveNonblockingLock _) = IO ⊤
  Reply (unlock _) = IO ⊤
  Reply (readComplete _) = IO (List Byte)
  Reply (readAtMost _ _) = IO (List Byte)
  Reply (writeAll _ _) = IO ⊤
  Reply (syncAll _) = IO ⊤
  Reply (rename _ _) = IO ⊤
  Reply (removeFile _) = IO ⊤
  Reply (close _) = ⊤
  Reply (awaitExisting _ operation) = IO (Reply operation)

  open E.Protocol Operation Reply public

  data Error : Set where
    noParent inspectParent parentKind parentWritable createParent : Error
    inspectDirectory directoryKind directoryOwnership createDirectory : Error
    unsafeLock unsafeReport oversizedReport invalidReport oversizedWrite : Error
    native : IOError → Error

  Result : Set → Set
  Result A = Error ⊎ A

  finallyClose : ∀ {A : Set} → Handle → A → Script A
  finallyClose handle result = ask (close handle) (λ _ → done result)

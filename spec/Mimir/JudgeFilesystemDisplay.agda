{-# OPTIONS --safe #-}
-- Exact fixed diagnostics at the judge-state filesystem boundary. Native I/O
-- error display is supplied explicitly; contextual guards deliberately hide
-- the underlying inspection/create error, matching the existing public API.
module Mimir.JudgeFilesystemDisplay where

open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.JudgeFilesystem as F

module With (Path Handle NativeError : Set) where
  module FS = F.With Path Handle NativeError
  open FS

  display : (IOError → Text) → Error → Text
  display nativeDisplay noParent = toList "state path has no parent"
  display nativeDisplay inspectParent = toList "unable to inspect state parent"
  display nativeDisplay parentKind = toList "state parent must be a real directory"
  display nativeDisplay parentWritable = toList "state parent is writable by another user"
  display nativeDisplay createParent = toList "unable to create state parent"
  display nativeDisplay inspectDirectory = toList "unable to inspect state directory"
  display nativeDisplay directoryKind = toList "state directory must be a real directory"
  display nativeDisplay directoryOwnership = toList "state directory must be owned by the user and private"
  display nativeDisplay createDirectory = toList "unable to create state directory"
  display nativeDisplay unsafeLock = toList "unsafe state lock"
  display nativeDisplay unsafeReport = toList "unsafe state report"
  display nativeDisplay oversizedReport = toList "oversized state report"
  display nativeDisplay invalidReport = toList "invalid state report"
  display nativeDisplay oversizedWrite = toList "state file is too large"
  display nativeDisplay (native error) = nativeDisplay error

  nativePreserved : ∀ nativeDisplay error → display nativeDisplay (native error) ≡ nativeDisplay error
  nativePreserved nativeDisplay error = refl

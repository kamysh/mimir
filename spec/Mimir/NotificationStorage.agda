{-# OPTIONS --safe #-}
-- Independent notification lock, three named files, 1 MiB bounds, private
-- ownership checks, and durable replacement. Parent creation races tolerate
-- AlreadyExists only because the entire chain is subsequently re-inspected.
module Mimir.NotificationStorage where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.ASCIIPath as ASCII
import Mimir.UnixPath as Path
import Mimir.UnixPathParent as Parent
import Mimir.UnixPathParts as Parts
import Mimir.JudgeFilesystem as Filesystem
import Mimir.JudgeDirectory as Directory
import Mimir.JudgeLock as Lock
import Mimir.JudgeRead as Read
import Mimir.JudgeWrite as Write
import Mimir.UUIDGroups as UUID
import Mimir.UUIDHyphenated as UUIDText

data Name : Set where outbox oauth digest : Name
filename : Name → Path.Path
filename outbox = ASCII.literal (toList "notification-outbox.json") tt
filename oauth = ASCII.literal (toList "notification-oauth.json") tt
filename digest = ASCII.literal (toList "notification-digest.json") tt

temporary : UUID.UUID → Path.Path
temporary id = ASCII.literal (toList ".notification-") tt ++ UUIDText.encode id ++
  ASCII.literal (toList ".tmp") tt

ancestors : Path.Path → List Path.Path
ancestors path with Parent.parents path
... | nothing = path ∷ []
... | just parents = path ∷ parents

module File (Handle NativeError : Set) where
  module FS = Filesystem.With Path.Path Handle NativeError
  module D = Directory.With Path.Path Handle NativeError
  module L = Lock.With Path.Path Handle NativeError
  module W = Write.With Path.Path Handle NativeError
  open FS

  created : IO ⊤ → Script (Result ⊤) → Script (Result ⊤)
  created (inj₂ _) next = next
  created (inj₁ error) next with IOError.kind error
  ... | exists = next
  ... | _ = done (inj₁ createParent)

  create : List Path.Path → Script (Result ⊤)
  create [] = done (inj₂ tt)
  create (path ∷ rest) = ask (pathExists path) λ where
    true → create rest
    false → ask (createDirectory0700 path) (λ reply → created reply (create rest))

  ensure : Path.Path → Script (Result D.CheckedDirectory)
  ensure path with Path.absolute path | Parts.noParent? path
  ... | false | _ = done (inj₁ noParent)
  ... | _ | no _ = done (inj₁ noParent)
  ... | true | yes _ = create (reverse (ancestors path)) >>= λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ _) → D.verifyList (ancestors path) >>= λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ _) → D.verifyDirectory path

  acquire : Path.Path → Script (Result (Maybe L.Locked))
  acquire path = ensure path >>= λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ _) → L.openLock path (Path.join path (ASCII.literal (toList "notification.lock") tt))

  module Decoded (Value DecodeError : Set) (decode : List Byte → DecodeError ⊎ Value) where
    module R = Read.With Path.Path Handle NativeError Value DecodeError decode
    read : L.Locked → Name → Script (Result (Maybe (R.Read (just 1048576))))
    read held name = ask (openFile (Path.join (L.Locked.path held) (filename name)) readNoFollowCloseOnExec)
      (R.afterOpen (just 1048576))

  -- Required ownership rule is shared with JudgeWrite: failure to create an
  -- exclusive temporary file grants no right to remove an existing file.
  data WriteResult : Set where
    oversized : WriteResult
    replaced : W.Outcome → WriteResult

  write : L.Locked → Name → UUID.UUID → List Byte → Script WriteResult
  write held name id bytes with length bytes ≤? 1048576
  ... | no _ = done oversized
  ... | yes _ = W.replace (Path.join directory (temporary id))
      (Path.join directory (filename name)) directory bytes >>= λ outcome → done (replaced outcome)
    where directory = L.Locked.path held

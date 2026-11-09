{-# OPTIONS --safe #-}
-- Instantiate the filesystem protocols with concrete Unix paths, names and
-- ancestor construction. Byte decoding and descriptor/native-error identities
-- remain explicit parameters, to be joined to their adapters separately.
module Mimir.JudgePersistence where

open import Data.String using (toList)
open import Data.List using (List; _++_; _∷_; [])
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_)
open import Data.Maybe using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Maybe
open import Mimir.Bits using (Byte)
open import Mimir.UnixPath using (Path; join)
import Mimir.UnixPathParent as Parent
import Mimir.ASCIIPath as ASCII
import Mimir.JudgeLock as Lock
import Mimir.JudgeRead as Read
import Mimir.StandardLibrary as Library
import Mimir.UUIDGroups as Groups

data Name : Set where status failure diagnostics : Name

filename : Name → Path
filename status = ASCII.literal (toList "judge-status.json") tt
filename failure = ASCII.literal (toList "judge-last-failure.json") tt
filename diagnostics = ASCII.literal (toList "judge-diagnostics.json") tt

lockFilename : Path
lockFilename = ASCII.literal (toList "judge.lock") tt

limit : Name → Maybe ℕ
limit name = nothing

noStateFileByteCeiling : ∀ name → limit name ≡ nothing
noStateFileByteCeiling name = refl

temporaryName : Library.Contract → Name → Groups.UUID → Path
temporaryName library name identifier = ASCII.literal (toList ".judge-") tt ++ filename name ++
  ASCII.literal (toList "-") tt ++ Library.Contract.encodeUTF8 library (Library.Contract.formatUUID library identifier) ++
  ASCII.literal (toList ".tmp") tt

module With (Handle NativeError : Set) where
  module L = Lock.With Path Handle NativeError

  acquire : (path : Path) → L.FS.Script (L.FS.Result (Data.Maybe.Maybe L.Locked))
  acquire path = L.acquire path (join path lockFilename) (Parent.parents path)

  module Decoder (Value DecodeError : Set) (decode : List Byte → DecodeError ⊎ Value) where
    module R = Read.With Path Handle NativeError Value DecodeError decode

    read : (path : Path) (name : Name) → R.FS.Script (R.FS.Result (Data.Maybe.Maybe (R.Read (limit name))))
    read path name = R.readNamed path (join path (filename name)) (Parent.parents path) (limit name)

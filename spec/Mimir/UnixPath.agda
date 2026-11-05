{-# OPTIONS --safe #-}
-- Unix Path bytes and component rules. Non-UTF-8 and NUL bytes are retained;
-- the operating-system call, not this lexical layer, rejects invalid names.
module Mimir.UnixPath where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (fromℕ; _↑ˡ_; _≟_)
open import Data.List using (List; []; _∷_; _++_; reverse; length; mapMaybe)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Mimir.Bits using (Byte)

Path = List Byte

slash dot : Byte
slash = fromℕ 47 ↑ˡ 208
dot = fromℕ 46 ↑ˡ 209

record Chunks : Set where
  constructor chunks
  field first : Path; rest : List Path

separatedTail : List Path → Path
separatedTail [] = []
separatedTail (path ∷ rest) = slash ∷ (path ++ separatedTail rest)

renderChunks : Chunks → Path
renderChunks (chunks first rest) = first ++ separatedTail rest

chunkList : Chunks → List Path
chunkList (chunks first rest) = first ∷ rest

prepend : Byte → Chunks → Chunks
prepend byte (chunks first rest) = chunks (byte ∷ first) rest

separate : Chunks → Chunks
separate groups = chunks [] (chunkList groups)

split : Path → Chunks
split [] = chunks [] []
split (byte ∷ rest) with byte ≟ slash
... | yes _ = separate (split rest)
... | no _ = prepend byte (split rest)

prependExact : ∀ byte groups → renderChunks (prepend byte groups) ≡ byte ∷ renderChunks groups
prependExact byte (chunks first rest) = refl

separateExact : ∀ groups → renderChunks (separate groups) ≡ slash ∷ renderChunks groups
separateExact (chunks first rest) = refl

splitExact : ∀ path → renderChunks (split path) ≡ path
splitExact [] = refl
splitExact (byte ∷ rest) with byte ≟ slash
... | yes refl = trans (separateExact (split rest)) (cong (slash ∷_) (splitExact rest))
... | no _ = trans (prependExact byte (split rest)) (cong (byte ∷_) (splitExact rest))

data Origin : Set where rooted current relative : Origin

prefix : Origin → Path
prefix rooted = slash ∷ []
prefix current = dot ∷ []
prefix relative = []

record Start : Set where
  constructor start
  field origin : Origin; body : Path

dotStart : Path → Start
dotStart [] = start current []
dotStart (byte ∷ rest) with byte ≟ slash
... | yes _ = start current (byte ∷ rest)
... | no _ = start relative (dot ∷ byte ∷ rest)

splitStart : Path → Start
splitStart [] = start relative []
splitStart (byte ∷ rest) with byte ≟ slash
... | yes _ = start rooted rest
... | no _ with byte ≟ dot
...   | yes _ = dotStart rest
...   | no _ = start relative (byte ∷ rest)

renderStart : Start → Path
renderStart value = prefix (Start.origin value) ++ Start.body value

dotStartExact : ∀ rest → renderStart (dotStart rest) ≡ dot ∷ rest
dotStartExact [] = refl
dotStartExact (byte ∷ rest) with byte ≟ slash
... | yes _ = refl
... | no _ = refl

startExact : ∀ path → renderStart (splitStart path) ≡ path
startExact [] = refl
startExact (byte ∷ rest) with byte ≟ slash
... | yes refl = refl
... | no _ with byte ≟ dot
...   | yes refl = dotStartExact rest
...   | no _ = refl

data Component : Set where
  rootDir curDir parentDir : Component
  normal : Path → Component

part : Path → Maybe Component
part [] = nothing
part (byte ∷ []) with byte ≟ dot
... | yes _ = nothing
... | no _ = just (normal (byte ∷ []))
part (first ∷ second ∷ []) with first ≟ dot | second ≟ dot
... | yes _ | yes _ = just parentDir
... | yes _ | no _ = just (normal (first ∷ second ∷ []))
... | no _ | _ = just (normal (first ∷ second ∷ []))
part (first ∷ second ∷ third ∷ rest) = just (normal (first ∷ second ∷ third ∷ rest))

bodyComponents : Path → List Component
bodyComponents path = mapMaybe part (chunkList (split path))

fromStart : Start → List Component
fromStart (start rooted body) = rootDir ∷ bodyComponents body
fromStart (start current body) = curDir ∷ bodyComponents body
fromStart (start relative body) = bodyComponents body

components : Path → List Component
components path = fromStart (splitStart path)

absolute : Path → Bool
absolute [] = false
absolute (byte ∷ _) with byte ≟ slash
... | yes _ = true
... | no _ = false

needsSeparator : Path → Bool
needsSeparator [] = false
needsSeparator (byte ∷ []) with byte ≟ slash
... | yes _ = false
... | no _ = true
needsSeparator (_ ∷ next ∷ rest) = needsSeparator (next ∷ rest)

joinRelative : Path → Path → Path
joinRelative base suffix with needsSeparator base
... | false = base ++ suffix
... | true = base ++ (slash ∷ suffix)

join : Path → Path → Path
join base suffix with absolute suffix
... | true = suffix
... | false = joinRelative base suffix

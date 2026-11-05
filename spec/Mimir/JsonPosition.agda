{-# OPTIONS --safe #-}
-- Byte-oriented source positions. LF advances the line and resets column;
-- other bytes each advance one column, including bytes inside UTF-8 scalars.
-- The streaming calculation agrees with the last-LF slice calculation.
module Mimir.JsonPosition where

open import Data.Fin using (#_; _≟_)
open import Data.List using (List; []; _∷_; _++_; length; take)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-suc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Mimir.Bits using (Byte)

record Position : Set where
  constructor position
  field line column : ℕ

step : Position → Byte → Position
step (position line column) byte with byte ≟ (# 10)
... | yes newline = position (suc line) 0
... | no other = position line (suc column)

scan : Position → List Byte → Position
scan before [] = before
scan before (byte ∷ rest) = scan (step before byte) rest

scanAppend : ∀ before first second → scan before (first ++ second) ≡ scan (scan before first) second
scanAppend before [] second = refl
scanAppend before (byte ∷ rest) second = scanAppend (step before byte) rest second

newlines : List Byte → ℕ
newlines [] = 0
newlines (byte ∷ rest) with byte ≟ (# 10)
... | yes newline = suc (newlines rest)
... | no other = newlines rest

-- The index immediately after the last LF; Nothing means no LF exists.
lastBreak : List Byte → Maybe ℕ
lastBreak [] = nothing
lastBreak (byte ∷ rest) with lastBreak rest
... | just offset = just (suc offset)
... | nothing with byte ≟ (# 10)
...   | yes newline = just 1
...   | no other = nothing

startFrom : Maybe ℕ → ℕ
startFrom nothing = 0
startFrom (just offset) = offset

start : List Byte → ℕ
start bytes = startFrom (lastBreak bytes)

columnFromBreak : ℕ → ℕ → Maybe ℕ → ℕ
columnFromBreak column size nothing = column + size
columnFromBreak column size (just offset) = size ∸ offset

columnFrom : ℕ → List Byte → ℕ
columnFrom column bytes = columnFromBreak column (length bytes) (lastBreak bytes)

lineLaw : ∀ before bytes → Position.line (scan before bytes) ≡ Position.line before + newlines bytes
lineLaw before [] = sym (Data.Nat.Properties.+-identityʳ (Position.line before))
lineLaw (position line column) (byte ∷ rest) with byte ≟ (# 10)
... | yes newline = trans (lineLaw (position (suc line) 0) rest) (sym (+-suc line (newlines rest)))
... | no other = lineLaw (position line (suc column)) rest

columnLaw : ∀ before bytes → Position.column (scan before bytes) ≡ columnFrom (Position.column before) bytes
columnLaw before [] = sym (Data.Nat.Properties.+-identityʳ (Position.column before))
columnLaw (position line column) (byte ∷ rest) with lastBreak rest | columnLaw (step (position line column) byte) rest
... | just offset | recursive = recursive
... | nothing | recursive with byte ≟ (# 10)
...   | yes newline = recursive
...   | no other = trans recursive (sym (+-suc column (length rest)))

noBreakCount : ∀ bytes → lastBreak bytes ≡ nothing → newlines bytes ≡ 0
noBreakCount [] observed = refl
noBreakCount (byte ∷ rest) observed with lastBreak rest in tailBreak
... | just offset with observed
...   | ()
noBreakCount (byte ∷ rest) observed | nothing with byte ≟ (# 10)
... | yes newline with observed
...   | ()
noBreakCount (byte ∷ rest) observed | nothing | no other = noBreakCount rest tailBreak

prefixCount : ∀ bytes → newlines (take (start bytes) bytes) ≡ newlines bytes
prefixCount [] = refl
prefixCount (byte ∷ rest) with lastBreak rest in tailBreak | prefixCount rest
... | just offset | recursive with byte ≟ (# 10)
...   | yes refl = cong suc recursive
...   | no other = recursive
prefixCount (byte ∷ rest) | nothing | recursive with byte ≟ (# 10)
... | yes refl = cong suc (sym (noBreakCount rest tailBreak))
... | no other = sym (noBreakCount rest tailBreak)

slicePosition : List Byte → Position
slicePosition consumed = position (suc (newlines (take (start consumed) consumed))) (length consumed ∸ start consumed)

zeroColumn : ∀ bytes → columnFrom 0 bytes ≡ length bytes ∸ start bytes
zeroColumn bytes with lastBreak bytes
... | nothing = refl
... | just offset = refl

sourceCorrespondence : ∀ consumed → scan (position 1 0) consumed ≡ slicePosition consumed
sourceCorrespondence consumed = cong₂ position
  (trans (lineLaw (position 1 0) consumed) (sym (cong suc (prefixCount consumed))))
  (trans (columnLaw (position 1 0) consumed) (zeroColumn consumed))

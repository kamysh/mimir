{-# OPTIONS --safe #-}
-- Complete byte-level reference hash with wrapping 64-bit length encoding.
-- Native overflow-checking profiles and CPU dispatch remain correspondence
-- obligations; this definition does not erase possible source panics.
module Mimir.SHA256Hash where

open import Data.List using (List; []; _∷_; _++_; length)
import Data.Fin
import Data.List.Properties as List
open import Data.Nat using (_*_; NonZero)
open import Data.Vec using (fromList; toList)
open import Data.Vec.Properties using (toList∘fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.ExactBytes using (Byte; Bytes)
import Mimir.WordEncoding as Encoding
import Mimir.WordBytes as Words
import Mimir.Bits as Bits
import Mimir.SHA256Core as Core
import Mimir.SHA256Padding as Padding
import Mimir.FixedBlocks as Fixed

module Blocks = Fixed.Blocks Byte

instance
  lengthModulusPositive : NonZero (Bits.Binary.power 64)
  lengthModulusPositive = Encoding.powerPositive 64

lengthField : Data.Nat.ℕ → Bytes 8
lengthField byteCount = Words.big 8 (Encoding.encode 64 (8 * byteCount))

paddedFrom : ∀ input → Blocks.Partition 64 input → List (Bytes 64)
paddedFrom input (Blocks.partition blocks remainder exact small) =
  blocks ++ Padding.finish (fromList remainder) small (lengthField (length input))

padded : List Byte → List (Bytes 64)
padded input = paddedFrom input (Blocks.split 63 input)

paddedLayout : ∀ input (parts : Blocks.Partition 64 input) →
  Blocks.flatten (paddedFrom input parts) ≡ input ++
    (Padding.paddingMarker ∷ Data.List.replicate (Padding.zeroCount (length (Blocks.Partition.remainder parts))) Data.Fin.zero) ++
    toList (lengthField (length input))
paddedLayout input (Blocks.partition blocks remainder exact small) =
  trans (Blocks.flattenAppend blocks (Padding.finish (fromList remainder) small (lengthField (length input))))
  (trans (cong (Blocks.flatten blocks ++_) (Padding.layout (fromList remainder) small (lengthField (length input))))
  (trans (cong (λ rest → Blocks.flatten blocks ++ (rest ++ suffix)) (toList∘fromList remainder))
  (trans (sym (List.++-assoc (Blocks.flatten blocks) remainder suffix))
    (cong (_++ suffix) (sym exact)))))
  where
  suffix = (Padding.paddingMarker ∷ Data.List.replicate (Padding.zeroCount (length remainder)) Data.Fin.zero) ++
    toList (lengthField (length input))

process processGrouped : List (Bytes 64) → Core.State → Core.State
process [] initial = initial
process (block ∷ rest) initial = process rest (Core.compress (Words.words 4 16 block) initial)
processGrouped [] initial = initial
processGrouped (block ∷ rest) initial = processGrouped rest (Core.compressGrouped (Words.words 4 16 block) initial)

processAppend : ∀ first second initial → process (first ++ second) initial ≡ process second (process first initial)
processAppend [] second initial = refl
processAppend (block ∷ rest) second initial = processAppend rest second (Core.compress (Words.words 4 16 block) initial)

processEquivalent : ∀ blocks initial → processGrouped blocks initial ≡ process blocks initial
processEquivalent [] initial = refl
processEquivalent (block ∷ rest) initial =
  trans (processEquivalent rest (Core.compressGrouped (Words.words 4 16 block) initial))
    (cong (process rest) (Core.compressionEquivalent (Words.words 4 16 block) initial))

output : Core.State → Bytes 32
output stateValue = Words.bytes 4 8 (Core.toWords stateValue)

hash groupedHash : List Byte → Bytes 32
hash input = output (process (padded input) Core.initial)
groupedHash input = output (processGrouped (padded input) Core.initial)

hashEquivalent : ∀ input → groupedHash input ≡ hash input
hashEquivalent input = cong output (processEquivalent (padded input) Core.initial)

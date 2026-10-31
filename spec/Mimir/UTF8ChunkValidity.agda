{-# OPTIONS --safe #-}
-- Each coalesced valid slice is UTF-8; each nonempty invalid slice contains
-- exactly one bad group of at most three bytes.
module Mimir.UTF8ChunkValidity where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.UTF8Text as UTF8
import Mimir.UTF8LossyBytes as B
import Mimir.UTF8LossyGroup as G
import Mimir.UTF8LossyCanonical as Canonical
import Mimir.UTF8LossyValid as Valid
import Mimir.UTF8LossyChunks as C

PieceValid : B.Piece → Set
PieceValid (B.piece true bytes) = UTF8.Decoded bytes
PieceValid (B.piece false bytes) = 1 ≤ length bytes × length bytes ≤ 3

ChunkValid : C.Chunk → Set
ChunkValid (C.chunk valid invalid) = UTF8.Decoded valid ×
  (invalid ≡ [] ⊎ (1 ≤ length invalid × length invalid ≤ 3))

groupValid : ∀ {byte input} (group : G.Group byte input) → PieceValid (B.fromGroup group)
groupValid group with G.valid group in admitted
... | false = G.positive group , G.invalidBound group admitted
... | true with Canonical.decode group admitted
...   | value , exact = Valid.oneDecoded (G.consumed group) value exact

partitionValid : ∀ {input pieces} → B.Partition input pieces → All PieceValid pieces
partitionValid B.empty = []
partitionValid (B.next byte input group later) = groupValid group ∷ partitionValid later

prependValid : ∀ bytes chunks → UTF8.Decoded bytes → All ChunkValid chunks → All ChunkValid (C.prepend bytes chunks)
prependValid bytes [] valid [] = (valid , inj₁ refl) ∷ []
prependValid bytes (C.chunk valid invalid ∷ rest) byteValues ((earlier , invalidBound) ∷ later) =
  (Valid.appendDecoded byteValues earlier , invalidBound) ∷ later

coalesceValid : ∀ pieces → All PieceValid pieces → All ChunkValid (C.coalesce pieces)
coalesceValid [] [] = []
coalesceValid (B.piece true bytes ∷ rest) (valid ∷ later) = prependValid bytes (C.coalesce rest) valid (coalesceValid rest later)
coalesceValid (B.piece false bytes ∷ rest) (bounds ∷ later) =
  (UTF8.decoded [] refl , inj₂ bounds) ∷ coalesceValid rest later

chunksValid : ∀ {input pieces} → B.Partition input pieces → All ChunkValid (C.coalesce pieces)
chunksValid {pieces = pieces} partition = coalesceValid pieces (partitionValid partition)

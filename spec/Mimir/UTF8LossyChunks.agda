{-# OPTIONS --safe #-}
-- Rust Utf8Chunks combines consecutive valid packets and then at most one
-- invalid group. Its empty invalid suffix is distinct from a replacement.
module Mimir.UTF8LossyChunks where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++-≤ˡ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≤_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.Bits using (Byte)
import Mimir.UTF8LossyBytes as B
import Mimir.UTF8LossyGroup as G

record Chunk : Set where
  constructor chunk
  field valid invalid : List Byte

prepend : List Byte → List Chunk → List Chunk
prepend bytes [] = chunk bytes [] ∷ []
prepend bytes (chunk valid invalid ∷ rest) = chunk (bytes ++ valid) invalid ∷ rest

coalesce : List B.Piece → List Chunk
coalesce [] = []
coalesce (B.piece true bytes ∷ rest) = prepend bytes (coalesce rest)
coalesce (B.piece false bytes ∷ rest) = chunk [] bytes ∷ coalesce rest

original : List Chunk → List Byte
original [] = []
original (chunk valid invalid ∷ rest) = valid ++ (invalid ++ original rest)

renderChunk : Chunk → List Byte
renderChunk (chunk valid []) = valid
renderChunk (chunk valid (byte ∷ invalid)) = valid ++ B.replacement

render : List Chunk → List Byte
render [] = []
render (part ∷ rest) = renderChunk part ++ render rest

originalPrepend : ∀ bytes chunks → original (prepend bytes chunks) ≡ bytes ++ original chunks
originalPrepend bytes [] = refl
originalPrepend bytes (chunk valid invalid ∷ rest) = ++-assoc bytes valid (invalid ++ original rest)

originalExact : ∀ pieces → original (coalesce pieces) ≡ B.original pieces
originalExact [] = refl
originalExact (B.piece true bytes ∷ rest) = trans (originalPrepend bytes (coalesce rest))
  (cong (bytes ++_) (originalExact rest))
originalExact (B.piece false bytes ∷ rest) = cong (bytes ++_) (originalExact rest)

renderPrepend : ∀ bytes chunks → render (prepend bytes chunks) ≡ bytes ++ render chunks
renderPrepend bytes [] = refl
renderPrepend bytes (chunk valid [] ∷ rest) = ++-assoc bytes valid (render rest)
renderPrepend bytes (chunk valid (byte ∷ invalid) ∷ rest) = trans
  (cong (_++ render rest) (++-assoc bytes valid B.replacement))
  (++-assoc bytes (valid ++ B.replacement) (render rest))

Nonempty : B.Piece → Set
Nonempty part = 1 ≤ length (B.Piece.bytes part)

renderExact : ∀ pieces → All Nonempty pieces → render (coalesce pieces) ≡ B.render pieces
renderExact [] [] = refl
renderExact (B.piece true bytes ∷ rest) (positive ∷ later) = trans (renderPrepend bytes (coalesce rest))
  (cong (bytes ++_) (renderExact rest later))
renderExact (B.piece false [] ∷ rest) (() ∷ later)
renderExact (B.piece false (byte ∷ bytes) ∷ rest) (positive ∷ later) =
  cong (B.replacement ++_) (renderExact rest later)

nonempty : ∀ {input pieces} → B.Partition input pieces → All Nonempty pieces
nonempty B.empty = []
nonempty (B.next byte input group later) = G.positive group ∷ nonempty later

-- Independent chunk grammar: an uninterrupted valid prefix, followed by
-- exactly one invalid group, or an all-valid nonempty final chunk.
data ValidPrefix : List B.Piece → List Byte → Set where
  emptyPrefix : ValidPrefix [] []
  validPrefix : ∀ bytes pieces valid → ValidPrefix pieces valid →
    ValidPrefix (B.piece true bytes ∷ pieces) (bytes ++ valid)

data Meaning : List B.Piece → List Chunk → Set where
  empty : Meaning [] []
  final : ∀ pieces valid → ValidPrefix pieces valid → 1 ≤ length valid →
    Meaning pieces (chunk valid [] ∷ [])
  terminated : ∀ prefix valid invalid rest chunks → ValidPrefix prefix valid →
    1 ≤ length invalid → Meaning rest chunks →
    Meaning (prefix ++ (B.piece false invalid ∷ rest)) (chunk valid invalid ∷ chunks)

prependMeaning : ∀ bytes {pieces chunks} → 1 ≤ length bytes → Meaning pieces chunks →
  Meaning (B.piece true bytes ∷ pieces) (prepend bytes chunks)
prependMeaning bytes positive empty = final (B.piece true bytes ∷ []) bytes
  (Relation.Binary.PropositionalEquality.subst (ValidPrefix (B.piece true bytes ∷ []))
    (++-identityʳ bytes) (validPrefix bytes [] [] emptyPrefix)) positive
prependMeaning bytes positive (final pieces valid prefix nonemptyValid) =
  final (B.piece true bytes ∷ pieces) (bytes ++ valid) (validPrefix bytes pieces valid prefix)
    (≤-trans positive (length-++-≤ˡ bytes))
prependMeaning bytes positive (terminated prefix valid invalid rest chunks admitted nonemptyInvalid later) =
  terminated (B.piece true bytes ∷ prefix) (bytes ++ valid) invalid rest chunks
    (validPrefix bytes prefix valid admitted) nonemptyInvalid later

meaning : ∀ pieces → All Nonempty pieces → Meaning pieces (coalesce pieces)
meaning [] [] = empty
meaning (B.piece true bytes ∷ rest) (positive ∷ later) = prependMeaning bytes positive (meaning rest later)
meaning (B.piece false bytes ∷ rest) (positive ∷ later) =
  terminated [] [] bytes rest (coalesce rest) emptyPrefix positive (meaning rest later)

partitionMeaning : ∀ {input pieces} → B.Partition input pieces → Meaning pieces (coalesce pieces)
partitionMeaning partition = meaning _ (nonempty partition)

partitionRender : ∀ {input pieces} → B.Partition input pieces → render (coalesce pieces) ≡ B.render pieces
partitionRender partition = renderExact _ (nonempty partition)

partitionOriginal : ∀ {input pieces} → B.Partition input pieces → original (coalesce pieces) ≡ input
partitionOriginal {pieces = pieces} partition = trans (originalExact pieces) (sym (B.conserves partition))

prefixInto : ∀ {prefix valid} → ValidPrefix prefix valid → ∀ invalid rest →
  coalesce (prefix ++ (B.piece false invalid ∷ rest)) ≡ chunk valid invalid ∷ coalesce rest
prefixInto emptyPrefix invalid rest = refl
prefixInto (validPrefix bytes pieces valid admitted) invalid rest =
  cong (prepend bytes) (prefixInto admitted invalid rest)

prefixFinal : ∀ {part pieces valid} → ValidPrefix (part ∷ pieces) valid →
  coalesce (part ∷ pieces) ≡ chunk valid [] ∷ []
prefixFinal (validPrefix bytes [] [] emptyPrefix) =
  cong (λ value → chunk value [] ∷ []) (sym (++-identityʳ bytes))
prefixFinal (validPrefix bytes (_ ∷ _) valid admitted@(validPrefix next pieces later tail)) =
  cong (prepend bytes) (prefixFinal admitted)

complete : ∀ {pieces chunks} → Meaning pieces chunks → coalesce pieces ≡ chunks
complete empty = refl
complete (final [] [] emptyPrefix ())
complete (final (_ ∷ _) valid admitted@(validPrefix bytes pieces rest tail) positive) = prefixFinal admitted
complete (terminated prefix valid invalid rest chunks admitted positive later) =
  trans (prefixInto admitted invalid rest) (cong (chunk valid invalid ∷_) (complete later))

unique : ∀ {pieces first second} → Meaning pieces first → Meaning pieces second → first ≡ second
unique first second = trans (sym (complete first)) (complete second)

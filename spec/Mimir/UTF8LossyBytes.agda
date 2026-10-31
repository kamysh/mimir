{-# OPTIONS --safe #-}
-- Total grouping and byte rendering for lossy UTF-8. The budget is derived
-- from input length. Scalar validity and Rust chunk coalescing are separate
-- correspondence obligations, not assumed by this partition proof.
module Mimir.UTF8LossyBytes where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; ++-assoc)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤; m≤m+n; *-distribˡ-+)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.UTF8LossyGroup as Group
import Mimir.UTF8Text as UTF8

record Piece : Set where
  constructor piece
  field valid : Bool; bytes : List Byte

fromGroup : ∀ {byte input} → Group.Group byte input → Piece
fromGroup group = piece (Group.valid group) (Group.consumed group)

data Partition : List Byte → List Piece → Set where
  empty : Partition [] []
  next : ∀ byte input (group : Group.Group byte input) {pieces} →
    Partition (Group.remaining group) pieces → Partition (byte ∷ input) (fromGroup group ∷ pieces)

suffixBound : ∀ fuel byte input (group : Group.Group byte input) →
  length (byte ∷ input) ≤ suc fuel → length (Group.remaining group) ≤ fuel
suffixBound fuel byte input group fits = UTF8.dropNonemptyPrefix
  (Group.consumed group) (Group.remaining group) fuel (Group.positive group)
  (subst (λ bytes → length bytes ≤ suc fuel) (Group.exact group) fits)

partition : ∀ fuel input → length input ≤ fuel → Σ (List Piece) (Partition input)
partition fuel [] fits = [] , empty
partition zero (byte ∷ input) ()
partition (suc fuel) (byte ∷ input) fits with Group.read byte input
... | group with partition fuel (Group.remaining group) (suffixBound fuel byte input group fits)
...   | pieces , meaning = fromGroup group ∷ pieces , next byte input group meaning

parse : ∀ input → Σ (List Piece) (Partition input)
parse input = partition (length input) input ≤-refl

original : List Piece → List Byte
original [] = []
original (piece valid bytes ∷ rest) = bytes ++ original rest

conserves : ∀ {input pieces} → Partition input pieces → input ≡ original pieces
conserves empty = refl
conserves (next byte input group meaning) = trans (Group.exact group)
  (cong (Group.consumed group ++_) (conserves meaning))

replacement : List Byte
replacement = # 239 ∷ # 191 ∷ # 189 ∷ []

renderPiece : Piece → List Byte
renderPiece (piece true bytes) = bytes
renderPiece (piece false bytes) = replacement

render : List Piece → List Byte
render [] = []
render (part ∷ rest) = renderPiece part ++ render rest

decode : List Byte → List Byte
decode input with parse input
... | pieces , meaning = render pieces

validPieceUnchanged : ∀ bytes → renderPiece (piece true bytes) ≡ bytes
validPieceUnchanged bytes = refl

invalidPieceReplaced : ∀ bytes → renderPiece (piece false bytes) ≡ replacement
invalidPieceReplaced bytes = refl

tripleBound : ∀ n → n ≤ 3 * n
tripleBound n = m≤m+n n (n + (n + 0))

groupRenderBound : ∀ {byte input} (group : Group.Group byte input) →
  length (renderPiece (fromGroup group)) ≤ 3 * length (Group.consumed group)
groupRenderBound group with Group.valid group
... | true = tripleBound (length (Group.consumed group))
... | false = Data.Nat.Properties.*-monoʳ-≤ 3 (Group.positive group)

renderBound : ∀ {input pieces} → Partition input pieces → length (render pieces) ≤ 3 * length input
renderBound empty = z≤n
renderBound (next byte input group {pieces} meaning) = subst (_≤ 3 * length (byte ∷ input))
  (sym (length-++ (renderPiece (fromGroup group)) {ys = render pieces}))
  (subst (length (renderPiece (fromGroup group)) + length (render pieces) ≤_)
    (trans (sym (*-distribˡ-+ 3 (length (Group.consumed group)) (length (Group.remaining group))))
      (cong (3 *_) (trans (sym (length-++ (Group.consumed group) {ys = Group.remaining group}))
        (cong length (sym (Group.exact group))))))
    (+-mono-≤ (groupRenderBound group) (renderBound meaning)))

decodedBound : ∀ input → length (decode input) ≤ 3 * length input
decodedBound input with parse input
... | pieces , meaning = renderBound meaning

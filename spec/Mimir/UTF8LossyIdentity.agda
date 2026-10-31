{-# OPTIONS --safe #-}
-- Partition uniqueness and canonical-packet admission establish that valid
-- UTF-8 is never replaced or normalized by the lossy decoder.
module Mimir.UTF8LossyIdentity where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Mimir.UTF8Packet as P
import Mimir.UTF8Text as UTF8
import Mimir.UTF8LossyGroup as G
import Mimir.UTF8LossyGroupComplete as Complete
import Mimir.UTF8LossyPacket as Packet
import Mimir.UTF8LossyBytes as Lossy

viewUnique : ∀ {byte input} (first second : G.Group byte input) → Complete.view first ≡ Complete.view second
viewUnique first second = trans (sym (Complete.readComplete first)) (Complete.readComplete second)

pieceUnique : ∀ {byte input} (first second : G.Group byte input) → Lossy.fromGroup first ≡ Lossy.fromGroup second
pieceUnique first second = cong₂ Lossy.piece
  (cong (λ fields → proj₂ (proj₂ fields)) (viewUnique first second)) (cong proj₁ (viewUnique first second))

remainingUnique : ∀ {byte input} (first second : G.Group byte input) → G.remaining first ≡ G.remaining second
remainingUnique first second = cong (λ fields → proj₁ (proj₂ fields)) (viewUnique first second)

partitionUnique : ∀ {input first second} → Lossy.Partition input first → Lossy.Partition input second → first ≡ second
partitionUnique Lossy.empty Lossy.empty = refl
partitionUnique (Lossy.next byte input first {firstPieces} firstTail)
  (Lossy.next .byte .input second {secondPieces} secondTail) = cong₂ _∷_ (pieceUnique first second)
    (partitionUnique firstTail (subst (λ remaining → Lossy.Partition remaining secondPieces)
      (sym (remainingUnique first second)) secondTail))

ValidPiece : Lossy.Piece → Set
ValidPiece part = Lossy.Piece.valid part ≡ true

canonicalPartition : ∀ values → Σ (List Lossy.Piece) (λ pieces → Lossy.Partition (UTF8.encode values) pieces × All ValidPiece pieces)
canonicalPartition [] = [] , Lossy.empty , []
canonicalPartition (P.scalar raw canonical ∷ values) with canonicalPartition values
... | pieces , meaning , valid = (Lossy.fromGroup group ∷ pieces) ,
  subst (λ input → Lossy.Partition input (Lossy.fromGroup group ∷ pieces)) (sym (Packet.split raw (UTF8.encode values)))
    (Lossy.next (Packet.head raw) (Packet.tail raw ++ UTF8.encode values) group
      (subst (λ remaining → Lossy.Partition remaining pieces) (sym (Packet.referenceRemaining raw canonical (UTF8.encode values))) meaning)) ,
  Packet.referenceValid raw canonical (UTF8.encode values) ∷ valid
  where
  group = Packet.reference raw canonical (UTF8.encode values)

renderOriginal : ∀ pieces → All ValidPiece pieces → Lossy.render pieces ≡ Lossy.original pieces
renderOriginal [] [] = refl
renderOriginal (Lossy.piece valid bytes ∷ rest) (admitted ∷ allValid) rewrite admitted =
  cong (bytes ++_) (renderOriginal rest allValid)

encodedUnchanged : ∀ values → Lossy.decode (UTF8.encode values) ≡ UTF8.encode values
encodedUnchanged values with Lossy.parse (UTF8.encode values) | canonicalPartition values
... | actual , observed | expected , meaning , allValid =
  trans (cong Lossy.render (partitionUnique observed meaning))
    (trans (renderOriginal expected allValid) (sym (Lossy.conserves meaning)))

validInputUnchanged : ∀ input → UTF8.Decoded input → Lossy.decode input ≡ input
validInputUnchanged .(UTF8.encode values) (UTF8.decoded values refl) = encodedUnchanged values

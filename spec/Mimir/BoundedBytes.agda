{-# OPTIONS --safe #-}
-- Byte-counted streaming independent of chunk boundaries. Header length is
-- only an early refusal; each actual chunk is checked again.
module Mimir.BoundedBytes where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; ++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _≤_; _≤?_; z≤n)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import Mimir.Framing using (Byte)

module Reader (maximum : ℕ) where
  record Buffer : Set where
    constructor buffer
    field bytes : List Byte; bounded : length bytes ≤ maximum

  empty : Buffer
  empty = buffer [] z≤n

  data Error : Set where oversized transport deadline : Error
  data State : Set where
    receiving complete : Buffer → State
    failed : Error → State

  data Input : Set where chunk : List Byte → Input; end ioFailure timeout : Input

  begin : Maybe ℕ → State
  begin nothing = receiving empty
  begin (just declared) with declared ≤? maximum
  ... | yes _ = receiving empty
  ... | no _ = failed oversized

  append : Buffer → List Byte → State
  append before next with length (Buffer.bytes before) + length next ≤? maximum
  ... | yes fits = receiving (buffer (Buffer.bytes before ++ next)
      (subst (_≤ maximum) (sym (length-++ (Buffer.bytes before))) fits))
  ... | no _ = failed oversized

  step : State → Input → State
  step (receiving before) (chunk next) = append before next
  step (receiving before) end = complete before
  step (receiving before) ioFailure = failed transport
  step (receiving before) timeout = failed deadline
  step (complete before) _ = complete before
  step (failed error) _ = failed error

  data AcceptedChunks : Buffer → List (List Byte) → Buffer → Set where
    noChunks : ∀ before → AcceptedChunks before [] before
    more : ∀ before next after rest final →
      append before next ≡ receiving after → AcceptedChunks after rest final →
      AcceptedChunks before (next ∷ rest) final

  concatenate : List (List Byte) → List Byte
  concatenate [] = []
  concatenate (part ∷ rest) = part ++ concatenate rest

  appendExact : ∀ before next after → append before next ≡ receiving after →
    Buffer.bytes after ≡ Buffer.bytes before ++ next
  appendExact before next after proof with length (Buffer.bytes before) + length next ≤? maximum
  ... | yes fits with proof
  ...   | refl = refl
  appendExact before next after () | no _

  -- Oversized content cannot be truncated into an admitted prefix.
  refusesOversize : ∀ before next →
    (length (Buffer.bytes before) + length next ≤ maximum → Data.Empty.⊥) →
    append before next ≡ failed oversized
  refusesOversize before next tooLarge with length (Buffer.bytes before) + length next ≤? maximum
  ... | no _ = refl
  ... | yes fits = ⊥-elim (tooLarge fits)

  acceptedBytesExact : ∀ before parts after → AcceptedChunks before parts after →
    Buffer.bytes after ≡ Buffer.bytes before ++ concatenate parts
  acceptedBytesExact before parts after (noChunks _) = sym (++-identityʳ (Buffer.bytes before))
  acceptedBytesExact before parts after (more _ next intermediate rest _ appended accepted) =
    trans (acceptedBytesExact intermediate rest after accepted)
      (trans (cong (_++ concatenate rest) (appendExact before next intermediate appended))
        (++-assoc (Buffer.bytes before) next (concatenate rest)))

  completeBounded : ∀ {before input after} → step before input ≡ complete after →
    length (Buffer.bytes after) ≤ maximum
  completeBounded {after = after} proof = Buffer.bounded after

  finishedStable : ∀ before input → step (complete before) input ≡ complete before
  finishedStable before input = refl

  failureStable : ∀ error input → step (failed error) input ≡ failed error
  failureStable error input = refl

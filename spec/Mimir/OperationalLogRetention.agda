{-# OPTIONS --safe #-}
-- Fixed-name log rotation. A write is serialized under one owned file lock;
-- retained slots cannot grow with error count, elapsed time, or process count.
module Mimir.OperationalLogRetention where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length; take; _++_)
open import Data.List.Properties using (length-++; length-take)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤?_; z≤n; s≤s; _⊓_)
open import Data.Nat.Properties using (+-mono-≤; m⊓n≤m)
open import Data.Vec using (Vec; []; _∷_; init)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

Byte = Fin 256

record File (limit : ℕ) : Set where
  constructor file
  field bytes : List Byte; bounded : length bytes ≤ limit

clip : ∀ limit → List Byte → File limit
clip limit bytes = file (take limit bytes)
  (subst (_≤ limit) (sym (length-take limit bytes)) (m⊓n≤m limit (length bytes)))

State : ℕ → ℕ → Set
State limit archives = Vec (File limit) (suc archives)

append : ∀ {limit archives} → List Byte → State limit archives → State limit archives
append {limit} bytes slots@(current ∷ previous) with
  (length (File.bytes current) + length (File.bytes (clip limit bytes))) ≤? limit
... | yes room = file (File.bytes current ++ File.bytes (clip limit bytes))
    (subst (_≤ limit) (sym (length-++ (File.bytes current))) room) ∷ previous
... | no full = clip limit bytes ∷ init slots

size : ∀ {limit count} → Vec (File limit) count → ℕ
size [] = 0
size (entry ∷ rest) = length (File.bytes entry) + size rest

boundedTotal : ∀ {limit count} (files : Vec (File limit) count) → size files ≤ count * limit
boundedTotal [] = z≤n
boundedTotal (x ∷ files) = +-mono-≤ (File.bounded x) (boundedTotal files)

after : ∀ {limit archives} → List (List Byte) → State limit archives → State limit archives
after [] state = state
after (entry ∷ rest) state = after rest (append entry state)

-- Arbitrarily many repeated errors, including oversized entries, retain the
-- same fixed bound. This is independent of the content and arrival sequence.
repetitionBound : ∀ {limit archives} entries (state : State limit archives) →
  size (after entries state) ≤ suc archives * limit
repetitionBound entries state = boundedTotal (after entries state)

-- OperationalLogSteps specifies the concrete rotation order and partial
-- append contents. OperationalLogProtocol requires their native receipts;
-- a size-bounded file set alone cannot supply a write outcome.

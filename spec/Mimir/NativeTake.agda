{-# OPTIONS --safe #-}
-- Rust Take's bounded read/read_buf adapter. At zero remaining budget it never
-- calls the underlying reader. Buffered reads may transfer bytes and return an
-- error together; their bytes still consume the budget. read() errors cannot
-- report transferred bytes. Native counts are admitted only within the buffer.
module Mimir.NativeTake where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊓_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; m⊓n≤m; m⊓n≤n; m+[n∸m]≡n; +-assoc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst; sym)
open import Mimir.Bits using (Byte)
import Mimir.Effects as E

module With (NativeError : Set) where
  data Mode : Set where slice cursor : Mode
  data Status : Set where ok interrupted : Status; failed : NativeError → Status

  ErrorBytes : Mode → Status → List Byte → Set
  ErrorBytes slice ok bytes = ⊤
  ErrorBytes slice interrupted bytes = bytes ≡ []
  ErrorBytes slice (failed _) bytes = bytes ≡ []
  ErrorBytes cursor status bytes = ⊤

  record Packet (mode : Mode) (capacity : ℕ) : Set where
    constructor packet
    field bytes : List Byte; fits : length bytes ≤ capacity
          status : Status; errorBytes : ErrorBytes mode status bytes

  record Operation : Set where
    constructor read
    field mode : Mode; capacity : ℕ

  Reply : Operation → Set
  Reply (read mode capacity) = Packet mode capacity

  open E.Protocol Operation Reply public

  record Response (remaining : ℕ) : Set where
    constructor response
    field bytes : List Byte; fits : length bytes ≤ remaining
          status : Status

  after : ∀ {remaining} → Response remaining → ℕ
  after {remaining} result = remaining ∸ length (Response.bytes result)

  adapt : ∀ mode remaining capacity → Packet mode (capacity ⊓ remaining) → Response remaining
  adapt mode remaining capacity (packet bytes fits status shape) =
    response bytes (≤-trans fits (m⊓n≤n capacity remaining)) status

  call : Mode → (remaining capacity : ℕ) → Script (Response remaining)
  call mode zero capacity = done (response [] z≤n ok)
  call mode (suc remaining) capacity = ask (read mode (capacity ⊓ suc remaining))
    (λ reply → done (adapt mode (suc remaining) capacity reply))

  consumedExact : ∀ {remaining} (result : Response remaining) →
    length (Response.bytes result) + after result ≡ remaining
  consumedExact result = m+[n∸m]≡n (Response.fits result)

  exhaustedDoesNotRead : ∀ mode capacity events result → Runs (call mode zero capacity) events result →
    events ≡ [] × Response.bytes result ≡ [] × Response.status result ≡ ok
  exhaustedDoesNotRead mode capacity events result (returned _) = refl , refl , refl

  requestBound : ∀ mode remaining capacity →
    Operation.capacity (read mode (capacity ⊓ remaining)) ≤ capacity ×
    Operation.capacity (read mode (capacity ⊓ remaining)) ≤ remaining
  requestBound mode remaining capacity = m⊓n≤m capacity remaining , m⊓n≤n capacity remaining

  -- Consumed bytes and remaining budget conserve the original limit, including
  -- bytes returned with an error from read_buf. No status erases consumption.
  record Accumulated (limit : ℕ) : Set where
    constructor accumulated
    field bytes : List Byte; remaining : ℕ; exact : length bytes + remaining ≡ limit

  append : ∀ {limit} (before : Accumulated limit) → Response (Accumulated.remaining before) → Accumulated limit
  append (accumulated bytes remaining exact) result =
    accumulated (bytes ++ Response.bytes result) (after result)
      (trans (cong (_+ after result) (length-++ bytes {ys = Response.bytes result}))
        (trans (+-assoc (length bytes) (length (Response.bytes result)) (after result))
          (trans (cong (length bytes +_) (consumedExact result)) exact)))

  initial : ∀ limit → Accumulated limit
  initial limit = accumulated [] limit refl

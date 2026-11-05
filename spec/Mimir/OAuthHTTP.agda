{-# OPTIONS --safe #-}
-- Refresh response protocol. Redirect/client-error responses are terminal;
-- there is no transition to a redirect destination. Decoding is requested
-- only after complete bounded bytes, then semantic token validation runs.
module Mimir.OAuthHTTP where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _≤_; _≤?_; _<_; _<?_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Framing using (Byte)
import Mimir.BoundedBytes as Bytes
open import Mimir.OAuthCache using (AuthError; retryable; needsAttention; Refresh; RefreshValid; refreshValid?)

Successful : ℕ → Set
Successful status = 200 ≤ status × status < 300

Attention : ℕ → Set
Attention status = 300 ≤ status × status < 500

successful? : ∀ status → Dec (Successful status)
successful? status = (200 ≤? status) ×-dec (status <? 300)

attention? : ∀ status → Dec (Attention status)
attention? status = (300 ≤? status) ×-dec (status <? 500)

data Category (status : ℕ) : Set where
  success : Successful status → Category status
  attention : ¬ Successful status → Attention status → Category status
  transient : ¬ Successful status → ¬ Attention status → Category status

classify : ∀ status → Category status
classify status with successful? status
... | yes proof = success proof
... | no notSuccess with attention? status
...   | yes proof = attention notSuccess proof
...   | no notAttention = transient notSuccess notAttention

module Exchange (maximum : ℕ) where
  module B = Bytes.Reader maximum

  data State : Set where
    waiting : State
    body : B.Buffer → State
    decoding : B.Buffer → State
    complete : (reply : Refresh) → RefreshValid reply → State
    failed : AuthError → State

  data Input : Set where
    headers : ℕ → Maybe ℕ → Input
    chunk : List Byte → Input
    end ioFailure timeout malformed : Input
    decoded : Refresh → Input

  data Effect : Set where decodeJSON : B.Buffer → Effect
  record Step : Set where
    constructor next
    field state : State; effects : List Effect

  fromBytes : B.State → Step
  fromBytes (B.receiving content) = next (body content) []
  fromBytes (B.complete content) = next (decoding content) (decodeJSON content ∷ [])
  fromBytes (B.failed B.oversized) = next (failed needsAttention) []
  fromBytes (B.failed B.transport) = next (failed retryable) []
  fromBytes (B.failed B.deadline) = next (failed retryable) []

  onHeaders : (status : ℕ) → Maybe ℕ → Step
  onHeaders status declared with classify status
  ... | success proof = fromBytes (B.begin declared)
  ... | attention notSuccess proof = next (failed needsAttention) []
  ... | transient notSuccess notAttention = next (failed retryable) []

  step : State → Input → Step
  step waiting (headers status declared) = onHeaders status declared
  step waiting ioFailure = next (failed retryable) []
  step waiting timeout = next (failed retryable) []
  step (body content) (chunk bytes) = fromBytes (B.step (B.receiving content) (B.chunk bytes))
  step (body content) end = fromBytes (B.step (B.receiving content) B.end)
  step (body content) ioFailure = next (failed retryable) []
  step (body content) timeout = next (failed retryable) []
  step (decoding content) malformed = next (failed needsAttention) []
  step (decoding content) (decoded reply) with refreshValid? reply
  ... | no invalid = next (failed needsAttention) []
  ... | yes valid = next (complete reply valid) []
  step state input = next state []

  decodeRequestBounded : ∀ content → length (B.Buffer.bytes content) ≤ maximum
  decodeRequestBounded = B.Buffer.bounded

  failedAbsorbs : ∀ error input → step (failed error) input ≡ next (failed error) []
  failedAbsorbs error input = refl

  completeAbsorbs : ∀ reply valid input → step (complete reply valid) input ≡ next (complete reply valid) []
  completeAbsorbs reply valid input = refl

  data RequestsDecode (content : B.Buffer) : List Effect → Set where
    requested : RequestsDecode content (decodeJSON content ∷ [])

  data WholeBody (before : State) (input : Input) (content : B.Buffer) : Set where
    ended : before ≡ body content → input ≡ end → WholeBody before input content

  decodeOnlyAfterEnd : ∀ before input content →
    RequestsDecode content (Step.effects (step before input)) → WholeBody before input content
  decodeOnlyAfterEnd waiting (headers status declared) content proof with classify status
  ... | attention _ _ with proof
  ...   | ()
  decodeOnlyAfterEnd waiting (headers status declared) content proof | transient _ _ with proof
  ... | ()
  decodeOnlyAfterEnd waiting (headers status nothing) content () | success _
  decodeOnlyAfterEnd waiting (headers status (just declared)) content proof | success _
    with declared ≤? maximum
  ... | yes _ with proof
  ...   | ()
  decodeOnlyAfterEnd waiting (headers status (just declared)) content proof | success _ | no _ with proof
  ... | ()
  decodeOnlyAfterEnd (body before) (chunk bytes) content proof
    with length (B.Buffer.bytes before) + length bytes ≤? maximum
  ... | yes _ with proof
  ...   | ()
  decodeOnlyAfterEnd (body before) (chunk bytes) content proof | no _ with proof
  ... | ()
  decodeOnlyAfterEnd (body before) end content requested = ended refl refl
  decodeOnlyAfterEnd (decoding before) (decoded reply) content proof with refreshValid? reply
  ... | yes _ with proof
  ...   | ()
  decodeOnlyAfterEnd (decoding before) (decoded reply) content proof | no _ with proof
  ... | ()

module Production = Exchange 16384

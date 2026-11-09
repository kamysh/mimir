{-# OPTIONS --safe #-}
-- Refresh response protocol. Redirect/client-error responses are terminal;
-- there is no transition to a redirect destination. Decoding is requested
-- only after the complete response, then semantic token validation runs.
module Mimir.OAuthHTTP where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _≤_; _≤?_; _<_; _<?_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Framing using (Byte)
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

module Exchange where
  data State : Set where
    waiting : State
    body decoding : List Byte → State
    complete : (reply : Refresh) → RefreshValid reply → State
    failed : AuthError → State

  data Input : Set where
    headers : ℕ → Maybe ℕ → Input
    chunk : List Byte → Input
    end ioFailure malformed : Input
    decoded : Refresh → Input

  data Effect : Set where decodeJSON : List Byte → Effect
  record Step : Set where
    constructor next
    field state : State; effects : List Effect

  onHeaders : (status : ℕ) → Maybe ℕ → Step
  onHeaders status declared with classify status
  ... | success proof = next (body []) []
  ... | attention notSuccess proof = next (failed needsAttention) []
  ... | transient notSuccess notAttention = next (failed retryable) []

  step : State → Input → Step
  step waiting (headers status declared) = onHeaders status declared
  step waiting ioFailure = next (failed retryable) []
  step (body content) (chunk bytes) = next (body (content ++ bytes)) []
  step (body content) end = next (decoding content) (decodeJSON content ∷ [])
  step (body content) ioFailure = next (failed retryable) []
  step (decoding content) malformed = next (failed needsAttention) []
  step (decoding content) (decoded reply) with refreshValid? reply
  ... | no invalid = next (failed needsAttention) []
  ... | yes valid = next (complete reply valid) []
  step state input = next state []

  failedAbsorbs : ∀ error input → step (failed error) input ≡ next (failed error) []
  failedAbsorbs error input = refl

  completeAbsorbs : ∀ reply valid input → step (complete reply valid) input ≡ next (complete reply valid) []
  completeAbsorbs reply valid input = refl

  data RequestsDecode (content : List Byte) : List Effect → Set where
    requested : RequestsDecode content (decodeJSON content ∷ [])

  data WholeBody (before : State) (input : Input) (content : List Byte) : Set where
    ended : before ≡ body content → input ≡ end → WholeBody before input content

  decodeOnlyAfterEnd : ∀ before input content →
    RequestsDecode content (Step.effects (step before input)) → WholeBody before input content
  decodeOnlyAfterEnd waiting (headers status declared) content proof with classify status
  ... | attention _ _ with proof
  ...   | ()
  decodeOnlyAfterEnd waiting (headers status declared) content proof | transient _ _ with proof
  ... | ()
  decodeOnlyAfterEnd waiting (headers status declared) content () | success _
  decodeOnlyAfterEnd (body before) (chunk bytes) content ()
  decodeOnlyAfterEnd (body before) end content requested = ended refl refl
  decodeOnlyAfterEnd (decoding before) (decoded reply) content proof with refreshValid? reply
  ... | yes _ with proof
  ...   | ()
  decodeOnlyAfterEnd (decoding before) (decoded reply) content proof | no _ with proof
  ... | ()

module Production = Exchange

{-# OPTIONS --safe #-}
-- Finite effect protocols. External replies are inputs; a request alone is
-- never a receipt. Traces retain the exact request and its matching reply.
module Mimir.Effects where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Nat using (ℕ; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (+-monoʳ-≤; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Protocol (Effect : Set) (Reply : Effect → Set) where
  data Script (Result : Set) : Set where
    done : Result → Script Result
    ask : (effect : Effect) → (Reply effect → Script Result) → Script Result

  Event : Set
  Event = Σ Effect Reply

  data Runs {Result : Set} : Script Result → List Event → Result → Set where
    returned : ∀ result → Runs (done result) [] result
    replied : ∀ effect continuation reply {events result} →
      Runs (continuation reply) events result →
      Runs (ask effect continuation) ((effect , reply) ∷ events) result

  _>>=_ : ∀ {A B} → Script A → (A → Script B) → Script B
  done value >>= next = next value
  ask effect continuation >>= next = ask effect (λ reply → continuation reply >>= next)

  bindRuns : ∀ {A B} {first : Script A} {next : A → Script B}
    {before after value result} → Runs first before value → Runs (next value) after result →
    Runs (first >>= next) (before ++ after) result
  bindRuns (returned value) second = second
  bindRuns (replied effect continuation reply rest) second =
    replied effect (λ response → continuation response >>= _) reply (bindRuns rest second)

  sameTraceSameResult : ∀ {A} {program : Script A} {events first second} →
    Runs program events first → Runs program events second → first ≡ second
  sameTraceSameResult (returned _) (returned _) = refl
  sameTraceSameResult (replied _ _ _ first) (replied _ _ _ second) =
    sameTraceSameResult first second

  completedCannotProduceEffects : ∀ {A} {value result : A} {events} →
    Runs (done value) events result → events ≡ [] × result ≡ value
  completedCannotProduceEffects (returned _) = refl , refl

  -- A process can disappear at any boundary. Prefixes retain all receipts
  -- already observed and the continuation that has not executed.
  data Prefix {Result : Set} : Script Result → List Event → Script Result → Set where
    stopped : ∀ program → Prefix program [] program
    replied : ∀ effect continuation reply {events residual} →
      Prefix (continuation reply) events residual →
      Prefix (ask effect continuation) ((effect , reply) ∷ events) residual

  module Counting (cost : Effect → ℕ) where
    count : List Event → ℕ
    count [] = 0
    count ((effect , _) ∷ rest) = cost effect + count rest

    data Bounded {A : Set} (budget : ℕ) : Script A → Set where
      done : ∀ value → Bounded budget (done value)
      ask : ∀ effect continuation remaining →
        cost effect + remaining ≤ budget →
        (∀ reply → Bounded remaining (continuation reply)) →
        Bounded budget (ask effect continuation)

    runBounded : ∀ {A budget} {program : Script A} {events result} →
      Bounded budget program → Runs program events result → count events ≤ budget
    runBounded (done _) (returned _) = z≤n
    runBounded (ask effect continuation remaining fits below) (replied _ _ reply run) =
      ≤-trans (+-monoʳ-≤ (cost effect) (runBounded (below reply) run)) fits

    prefixBounded : ∀ {A budget} {program residual : Script A} {events} →
      Bounded budget program → Prefix program events residual → count events ≤ budget
    prefixBounded bound (stopped _) = z≤n
    prefixBounded (ask effect continuation remaining fits below) (replied _ _ reply prefix) =
      ≤-trans (+-monoʳ-≤ (cost effect) (prefixBounded (below reply) prefix)) fits

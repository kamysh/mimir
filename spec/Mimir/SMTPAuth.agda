{-# OPTIONS --safe #-}
-- SMTP authorization recovery has at most one refresh retry. Rejection of a
-- newly refreshed token requires attention; it never loops through refresh.
module Mimir.SMTPAuth where

open import Data.Bool using (true; false)
open import Data.List using (List)
open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.OAuthCache using (Access; access; AuthError; retryable; needsAttention; storage)
open import Mimir.Effects

data SMTPReceipt : Set where accepted retryable authRejected : SMTPReceipt
data Result : Set where sent retryable authRequired unavailable : Result
data Effect : Set where
  acquireCachedOrRefresh acquireForcedRefresh invalidateAccess : Effect
  deliver : Access → Effect

Reply : Effect → Set
Reply acquireCachedOrRefresh = AuthError ⊎ Access
Reply acquireForcedRefresh = AuthError ⊎ Access
Reply invalidateAccess = AuthError ⊎ ⊤
Reply (deliver _) = SMTPReceipt

open Protocol Effect Reply public

mapError : AuthError → Result
mapError retryable = retryable
mapError needsAttention = authRequired
mapError storage = unavailable

afterInvalidation : Result → AuthError ⊎ ⊤ → Script Result
afterInvalidation result (inj₁ failure) = done (mapError failure)
afterInvalidation result (inj₂ tt) = done result

afterSecondDelivery : SMTPReceipt → Script Result
afterSecondDelivery accepted = done sent
afterSecondDelivery retryable = done retryable
afterSecondDelivery authRejected = ask invalidateAccess (afterInvalidation authRequired)

afterSecondToken : AuthError ⊎ Access → Script Result
afterSecondToken (inj₁ failure) = done (mapError failure)
afterSecondToken (inj₂ token) = ask (deliver token) afterSecondDelivery

afterFirstInvalidation : Access → AuthError ⊎ ⊤ → Script Result
afterFirstInvalidation first (inj₁ failure) = done (mapError failure)
afterFirstInvalidation (access value false) (inj₂ tt) = done authRequired
afterFirstInvalidation (access value true) (inj₂ tt) = ask acquireForcedRefresh afterSecondToken

afterFirstDelivery : Access → SMTPReceipt → Script Result
afterFirstDelivery first accepted = done sent
afterFirstDelivery first retryable = done retryable
afterFirstDelivery first authRejected = ask invalidateAccess (afterFirstInvalidation first)

afterFirstToken : AuthError ⊎ Access → Script Result
afterFirstToken (inj₁ failure) = done (mapError failure)
afterFirstToken (inj₂ token) = ask (deliver token) (afterFirstDelivery token)

sendOAuth : Script Result
sendOAuth = ask acquireCachedOrRefresh afterFirstToken

-- Password/anonymous SMTP follows the existing generic retry classification.
withoutOAuth : SMTPReceipt → Result
withoutOAuth accepted = sent
withoutOAuth retryable = retryable
withoutOAuth authRejected = retryable

cost : Effect → ℕ
cost (deliver _) = 1
cost _ = 0

open Counting cost

invalidationBound : ∀ budget result reply → Bounded budget (afterInvalidation result reply)
invalidationBound budget result (inj₁ failure) = done _
invalidationBound budget result (inj₂ tt) = done _

secondDeliveryBound : ∀ reply → Bounded 0 (afterSecondDelivery reply)
secondDeliveryBound accepted = done _
secondDeliveryBound retryable = done _
secondDeliveryBound authRejected = ask invalidateAccess _ 0 ≤-refl (invalidationBound 0 authRequired)

secondTokenBound : ∀ reply → Bounded 1 (afterSecondToken reply)
secondTokenBound (inj₁ failure) = done _
secondTokenBound (inj₂ token) = ask (deliver token) _ 0 ≤-refl secondDeliveryBound

firstInvalidationBound : ∀ first reply → Bounded 1 (afterFirstInvalidation first reply)
firstInvalidationBound first (inj₁ failure) = done _
firstInvalidationBound (access value false) (inj₂ tt) = done _
firstInvalidationBound (access value true) (inj₂ tt) = ask acquireForcedRefresh _ 1 ≤-refl secondTokenBound

firstDeliveryBound : ∀ first reply → Bounded 1 (afterFirstDelivery first reply)
firstDeliveryBound first accepted = done _
firstDeliveryBound first retryable = done _
firstDeliveryBound first authRejected = ask invalidateAccess _ 1 ≤-refl (firstInvalidationBound first)

firstTokenBound : ∀ reply → Bounded 2 (afterFirstToken reply)
firstTokenBound (inj₁ failure) = done _
firstTokenBound (inj₂ token) = ask (deliver token) _ 1 ≤-refl (firstDeliveryBound token)

twoAttempts : Bounded 2 sendOAuth
twoAttempts = ask acquireCachedOrRefresh _ 2 ≤-refl firstTokenBound

everyRunAtMostTwoSMTPAttempts : ∀ events result → Runs sendOAuth events result → count events ≤ 2
everyRunAtMostTwoSMTPAttempts events result = runBounded twoAttempts

everyInterruptedRunAtMostTwoSMTPAttempts : ∀ events residual → Prefix sendOAuth events residual → count events ≤ 2
everyInterruptedRunAtMostTwoSMTPAttempts events residual = prefixBounded twoAttempts

freshRejectionDoesNotRefreshAgain : ∀ value →
  afterFirstInvalidation (access value false) (inj₂ tt) ≡ done authRequired
freshRejectionDoesNotRefreshAgain value = refl

invalidationFailureDoesNotRefresh : ∀ first failure →
  afterFirstInvalidation first (inj₁ failure) ≡ done (mapError failure)
invalidationFailureDoesNotRefresh first failure = refl

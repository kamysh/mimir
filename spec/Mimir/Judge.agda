{-# OPTIONS --safe #-}
-- Pure runner/notification contracts. A confirmed receipt is an observation
-- from the database adapter, never an LLM's assertion. SQL/process/SMTP I/O
-- must implement the assumptions recorded in the correspondence document.
module Mimir.Judge where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)

module Completion where
  data Receipt : Set where confirmed pending corrected unavailable : Receipt
  data Status : Set where idle running partial complete blocked : Status

  begin : List Receipt → Status
  begin [] = idle
  begin (_ ∷ _) = running

  nonempty-batch-starts-running : ∀ r rs → begin (r ∷ rs) ≡ running
  nonempty-batch-starts-running r rs = refl

  Confirmed : Receipt → Set
  Confirmed confirmed = ⊤
  Confirmed _ = ⊥

  isConfirmed : Receipt → Bool
  isConfirmed confirmed = true
  isConfirmed _ = false

  allConfirmed : List Receipt → Bool
  allConfirmed [] = true
  allConfirmed (r ∷ rs) = isConfirmed r ∧ allConfirmed rs

  anyConfirmed : List Receipt → Bool
  anyConfirmed [] = false
  anyConfirmed (r ∷ rs) = isConfirmed r ∨ anyConfirmed rs

  finish : List Receipt → Bool → Status
  finish [] false = idle
  finish [] true = blocked
  finish (r ∷ rs) true with anyConfirmed (r ∷ rs)
  ... | true = partial
  ... | false = blocked
  finish (r ∷ rs) false with allConfirmed (r ∷ rs)
  ... | true = complete
  ... | false with anyConfirmed (r ∷ rs)
  ...   | true = partial
  ...   | false = blocked

  all-confirmed-sound : ∀ rs → allConfirmed rs ≡ true → All Confirmed rs
  all-confirmed-sound [] eq = []
  all-confirmed-sound (confirmed ∷ rs) eq = tt ∷ all-confirmed-sound rs eq
  all-confirmed-sound (pending ∷ rs) ()
  all-confirmed-sound (corrected ∷ rs) ()
  all-confirmed-sound (unavailable ∷ rs) ()

  complete-requires-database-receipts : ∀ rs failed →
    finish rs failed ≡ complete → All Confirmed rs
  complete-requires-database-receipts [] false ()
  complete-requires-database-receipts [] true ()
  complete-requires-database-receipts (r ∷ rs) true proof with anyConfirmed (r ∷ rs)
  ... | true = impossible proof
    where
    impossible : partial ≡ complete → All Confirmed (r ∷ rs)
    impossible ()
  ... | false = impossible proof
    where
    impossible : blocked ≡ complete → All Confirmed (r ∷ rs)
    impossible ()
  complete-requires-database-receipts (r ∷ rs) false proof
    with allConfirmed (r ∷ rs) in eq
  ... | true = all-confirmed-sound (r ∷ rs) eq
  ... | false with anyConfirmed (r ∷ rs)
  ...   | true = impossible proof
    where
    impossible : partial ≡ complete → All Confirmed (r ∷ rs)
    impossible ()
  ...   | false = impossible proof
    where
    impossible : blocked ≡ complete → All Confirmed (r ∷ rs)
    impossible ()

  -- A model's completion claim cannot affect the final verdict.
  finishWithClaim : Bool → List Receipt → Bool → Status
  finishWithClaim claim rs failed = finish rs failed
  model-claim-does-not-acknowledge : ∀ claim₁ claim₂ rs failed →
    finishWithClaim claim₁ rs failed ≡ finishWithClaim claim₂ rs failed
  model-claim-does-not-acknowledge claim₁ claim₂ rs failed = refl

module Budget where
  data Action : Set where modelCall toolCall : Action
  record Remaining : Set where
    constructor remaining
    field models tools : ℕ

  spend : Action → Remaining → Maybe Remaining
  spend modelCall (remaining zero tools) = nothing
  spend modelCall (remaining (suc models) tools) = just (remaining models tools)
  spend toolCall (remaining models zero) = nothing
  spend toolCall (remaining models (suc tools)) = just (remaining models tools)

  no-model-call-without-fuel : ∀ tools → spend modelCall (remaining zero tools) ≡ nothing
  no-model-call-without-fuel tools = refl
  no-tool-call-without-fuel : ∀ models → spend toolCall (remaining models zero) ≡ nothing
  no-tool-call-without-fuel models = refl

  -- Each admitted operation spends exactly one of the two independent bounds.
  model-spends-one : ∀ models tools → spend modelCall (remaining (suc models) tools)
    ≡ just (remaining models tools)
  model-spends-one models tools = refl
  tool-spends-one : ∀ models tools → spend toolCall (remaining models (suc tools))
    ≡ just (remaining models tools)
  tool-spends-one models tools = refl

  permitted : Bool → Action → Remaining → Maybe Remaining
  permitted false action fuel = nothing
  permitted true action fuel = spend action fuel
  refused-tool-cannot-spend : ∀ fuel → permitted false toolCall fuel ≡ nothing
  refused-tool-cannot-spend fuel = refl

  -- Admitted traces count every attempted model/tool operation, including
  -- failures. Retries are additional operations, not free recursive steps.
  data Trace : Remaining → List Action → Remaining → Set where
    done : ∀ {fuel} → Trace fuel [] fuel
    model : ∀ {m t actions final} → Trace (remaining m t) actions final →
      Trace (remaining (suc m) t) (modelCall ∷ actions) final
    tool : ∀ {m t actions final} → Trace (remaining m t) actions final →
      Trace (remaining m (suc t)) (toolCall ∷ actions) final

  total : Remaining → ℕ
  total (remaining m t) = m + t

  trace-conserves-budget : ∀ {initial actions final} → Trace initial actions final →
    length actions + total final ≡ total initial
  trace-conserves-budget done = refl
  trace-conserves-budget (model trace) = cong suc (trace-conserves-budget trace)
  trace-conserves-budget (tool {m} {t} trace) =
    trans (cong suc (trace-conserves-budget trace)) (sym (+-suc m t))

module Notification where
  data Mail : Set where disabled notNeeded sent exhausted : Mail
                        retryPending : ℕ → Mail
  attempt : ℕ → Bool → Mail
  attempt zero success = exhausted
  attempt (suc fuel) true = sent
  attempt (suc zero) false = exhausted
  attempt (suc (suc fuel)) false = retryPending (suc fuel)

  retry-exhaustion : ∀ success → attempt zero success ≡ exhausted
  retry-exhaustion success = refl
  failed-attempt-never-sent : ∀ fuel → attempt fuel false ≢ sent
  failed-attempt-never-sent zero ()
  failed-attempt-never-sent (suc zero) ()
  failed-attempt-never-sent (suc (suc fuel)) ()
  failure-spends-one : ∀ fuel → attempt (suc (suc fuel)) false ≡ retryPending (suc fuel)
  failure-spends-one fuel = refl

  -- The quantified review state may be any committed review/graph snapshot.
  notify : {ReviewState : Set} → ℕ → Bool → ReviewState × Mail → ReviewState × Mail
  notify fuel accepted (review , previous) = review , attempt fuel accepted
  mail-cannot-undo-review : ∀ {ReviewState : Set} fuel accepted (s : ReviewState × Mail) →
    proj₁ (notify fuel accepted s) ≡ proj₁ s
  mail-cannot-undo-review fuel accepted (review , previous) = refl

  module OAuth where
    -- Tokens and account identities are opaque here. The adapter must perform
    -- exact identity comparison and durable writes before reporting readiness.
    record Cache : Set where
      constructor cache
      field owner refresh : ℕ
            access : Maybe ℕ

    data Refresh : Set where
      unchanged : ℕ → Refresh
      rotated : ℕ → ℕ → Refresh
      denied malformed : Refresh

    data Decision : Set where
      ready authRequired storageFailure : Decision

    -- The first guard means the configured account/client still owns the cache;
    -- the second means the new cache state has been durably stored.
    step : Bool → Refresh → Bool → Cache → Cache × Decision
    step false reply durable old = old , authRequired
    step true denied durable old = old , authRequired
    step true malformed durable old = old , authRequired
    step true (unchanged token) false old = old , storageFailure
    step true (unchanged token) true (cache owner refresh access) =
      cache owner refresh (just token) , ready
    step true (rotated newRefresh token) false old = old , storageFailure
    step true (rotated newRefresh token) true (cache owner refresh access) =
      cache owner newRefresh (just token) , ready

    account-change-refuses : ∀ reply durable old →
      step false reply durable old ≡ (old , authRequired)
    account-change-refuses reply durable old = refl

    no-send-before-durable-write : ∀ reply old →
      proj₂ (step true reply false old) ≢ ready
    no-send-before-durable-write (unchanged token) old ()
    no-send-before-durable-write (rotated refresh token) old ()
    no-send-before-durable-write denied old ()
    no-send-before-durable-write malformed old ()

    rotated-refresh-is-stored : ∀ owner oldRefresh oldAccess newRefresh token →
      proj₁ (step true (rotated newRefresh token) true
        (cache owner oldRefresh oldAccess))
        ≡ cache owner newRefresh (just token)
    rotated-refresh-is-stored owner oldRefresh oldAccess newRefresh token = refl

    rejectAccess : Cache → Cache
    rejectAccess (cache owner refresh access) = cache owner refresh nothing

    rejected-access-keeps-refresh : ∀ owner refresh access →
      rejectAccess (cache owner refresh access) ≡ cache owner refresh nothing
    rejected-access-keeps-refresh owner refresh access = refl

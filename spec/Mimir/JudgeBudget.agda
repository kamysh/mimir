{-# OPTIONS --safe #-}
-- The shared batch budget counts provider requests and model tool attempts
-- separately. Queued calls do not spend another provider request. Invalid tool
-- arguments still spend an attempt; host-only receipt reads are not attempts.
module Mimir.JudgeBudget where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (+-assoc; m≤m+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

record Budget : Set where
  constructor budget
  field models tools : ℕ

data Charge : Set where provider tool : Charge

consume : Budget → Charge → Maybe Budget
consume b provider with Budget.models b
... | zero = nothing
... | suc models = just (budget models (Budget.tools b))
consume b tool with Budget.tools b
... | zero = nothing
... | suc tools = just (budget (Budget.models b) tools)

modelCost toolCost : Charge → ℕ
modelCost provider = 1
modelCost tool = 0
toolCost provider = 0
toolCost tool = 1

modelsConsumed : ∀ before charge after → consume before charge ≡ just after →
  modelCost charge + Budget.models after ≡ Budget.models before
modelsConsumed (budget zero tools) provider after ()
modelsConsumed (budget (suc models) tools) provider .(budget models tools) refl = refl
modelsConsumed (budget models zero) tool after ()
modelsConsumed (budget models (suc tools)) tool .(budget models tools) refl = refl

toolsConsumed : ∀ before charge after → consume before charge ≡ just after →
  toolCost charge + Budget.tools after ≡ Budget.tools before
toolsConsumed (budget zero tools) provider after ()
toolsConsumed (budget (suc models) tools) provider .(budget models tools) refl = refl
toolsConsumed (budget models zero) tool after ()
toolsConsumed (budget models (suc tools)) tool .(budget models tools) refl = refl

data Trace : Budget → List Charge → Budget → Set where
  empty : ∀ {b} → Trace b [] b
  spent : ∀ {before after final charge rest} → consume before charge ≡ just after →
    Trace after rest final → Trace before (charge ∷ rest) final

count : (Charge → ℕ) → List Charge → ℕ
count cost [] = zero
count cost (charge ∷ rest) = cost charge + count cost rest

conservation : (remaining : Budget → ℕ) (cost : Charge → ℕ) →
  (∀ before charge after → consume before charge ≡ just after →
    cost charge + remaining after ≡ remaining before) →
  ∀ {before charges after} → Trace before charges after →
    count cost charges + remaining after ≡ remaining before
conservation remaining cost one empty = refl
conservation remaining cost one (spent {before} {middle} {after} {charge} {rest} permission steps) =
  trans (+-assoc (cost charge) (count cost rest) (remaining after))
    (trans (cong (cost charge +_) (conservation remaining cost one steps))
      (one before charge middle permission))

modelConservation : ∀ {before charges after} → Trace before charges after →
  count modelCost charges + Budget.models after ≡ Budget.models before
modelConservation = conservation Budget.models modelCost modelsConsumed

toolConservation : ∀ {before charges after} → Trace before charges after →
  count toolCost charges + Budget.tools after ≡ Budget.tools before
toolConservation = conservation Budget.tools toolCost toolsConsumed

modelRequestsBounded : ∀ {before charges after} → Trace before charges after →
  count modelCost charges ≤ Budget.models before
modelRequestsBounded {before} {charges} {after} steps =
  subst (count modelCost charges ≤_) (modelConservation steps)
    (m≤m+n (count modelCost charges) (Budget.models after))

toolAttemptsBounded : ∀ {before charges after} → Trace before charges after →
  count toolCost charges ≤ Budget.tools before
toolAttemptsBounded {before} {charges} {after} steps =
  subst (count toolCost charges ≤_) (toolConservation steps)
    (m≤m+n (count toolCost charges) (Budget.tools after))

join : ∀ {first middle final left right} → Trace first left middle → Trace middle right final →
  Trace first (left Data.List.++ right) final
join empty right = right
join (spent permission left) right = spent permission (join left right)

-- Budgets remain shared across selected experiences: concatenating two traces
-- retains conservation rather than resetting either remaining counter.
combinedModelBound : ∀ {first middle final left right} → Trace first left middle →
  Trace middle right final → count modelCost (left Data.List.++ right) ≤ Budget.models first
combinedModelBound left right = modelRequestsBounded (join left right)

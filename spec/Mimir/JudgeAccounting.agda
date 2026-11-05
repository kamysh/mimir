{-# OPTIONS --safe #-}
-- Cumulative work accounting. Recording work never refuses a request.
module Mimir.JudgeAccounting where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

record Counts : Set where
  constructor counts
  field models tools : ℕ

data Charge : Set where provider tool : Charge

recordCharge : Counts → Charge → Counts
recordCharge (counts models tools) provider = counts (suc models) tools
recordCharge (counts models tools) tool = counts models (suc tools)

modelCost toolCost : Charge → ℕ
modelCost provider = 1
modelCost tool = 0
toolCost provider = 0
toolCost tool = 1

modelRecorded : ∀ before charge →
  Counts.models (recordCharge before charge) ≡ modelCost charge + Counts.models before
modelRecorded (counts models tools) provider = refl
modelRecorded (counts models tools) tool = refl

toolRecorded : ∀ before charge →
  Counts.tools (recordCharge before charge) ≡ toolCost charge + Counts.tools before
toolRecorded (counts models tools) provider = refl
toolRecorded (counts models tools) tool = refl

data Trace : Counts → List Charge → Counts → Set where
  empty : ∀ {b} → Trace b [] b
  recorded : ∀ {before after final charge rest} → recordCharge before charge ≡ after →
    Trace after rest final → Trace before (charge ∷ rest) final

count : (Charge → ℕ) → List Charge → ℕ
count cost [] = zero
count cost (charge ∷ rest) = cost charge + count cost rest

join : ∀ {first middle final left right} → Trace first left middle → Trace middle right final →
  Trace first (left ++ right) final
join empty right = right
join (recorded receipt left) right = recorded receipt (join left right)

-- The exact total, rather than an upper allowance, is carried across revisions.
-- A proof is supplied below for every finite trace, of any length.
modelTotal : ∀ {before charges after} → Trace before charges after →
  Counts.models after ≡ count modelCost charges + Counts.models before
modelTotal empty = refl
modelTotal (recorded {before = counts models tools} {charge = provider} {rest = rest} refl steps) =
  trans (modelTotal steps) (+-suc (count modelCost rest) models)
modelTotal (recorded {before = counts models tools} {charge = tool} refl steps) = modelTotal steps

toolTotal : ∀ {before charges after} → Trace before charges after →
  Counts.tools after ≡ count toolCost charges + Counts.tools before
toolTotal empty = refl
toolTotal (recorded {before = counts models tools} {charge = provider} refl steps) = toolTotal steps
toolTotal (recorded {before = counts models tools} {charge = tool} {rest = rest} refl steps) =
  trans (toolTotal steps) (+-suc (count toolCost rest) tools)

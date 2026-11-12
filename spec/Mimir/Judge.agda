{-# OPTIONS --safe #-}
-- Pure runner/notification contracts. A confirmed receipt is an observation
-- from the database adapter, never an LLM's assertion. SQL/process/SMTP I/O
-- must implement the assumptions recorded in the correspondence document.
module Mimir.Judge where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc; ≤-refl)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)

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

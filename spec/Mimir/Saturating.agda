{-# OPTIONS --safe #-}
-- Deadline arithmetic shared by notification retry and OAuth expiry.
module Mimir.Saturating where

open import Data.Nat using (ℕ; _+_; _≤_; _⊓_)
open import Data.Nat.Properties using (m⊓n≤n; m≤m+n; ⊓-glb; m≤n⇒m⊓n≡m;
  m≥n⇒m⊓n≡n; ⊓-mono-≤; +-mono-≤; ≤-refl)
open import Relation.Binary.PropositionalEquality using (_≡_)

add : ℕ → ℕ → ℕ → ℕ
add maximum first second = (first + second) ⊓ maximum

bounded : ∀ maximum first second → add maximum first second ≤ maximum
bounded maximum first second = m⊓n≤n (first + second) maximum

doesNotWrap : ∀ maximum first second → first ≤ maximum → first ≤ add maximum first second
doesNotWrap maximum first second bound = ⊓-glb (m≤m+n first second) bound

exactWhenFits : ∀ maximum first second → first + second ≤ maximum → add maximum first second ≡ first + second
exactWhenFits maximum first second = m≤n⇒m⊓n≡m

saturatesWhenFull : ∀ maximum first second → maximum ≤ first + second → add maximum first second ≡ maximum
saturatesWhenFull maximum first second = m≥n⇒m⊓n≡n

monotone : ∀ maximum {a b c d} → a ≤ b → c ≤ d → add maximum a c ≤ add maximum b d
monotone maximum first second = ⊓-mono-≤ (+-mono-≤ first second) ≤-refl

u64Maximum : ℕ
u64Maximum = 18446744073709551615

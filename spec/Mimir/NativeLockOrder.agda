{-# OPTIONS --safe #-}
-- Order actual transaction-held intervals using the trusted exclusive-lock
-- guarantee. No PostgreSQL implementation, scheduler or fairness is proved.
module Mimir.NativeLockOrder where

open import Data.Nat using (ℕ; _≤_; _<_; _≤?_)
open import Data.Nat.Properties using (≤-total; ≤-refl; ≰⇒>)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_)
import Mimir.DatabaseAdvisoryLock as Lock

module Over (locks : Lock.Contract) (snapshotAt : ℕ → Lock.Contract.Snapshot locks)
  (database : Lock.Contract.Database locks) (key : Lock.Contract.Key locks) where
  module L = Lock.Contract locks

  -- Positions refer to one native history shared by both operations. These
  -- are actual database lease intervals, including an end caused by failure;
  -- they are not intervals guessed from when the client sees a reply.
  record Span (transaction : L.Transaction) : Set where
    field
      acquired ended : ℕ
      nonempty : acquired < ended
      ownsThroughout : ∀ point → acquired ≤ point → point < ended → L.Held (snapshotAt point) database key transaction

  order : ∀ first second → first ≢ second → (a : Span first) → (b : Span second) →
    Span.ended a ≤ Span.acquired b ⊎ Span.ended b ≤ Span.acquired a
  order first second different a b with ≤-total (Span.acquired a) (Span.acquired b)
  ... | inj₁ firstStarts with Span.ended a ≤? Span.acquired b
  ...   | yes firstEnded = inj₁ firstEnded
  ...   | no overlapping = ⊥-elim (different (L.exclusive (snapshotAt (Span.acquired b)) database key first second
    (Span.ownsThroughout a (Span.acquired b) firstStarts (≰⇒> overlapping))
    (Span.ownsThroughout b (Span.acquired b) ≤-refl (Span.nonempty b))))
  order first second different a b | inj₂ secondStarts with Span.ended b ≤? Span.acquired a
  ... | yes secondEnded = inj₂ secondEnded
  ... | no overlapping = ⊥-elim (different (L.exclusive (snapshotAt (Span.acquired a)) database key first second
    (Span.ownsThroughout a (Span.acquired a) ≤-refl (Span.nonempty a))
    (Span.ownsThroughout b (Span.acquired a) secondStarts (≰⇒> overlapping))))

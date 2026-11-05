{-# OPTIONS --safe #-}
-- Byte windows used by private judge failure excerpts. Bounds are on input
-- bytes; lossy text conversion may expand their encoded length.
module Mimir.SourceWindow where

open import Data.List using (List; take; drop; length; _++_)
open import Data.List.Properties using (length-take; length-drop; take++drop≡id; ++-assoc)
open import Data.Nat using (ℕ; _+_; _∸_; _⊓_; _≤_)
open import Data.Nat.Properties using (⊓-assoc; m≥n⇒m⊓n≡n; m⊓n≤m; m⊓n≤n;
  +-distribˡ-⊓; m+[n∸m]≡n; ≤-trans; m∸n≤m)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Bits using (Byte)

clip : ℕ → ℕ → ℕ
clip total value = value ⊓ total

saturatingClip : ∀ maximum total value → total ≤ maximum →
  clip total (value ⊓ maximum) ≡ clip total value
saturatingClip maximum total value bounded = trans (⊓-assoc value maximum total)
  (cong (value ⊓_) (m≥n⇒m⊓n≡n bounded))

bytes : ℕ → ℕ → List Byte → List Byte
bytes start width source = take width (drop start source)

end : ℕ → ℕ → ℕ → ℕ
end start width total = (start + width) ⊓ total

lengthExact : ∀ start width source →
  length (bytes start width source) ≡ width ⊓ (length source ∸ start)
lengthExact start width source = trans (length-take width (drop start source))
  (cong (width ⊓_) (length-drop start source))

bounded : ∀ start width source → length (bytes start width source) ≤ width
bounded start width source = subst (_≤ width) (sym (lengthExact start width source))
  (m⊓n≤m width (length source ∸ start))

endExact : ∀ start width source → start ≤ length source →
  start + length (bytes start width source) ≡ end start width (length source)
endExact start width source inside = trans (cong (start +_) (lengthExact start width source))
  (trans (+-distribˡ-⊓ start width (length source ∸ start))
    (cong ((start + width) ⊓_) (m+[n∸m]≡n inside)))

endBound : ∀ start width total → end start width total ≤ total
endBound start width total = m⊓n≤n (start + width) total

-- No byte is invented, skipped inside the window, or reordered.
reconstruct : ∀ start width source →
  take start source ++ (bytes start width source ++ drop width (drop start source)) ≡ source
reconstruct start width source = trans
  (cong (take start source ++_) (take++drop≡id width (drop start source)))
  (take++drop≡id start source)

start : ℕ → ℕ → ℕ → ℕ
start half total offset = clip total offset ∸ half

startBound : ∀ half total offset → start half total offset ≤ total
startBound half total offset = ≤-trans (m∸n≤m (clip total offset) half) (m⊓n≤n offset total)

nativeEnd : ∀ maximum start width total → total ≤ maximum →
  ((start + width) ⊓ maximum) ⊓ total ≡ end start width total
nativeEnd maximum start width total bounded = saturatingClip maximum total (start + width) bounded

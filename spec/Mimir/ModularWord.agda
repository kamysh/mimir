{-# OPTIONS --safe #-}
-- Unsigned wrapping arithmetic, proved symbolically before word-size
-- instantiation. This avoids expanding concrete 32/64-bit bounds in proofs.
module Mimir.ModularWord where

open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n; toℕ-injective)
open import Data.Nat using (ℕ; suc; _+_; _*_; _%_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityˡ; *-comm)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m; %-distribˡ-+; %-distribˡ-*)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

module Modulus (maximum : ℕ) where
  modulus = suc maximum
  Word = Fin modulus

  abstract
    wrap : ℕ → Word
    wrap number = fromℕ< (m%n<n number modulus)

    wrapValue : ∀ number → toℕ (wrap number) ≡ number % modulus
    wrapValue number = toℕ-fromℕ< (m%n<n number modulus)

    wrapWord : ∀ word → wrap (toℕ word) ≡ word
    wrapWord word = toℕ-injective (trans (wrapValue (toℕ word)) (m<n⇒m%n≡m (toℕ<n word)))

  add multiply : Word → Word → Word
  add first second = wrap (toℕ first + toℕ second)
  multiply first second = wrap (toℕ first * toℕ second)

  abstract
    addValue : ∀ first second → toℕ (add first second) ≡ (toℕ first + toℕ second) % modulus
    addValue first second = wrapValue (toℕ first + toℕ second)

    multiplyValue : ∀ first second → toℕ (multiply first second) ≡ (toℕ first * toℕ second) % modulus
    multiplyValue first second = wrapValue (toℕ first * toℕ second)

    addWrapped : ∀ first second → add (wrap first) (wrap second) ≡ wrap (first + second)
    addWrapped first second = toℕ-injective (trans (addValue (wrap first) (wrap second))
      (trans (cong₂ (λ a b → (a + b) % modulus) (wrapValue first) (wrapValue second))
        (trans (sym (%-distribˡ-+ first second modulus)) (sym (wrapValue (first + second))))))

    multiplyWrapped : ∀ first second → multiply (wrap first) (wrap second) ≡ wrap (first * second)
    multiplyWrapped first second = toℕ-injective (trans (multiplyValue (wrap first) (wrap second))
      (trans (cong₂ (λ a b → (a * b) % modulus) (wrapValue first) (wrapValue second))
        (trans (sym (%-distribˡ-* first second modulus)) (sym (wrapValue (first * second))))))

    addAssociative : ∀ first second third → add (add first second) third ≡ add first (add second third)
    addAssociative first second third =
      trans (cong (add (add first second)) (sym (wrapWord third)))
      (trans (addWrapped (toℕ first + toℕ second) (toℕ third))
      (trans (cong wrap (+-assoc (toℕ first) (toℕ second) (toℕ third)))
      (trans (sym (addWrapped (toℕ first) (toℕ second + toℕ third)))
        (cong (λ word → add word (add second third)) (wrapWord first)))))

    addCommutative : ∀ first second → add first second ≡ add second first
    addCommutative first second = cong wrap (+-comm (toℕ first) (toℕ second))

    multiplyCommutative : ∀ first second → multiply first second ≡ multiply second first
    multiplyCommutative first second = cong wrap (*-comm (toℕ first) (toℕ second))

    addZero : ∀ word → add (wrap 0) word ≡ word
    addZero word = trans (cong (add (wrap 0)) (sym (wrapWord word)))
      (trans (addWrapped 0 (toℕ word)) (wrapWord word))

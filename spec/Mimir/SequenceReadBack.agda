{-# OPTIONS --safe #-}
-- A successful cursor result retains its value and the specified suffix.
module Mimir.SequenceReadBack where

open import Data.List using (List; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SequenceCursor as Cursor

module Over (Atom Code : Set) where
  private
    module C = Cursor.Over Atom Code

  data Returned {Value : Set} : ∀ {input} → C.Result Value input → Value → List Atom → Set where
    returned : ∀ {input value consumed suffix} {exact : input ≡ consumed ++ suffix} →
      Returned (C.success value consumed suffix exact) value suffix

  prefix : ∀ {Value input} bytes {result : C.Result Value input} {value suffix} →
    Returned result value suffix → Returned (C.prefix bytes result) value suffix
  prefix bytes returned = returned

  retarget : ∀ {Value input} {result : C.Result Value input} {first second before after} →
    Returned result first before → first ≡ second → before ≡ after → Returned result second after
  retarget receipt refl refl = receipt

  remaining : ∀ {Value input} {result : C.Result Value input} {value suffix} →
    Returned result value suffix → C.remaining result ≡ suffix
  remaining returned = refl

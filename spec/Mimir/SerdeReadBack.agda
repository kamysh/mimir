{-# OPTIONS --safe #-}
-- Successful decoding with both the returned value and unconsumed suffix fixed.
module Mimir.SerdeReadBack where

open import Data.List using (List; _++_)
open import Data.List.Properties using (++-cancelʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
import Mimir.SerdeFlow as Flow
open import Mimir.Bits using (Byte)

record Returned {Value input} (result : Flow.Result Value input) value suffix : Set where
  constructor returned
  field
    position : Flow.F.Cursor input
    observed : result ≡ Flow.ordinary (Flow.F.success value position)
    remaining : Flow.F.Cursor.remaining position ≡ suffix

Returns : ∀ {Value} → Flow.Parser Value → List Byte → Value → List Byte → Set
Returns reader input = Returned (Flow.Productive.result (reader input))

retarget : ∀ {Value input} {result : Flow.Result Value input} {first second before after} →
  Returned result first before → first ≡ second → before ≡ after →
  Returned result second after
retarget receipt refl refl = receipt

consumedExactly : ∀ {Value} prefix suffix (value : Value) {result : Flow.Result Value (prefix ++ suffix)}
  (receipt : Returned result value suffix) →
  Flow.F.Cursor.consumed (Returned.position receipt) ≡ prefix
consumedExactly prefix suffix value receipt = ++-cancelʳ suffix
  (Flow.F.Cursor.consumed (Returned.position receipt)) prefix
  (sym
   (trans (Flow.F.Cursor.exact (Returned.position receipt))
    (cong (Flow.F.Cursor.consumed (Returned.position receipt) ++_)
     (Returned.remaining receipt))))

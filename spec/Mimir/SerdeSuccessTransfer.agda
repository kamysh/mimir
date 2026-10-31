{-# OPTIONS --safe #-}
-- Transfer a checked success law without changing the parser or its result.
module Mimir.SerdeSuccessTransfer where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S
module F = Flow.F

implies : ∀ {Value input} (first second : Value → Set) →
  (∀ value → first value → second value) → (result : Flow.Result Value input) →
  S.Ensures first result → S.Ensures second result
implies first second transform (Flow.ordinary (F.success value position)) holds = transform value holds
implies first second transform (Flow.ordinary (F.failure error)) holds = tt
implies first second transform (Flow.panicked position) holds = tt

fromSuccess : ∀ {Value input} (property : Value → Set) (result : Flow.Result Value input) →
  (∀ value position → result ≡ Flow.ordinary (F.success value position) → property value) →
  S.Ensures property result
fromSuccess property (Flow.ordinary (F.success value position)) law = law value position refl
fromSuccess property (Flow.ordinary (F.failure error)) law = tt
fromSuccess property (Flow.panicked position) law = tt

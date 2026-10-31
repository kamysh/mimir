{-# OPTIONS --safe #-}
-- A schema-directed struct parser accepts map and positional forms. Only
-- recognized containers spend recursion allowance; ignored fields use their
-- separate iterative scanner through SerdeMember.
import Mimir.FloatConversion
module Mimir.SerdeRecord (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeMap as MapDependency
private
  module Map = MapDependency floatConversion
import Mimir.SerdePositional as Positional
import Mimir.SerdeContainer as Container
import Mimir.SerdeScalar as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SignedMachine as Machine
import Mimir.JsonTreeParser as TokensDependency
private
  module Tokens = TokensDependency floatConversion
import Mimir.JsonControls as Controls
import Mimir.NumericTokens as Numeric
import Mimir.Validation as V

module Parser (checks : Machine.OverflowChecks) (fields : List Sequence.Field)
  (readers : ℕ → Slots.Readers fields) (expected : V.Fault) where
  module S = Scalar.Parser checks

  mapBody : ℕ → ∀ input → Flow.Result (Slots.Values fields) input
  mapBody allowance = Map.Record.body fields (readers allowance)

  arrayBody : ℕ → ∀ input → Flow.Result (Slots.Values fields) input
  arrayBody allowance = Positional.body fields (readers allowance)

  dispatch : ℕ → Flow.Parser (Slots.Values fields)
  dispatch allowance [] = S.rejectAll expected []
  dispatch allowance input@(byte ∷ rest) with Tokens.classify byte
  ... | Tokens.arrayToken with allowance
  ...   | zero = Flow.productive (Flow.lift (Controls.C.fail (Controls.recursionLimit , Numeric.peek) input)) tt
  ...   | suc remaining = Container.enter byte rest (arrayBody remaining rest) Controls.arrayEnd
  dispatch allowance input@(byte ∷ rest) | Tokens.objectToken with allowance
  ... | zero = Flow.productive (Flow.lift (Controls.C.fail (Controls.recursionLimit , Numeric.peek) input)) tt
  ... | suc remaining = Container.enter byte rest (mapBody remaining rest) Controls.objectEnd
  dispatch allowance input@(byte ∷ rest) | Tokens.nullToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.trueToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.falseToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.numberToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.stringToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.invalidToken = S.rejectAll expected input

  read : ℕ → Flow.Parser (Slots.Values fields)
  read allowance input = Scalar.whitespace input (dispatch allowance)

  arrayDepthRefused : ∀ byte rest → Tokens.classify byte ≡ Tokens.arrayToken →
    Flow.Productive.result (dispatch zero (byte ∷ rest)) ≡
      Flow.lift (Controls.C.fail (Controls.recursionLimit , Numeric.peek) (byte ∷ rest))
  arrayDepthRefused byte rest classified rewrite classified = refl

  mapDepthRefused : ∀ byte rest → Tokens.classify byte ≡ Tokens.objectToken →
    Flow.Productive.result (dispatch zero (byte ∷ rest)) ≡
      Flow.lift (Controls.C.fail (Controls.recursionLimit , Numeric.peek) (byte ∷ rest))
  mapDepthRefused byte rest classified rewrite classified = refl

  arrayUsesRemaining : ∀ allowance byte rest → Tokens.classify byte ≡ Tokens.arrayToken →
    dispatch (suc allowance) (byte ∷ rest) ≡ Container.enter byte rest (arrayBody allowance rest) Controls.arrayEnd
  arrayUsesRemaining allowance byte rest classified rewrite classified = refl

  mapUsesRemaining : ∀ allowance byte rest → Tokens.classify byte ≡ Tokens.objectToken →
    dispatch (suc allowance) (byte ∷ rest) ≡ Container.enter byte rest (mapBody allowance rest) Controls.objectEnd
  mapUsesRemaining allowance byte rest classified rewrite classified = refl

{-# OPTIONS --safe #-}
-- Typed vectors parse elements in source order. The accumulator is reversed
-- internally and restored once at the closing boundary.
import Mimir.FloatConversion
module Mimir.SerdeVector (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; reverse)
import Data.List.Properties as Lists
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeLoop as Loop
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
module F = Flow.F

module Body (Value : Set) (child : Flow.Parser Value) where
  State : Set
  State = Bool × List Value

  transition : State → ∀ input → Loop.Step State (List Value) input
  transition (first , values) input with Controls.arrayNext first input
  ... | Controls.C.failure code consumed remaining exact =
    Loop.step (Flow.lift (Controls.C.failure code consumed remaining exact)) tt
  ... | Controls.C.success false consumed remaining exact =
    Loop.step (Flow.ordinary (F.success (inj₂ (reverse values)) (F.cursor consumed remaining exact))) tt
  ... | Controls.C.success true consumed remaining exact with child remaining
  ... | Flow.productive result progress = Loop.continuing (λ value → false , value ∷ values)
    (Flow.productive (Flow.prefix before result) (Flow.preserveProgress before result progress))
    where before = F.cursor consumed remaining exact

  module Run = Loop.Machine State (List Value) transition

  read : ∀ input → Flow.Result (List Value) input
  read input = Run.read (true , []) input

  boundaryKeepsOrder : ∀ first values input consumed remaining exact →
    Controls.arrayNext first input ≡ Controls.C.success false consumed remaining exact →
    Loop.Step.result (transition (first , values) input) ≡
      Flow.ordinary (F.success (inj₂ (reverse values)) (F.cursor consumed remaining exact))
  boundaryKeepsOrder first values input consumed remaining exact closed rewrite closed = refl

  appendOrder : ∀ (values : List Value) (value : Value) → reverse (value ∷ values) ≡ reverse values ++ (value ∷ [])
  appendOrder values value = Lists.unfold-reverse value values

module Parser (checks : Machine.OverflowChecks) (Value : Set)
  (child : ℕ → Flow.Parser Value) (expected : V.Fault) where
  module S = Scalar.Parser checks

  body : ℕ → ∀ input → Flow.Result (List Value) input
  body allowance = Body.read Value (child allowance)

  dispatch : ℕ → Flow.Parser (List Value)
  dispatch allowance [] = S.rejectAll expected []
  dispatch allowance input@(byte ∷ rest) with Tokens.classify byte
  ... | Tokens.arrayToken with allowance
  ... | zero = Flow.productive (Flow.lift (Controls.C.fail (Controls.recursionLimit , Numeric.peek) input)) tt
  ... | suc remaining = Container.enter byte rest (body remaining rest) Controls.arrayEnd
  dispatch allowance input@(byte ∷ rest) | Tokens.objectToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.nullToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.trueToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.falseToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.numberToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.stringToken = S.rejectAll expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.invalidToken = S.rejectAll expected input

  read : ℕ → Flow.Parser (List Value)
  read allowance input = Scalar.whitespace input (dispatch allowance)

  depthRefused : ∀ byte rest → Tokens.classify byte ≡ Tokens.arrayToken →
    Flow.Productive.result (dispatch zero (byte ∷ rest)) ≡
      Flow.lift (Controls.C.fail (Controls.recursionLimit , Numeric.peek) (byte ∷ rest))
  depthRefused byte rest classified rewrite classified = refl

  usesRemaining : ∀ allowance byte rest → Tokens.classify byte ≡ Tokens.arrayToken →
    dispatch (suc allowance) (byte ∷ rest) ≡ Container.enter byte rest (body allowance rest) Controls.arrayEnd
  usesRemaining allowance byte rest classified rewrite classified = refl

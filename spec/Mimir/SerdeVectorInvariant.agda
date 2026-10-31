{-# OPTIONS --safe #-}
-- A vector decoder returns only elements satisfying the child invariant.
import Mimir.FloatConversion
module Mimir.SerdeVectorInvariant (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; reverse)
import Data.List.Properties as Lists
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllProperties
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Mimir.SerdeVector as VectorDependency
private
  module Vector = VectorDependency floatConversion
import Mimir.SerdeLoop as Loop
import Mimir.SerdeLoopInvariant as Invariant
import Mimir.SerdeParserInvariant as ParserDependency
private
  module Parser = ParserDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S
import Mimir.SignedMachine as Machine
import Mimir.JsonTreeParser as TokensDependency
private
  module Tokens = TokensDependency floatConversion
import Mimir.JsonControls as Controls
import Mimir.Validation as V
module F = Flow.F

reverseValid : ∀ {Value : Set} {property : Value → Set} {values} →
  All property values → All property (reverse values)
reverseValid All.[] = All.[]
reverseValid {property = property} {values = value ∷ values} (valid All.∷ holds) =
  subst (All property) (sym (Lists.unfold-reverse value values)) (AllProperties.∷ʳ⁺ (reverseValid holds) valid)

module Body (Value : Set) (child : Flow.Parser Value) (property : Value → Set)
  (childValid : ∀ input → S.Ensures property (Flow.Productive.result (child input))) where
  module B = Vector.Body Value child
  module Inv = Invariant.Machine B.State (List Value) B.transition
    (λ state → All property (proj₂ state)) (All property)

  transition : ∀ state input → All property (proj₂ state) →
    S.Ensures Inv.Next (Loop.Step.result (B.transition state input))
  transition (first , values) input holds with Controls.arrayNext first input
  ... | Controls.C.failure code consumed remaining exact = tt
  ... | Controls.C.success false consumed remaining exact = reverseValid holds
  ... | Controls.C.success true consumed remaining exact =
    S.map property Inv.Next (λ value → inj₁ (false , value ∷ values)) (λ value valid → valid All.∷ holds)
      (Flow.prefix before (Flow.Productive.result (child remaining)))
      (S.prefix property before (Flow.Productive.result (child remaining)) (childValid remaining))
    where before = F.cursor consumed remaining exact

  module Run = Inv.Laws transition

  read : ∀ input → S.Ensures (All property) (B.read input)
  read input = Run.read (true , []) input All.[]

module Schema (checks : Machine.OverflowChecks) (Value : Set) (child : ℕ → Flow.Parser Value)
  (expected : V.Fault) (property : Value → Set)
  (childValid : ∀ allowance input → S.Ensures property (Flow.Productive.result (child allowance input))) where
  module R = Vector.Parser checks Value child expected

  dispatch : ∀ allowance input → S.Ensures (All property) (Flow.Productive.result (R.dispatch allowance input))
  dispatch allowance [] = Parser.rejectAll checks (All property) expected []
  dispatch allowance input@(byte ∷ rest) with Tokens.classify byte
  ... | Tokens.arrayToken with allowance
  ... | zero = tt
  ... | suc remaining = Parser.enter (All property) byte rest (R.body remaining rest) Controls.arrayEnd
    (Body.read Value (child remaining) property (childValid remaining) rest)
  dispatch allowance input@(byte ∷ rest) | Tokens.objectToken = Parser.rejectAll checks (All property) expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.nullToken = Parser.rejectAll checks (All property) expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.trueToken = Parser.rejectAll checks (All property) expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.falseToken = Parser.rejectAll checks (All property) expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.numberToken = Parser.rejectAll checks (All property) expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.stringToken = Parser.rejectAll checks (All property) expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.invalidToken = Parser.rejectAll checks (All property) expected input

  read : ∀ allowance input → S.Ensures (All property) (Flow.Productive.result (R.read allowance input))
  read allowance input = Parser.whitespace (All property) (R.dispatch allowance) (dispatch allowance) input

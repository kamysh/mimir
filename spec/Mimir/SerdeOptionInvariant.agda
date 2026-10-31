{-# OPTIONS --safe #-}
-- An optional field is absent or contains a value satisfying its child law.
import Mimir.FloatConversion
module Mimir.SerdeOptionInvariant (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([]; _∷_)
open import Data.Fin using (#_; _≟_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Relation.Unary.All using (All)
import Data.Maybe.Relation.Unary.All as All
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S
import Mimir.SerdeParserInvariant as ParserDependency
private
  module Parser = ParserDependency floatConversion
import Mimir.SerdeOption as OptionDependency
private
  module Option = OptionDependency floatConversion
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonControls as Controls

literal : ∀ {Value} (property : Value → Set) value → property value →
  ∀ first expected rest → S.Ensures property
    (Flow.Productive.result (Flow.fromJsonProductive (Atoms.literal value first expected rest)))
literal property value valid first expected rest with Controls.identifier expected rest
... | Controls.C.success tt consumed remaining exact = valid
... | Controls.C.failure code consumed remaining exact = tt

module Child (Value : Set) (child : Flow.Parser Value) (property : Value → Set)
  (childValid : ∀ input → S.Ensures property (Flow.Productive.result (child input))) where

  dispatch : ∀ input → S.Ensures (All property) (Flow.Productive.result (Option.dispatch child input))
  dispatch [] = S.map property (All property) just (λ value valid → All.just valid)
    (Flow.Productive.result (child [])) (childValid [])
  dispatch input@(byte ∷ rest) with byte ≟ (# 110)
  ... | yes isNull = literal (All property) nothing All.nothing byte ((# 117) ∷ (# 108) ∷ (# 108) ∷ []) rest
  ... | no notNull = S.map property (All property) just (λ value valid → All.just valid)
    (Flow.Productive.result (child input)) (childValid input)

  read : ∀ input → S.Ensures (All property) (Flow.Productive.result (Option.read child input))
  read input = Parser.whitespace (All property) (Option.dispatch child) dispatch input

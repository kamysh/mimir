{-# OPTIONS --safe #-}
-- Both accepted struct forms preserve the same field-indexed invariants.
-- Every reader depth and every default must provide its own proof.
import Mimir.FloatConversion
module Mimir.SerdeRecordInvariant (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeSlotInvariant as I
import Mimir.SerdeMapInvariant as MapDependency
private
  module Map = MapDependency floatConversion
import Mimir.SerdePositionalInvariant as Positional
import Mimir.SerdeParserInvariant as ParserDependency
private
  module Parser = ParserDependency floatConversion
import Mimir.SerdeRecord as RecordDependency
private
  module Record = RecordDependency floatConversion
import Mimir.SerdeSuccess as S
import Mimir.SerdeFlow as Flow
import Mimir.SignedMachine as Machine
import Mimir.JsonControls as Controls
import Mimir.JsonTreeParser as TokensDependency
private
  module Tokens = TokensDependency floatConversion
import Mimir.Validation as V

module Schema (checks : Machine.OverflowChecks) (fields : List Sequence.Field)
  (readers : ℕ → Slots.Readers fields) (expected : V.Fault) (properties : I.Predicates fields)
  (readersValid : ∀ allowance index input → S.Ensures (properties index)
    (Flow.Productive.result (Slots.readerAt fields index (readers allowance) input)))
  (defaults : I.Defaults fields properties) where
  module R = Record.Parser checks fields readers expected
  Valid = I.Valid fields properties

  mapBody : ∀ allowance input → S.Ensures Valid (R.mapBody allowance input)
  mapBody allowance input = Map.Record.body fields (readers allowance) properties (readersValid allowance) input defaults

  arrayBody : ∀ allowance input → S.Ensures Valid (R.arrayBody allowance input)
  arrayBody allowance input = Positional.read fields (readers allowance) properties (readersValid allowance) defaults 0 true input

  dispatch : ∀ allowance input → S.Ensures Valid (Flow.Productive.result (R.dispatch allowance input))
  dispatch allowance [] = Parser.rejectAll checks Valid expected []
  dispatch allowance input@(byte ∷ rest) with Tokens.classify byte
  ... | Tokens.arrayToken with allowance
  ...   | zero = tt
  ...   | suc remaining = Parser.enter Valid byte rest (R.arrayBody remaining rest) Controls.arrayEnd (arrayBody remaining rest)
  dispatch allowance input@(byte ∷ rest) | Tokens.objectToken with allowance
  ... | zero = tt
  ... | suc remaining = Parser.enter Valid byte rest (R.mapBody remaining rest) Controls.objectEnd (mapBody remaining rest)
  dispatch allowance input@(byte ∷ rest) | Tokens.nullToken = Parser.rejectAll checks Valid expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.trueToken = Parser.rejectAll checks Valid expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.falseToken = Parser.rejectAll checks Valid expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.numberToken = Parser.rejectAll checks Valid expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.stringToken = Parser.rejectAll checks Valid expected input
  dispatch allowance input@(byte ∷ rest) | Tokens.invalidToken = Parser.rejectAll checks Valid expected input

  read : ∀ allowance input → S.Ensures Valid (Flow.Productive.result (R.read allowance input))
  read allowance input = Parser.whitespace Valid (R.dispatch allowance) (dispatch allowance) input

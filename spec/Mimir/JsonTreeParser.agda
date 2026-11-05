{-# OPTIONS --safe #-}
-- Recursive serde_json::Value parsing before duplicate-key map normalization.
-- Object order/duplicates are retained here for the subsequent map fold.
import Mimir.FloatConversion
module Mimir.JsonTreeParser (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_; toℕ; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤?_; s≤s; z≤n)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Mimir.Bits using (Byte)
open import Mimir.Binary64 using (Sign)
import Mimir.FloatValue as A
import Mimir.JsonString as String
import Mimir.NumericTokens as Numeric
import Mimir.SignedMachine as Machine
import Mimir.JsonControls as Controls
import Mimir.JsonFlow as Flow
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonCollection as Collection
module F = Flow.F

open import Mimir.JsonTree public
import Mimir.JsonTreeBounds as Bounds

data Token : Set where nullToken trueToken falseToken numberToken stringToken arrayToken objectToken invalidToken : Token

classify : Byte → Token
classify byte with byte ≟ (# 110)
... | yes matched = nullToken
... | no notNull with byte ≟ (# 116)
...   | yes matched = trueToken
...   | no notTrue with byte ≟ (# 102)
...     | yes matched = falseToken
...     | no notFalse with byte ≟ (# 45)
...       | yes matched = numberToken
...       | no notMinus with byte ≟ (# 34)
...         | yes matched = stringToken
...         | no notString with byte ≟ (# 91)
...           | yes matched = arrayToken
...           | no notArray with byte ≟ (# 123)
...             | yes matched = objectToken
...             | no notObject with 48 ≤? toℕ byte
...               | no below = invalidToken
...               | yes above with toℕ byte ≤? 57
...                 | yes below = numberToken
...                 | no above = invalidToken

container : ∀ {Value Output} → (Value → Output) → (byte : Byte) → ∀ rest → Flow.Result Value rest →
  (∀ input → Controls.C.Result ⊤ input) → Flow.Productive Output (byte ∷ rest)
container wrap byte rest result finish = Flow.productive (Flow.prefix before parsed)
  (Flow.prefixProgress before (s≤s z≤n) parsed)
  where
  before = F.cursor (byte ∷ []) rest refl
  parsed = Flow.map wrap (Flow.finalize result finish)

module Parser (checks : Machine.OverflowChecks) where
  module N = Atoms.Numbers checks

  mutual
    value : (allowance : ℕ) → Flow.Parser (Bounds.Bounded allowance)
    value allowance input = Atoms.whitespace input (dispatch allowance)

    dispatch : (allowance : ℕ) → Flow.Parser (Bounds.Bounded allowance)
    dispatch allowance [] = Flow.productive (Flow.fail (Controls.eofValue , Numeric.peek) []) tt
    dispatch allowance input@(byte ∷ rest) with classify byte
    ... | nullToken = Atoms.literal (Bounds.bounded null Bounds.null) byte ((# 117) ∷ (# 108) ∷ (# 108) ∷ []) rest
    ... | trueToken = Atoms.literal (Bounds.bounded (boolean true) Bounds.boolean) byte ((# 114) ∷ (# 117) ∷ (# 101) ∷ []) rest
    ... | falseToken = Atoms.literal (Bounds.bounded (boolean false) Bounds.boolean) byte ((# 97) ∷ (# 108) ∷ (# 115) ∷ (# 101) ∷ []) rest
    ... | numberToken = Flow.mapProductive Bounds.numericValue (N.number input)
    ... | stringToken = Flow.mapProductive (λ value → Bounds.bounded (string value) Bounds.string) (Atoms.string input)
    ... | invalidToken = Flow.productive (Flow.fail (Controls.expectedValue , Numeric.peek) input) tt
    ... | arrayToken with allowance
    ...   | zero = Flow.productive (Flow.fail (Controls.recursionLimit , Numeric.peek) input) tt
    ...   | suc remaining = container Bounds.arrayValue byte rest (Collection.run Collection.arrayControl (value remaining) rest) Controls.arrayEnd
    dispatch allowance input@(byte ∷ rest) | objectToken with allowance
    ... | zero = Flow.productive (Flow.fail (Controls.recursionLimit , Numeric.peek) input) tt
    ... | suc remaining = container Bounds.objectValue byte rest (Collection.run Collection.objectControl (Atoms.member (value remaining)) rest) Controls.objectEnd

  endAt : ∀ input → Controls.C.Result ⊤ input
  endAt [] = Controls.C.done tt []
  endAt input@(byte ∷ rest) = Controls.C.fail (Controls.trailingCharacters , Numeric.peek) input

  boundedDocument : ∀ input → Flow.Productive (Bounds.Bounded 127) input
  boundedDocument input = Flow.bindProductive (value 127 input) λ tree rest →
    Flow.map (λ unit → tree) (Flow.lift (Controls.skipWhitespace rest endAt))

  document : ∀ input → Flow.Productive Tree input
  document input = Flow.mapProductive Bounds.Bounded.tree (boundedDocument input)

{-# OPTIONS --safe #-}
-- Parsed JSON tree before duplicate-key normalization. Strings retain source
-- spelling while their decoded scalar sequence determines semantic identity.
module Mimir.JsonTree where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Product using (_×_)
open import Mimir.Binary64 using (Sign)
import Mimir.FloatValue as A
import Mimir.JsonString as String
import Mimir.NumericTokens as Numeric

data ScalarNumber : Set where
  unsigned : Numeric.U64 → ScalarNumber
  signed : Numeric.I64.Integer → ScalarNumber
  floating : Sign → A.Magnitude → ScalarNumber

data Tree : Set where
  null : Tree
  boolean : Bool → Tree
  number : ScalarNumber → Tree
  string : String.StringValue → Tree
  array : List Tree → Tree
  object : List (String.StringValue × Tree) → Tree

-- Value's visit_f64 maps nonfinite inputs to Null. The staged parser's finite
-- input/result laws must establish which of these total visitor cases occur.
visitNumber : Numeric.Number → Tree
visitNumber (Numeric.unsigned64 value) = number (unsigned value)
visitNumber (Numeric.signed64 value) = number (signed value)
visitNumber (Numeric.binary64 (A.finite sign amount)) = number (floating sign amount)
visitNumber (Numeric.binary64 (A.infinity sign)) = null
visitNumber (Numeric.binary64 A.nan) = null


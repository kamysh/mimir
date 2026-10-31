{-# OPTIONS --safe #-}
-- Value boundary only: no floating arithmetic, rounding, quantization or
-- formatter implementation. Finite values reuse the numeric input domain.
module Mimir.FloatValue where

open import Data.Fin using (#_)
open import Data.Nat using (s≤s; z≤n)
import Mimir.Binary64 as B

Magnitude = B.FiniteNumber

data Number : Set where
  finite : B.Sign → Magnitude → Number
  infinity : B.Sign → Number
  nan : Number

finiteValue : B.Sign → Magnitude → B.FiniteNumber
finiteValue sign amount = B.finiteNumber
  (record (B.FiniteNumber.word amount) { sign = sign }) (B.FiniteNumber.finite amount)

opposite : B.Sign → B.Sign
opposite B.positive = B.negative
opposite B.negative = B.positive

negate : Number → Number
negate (finite sign amount) = finite (opposite sign) amount
negate (infinity sign) = infinity (opposite sign)
negate nan = nan

signedZero : B.Sign → Number
signedZero sign = finite sign (B.finiteNumber (B.bits sign (# 0) (# 0)) (s≤s z≤n))

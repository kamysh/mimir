{-# OPTIONS --safe #-}
-- The iterative ignored-value protocol. Container frames are explicit; this
-- protocol does not spend the typed deserializer's recursion-depth allowance.
import Mimir.FloatConversion
module Mimir.JsonIgnoredStep (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_; _≟_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++-≤ʳ)
open import Data.Nat using (_≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.JsonControls as Controls
import Mimir.JsonIgnoredString as String
import Mimir.JsonIgnoredNumber as Number
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.DecimalLexer as Digits
import Mimir.ByteText as Wire
import Mimir.JsonWhitespace as White
import Mimir.NumericTokens as Numeric
import Mimir.CursorProgress as Progress
module C = Controls.C
module P = Progress.Over Byte Controls.Code

data Frame : Set where
  array object : Frame

data State : Set where
  value key : List Frame → State
  boundary : List Frame → Bool → State

data Move : Set where
  finished : Move
  next : State → Move

Advances : ∀ {input} → C.Result Move input → Set
Advances (C.failure code consumed remaining exact) = ⊤
Advances (C.success finished consumed remaining exact) = ⊤
Advances (C.success (next state) consumed remaining exact) = 1 ≤ length consumed

record Step (input : List Byte) : Set where
  constructor step
  field result : C.Result Move input; progress : Advances result

reject : ∀ code input → Step input
reject code input = step (C.fail code input) tt

advance : ∀ state {input} → C.Result ⊤ input → C.Result Move input
advance state (C.failure code consumed remaining exact) = C.failure code consumed remaining exact
advance state (C.success tt consumed remaining exact) = C.success (next state) consumed remaining exact

advanceProgress : ∀ state {input} (result : C.Result ⊤ input) →
  1 ≤ length (C.consumed result) → Advances (advance state result)
advanceProgress state (C.success tt consumed remaining exact) positive = positive
advanceProgress state (C.failure code consumed remaining exact) positive = tt

consume : ∀ state byte {input} → C.Result ⊤ input → Step (byte ∷ input)
consume state byte result = step (advance state prefixed)
  (advanceProgress state prefixed (P.prefixPositive byte result))
  where prefixed = C.prefix (byte ∷ []) result

numberResult : ∀ {input} → Number.Bridge.B.Result ⊤ input → C.Result ⊤ input
numberResult (Number.Bridge.B.success tt consumed remaining exact) = C.success tt consumed remaining exact
numberResult (Number.Bridge.B.failure (reason , position) consumed remaining exact) =
  C.failure (Controls.numericError reason , position) consumed remaining exact

numberConsumption : ∀ {input} (result : Number.Bridge.B.Result ⊤ input) →
  C.consumed (numberResult result) ≡ Number.Bridge.B.consumed result
numberConsumption (Number.Bridge.B.success tt consumed remaining exact) = refl
numberConsumption (Number.Bridge.B.failure (reason , position) consumed remaining exact) = refl

number : ∀ frames byte rest → Step (byte ∷ rest)
number frames byte rest = step (advance (boundary frames true) parsed)
  (advanceProgress (boundary frames true) parsed
    (subst (λ bytes → 1 ≤ length bytes)
      (sym (numberConsumption (Number.readBytes (byte ∷ rest))))
      (Number.wireConsumes byte rest)))
  where parsed = numberResult (Number.readBytes (byte ∷ rest))

stringBody : ∀ input → C.Result ⊤ input
stringBody input with String.readBody input
... | inj₁ (String.Fault.failed code consumed remaining exact) =
  C.failure (Atoms.stringCode code) consumed remaining exact
... | inj₂ (String.parsed body valid rest exact) =
  C.success tt (String.spellBody body) rest exact

valueAt : ∀ frames input → Step input
valueAt frames [] = reject (Controls.eofValue , Numeric.peek) []
valueAt frames input@(byte ∷ rest) with byte ≟ (# 110)
... | yes refl = consume (boundary frames true) (# 110) (Controls.identifier ((# 117) ∷ (# 108) ∷ (# 108) ∷ []) rest)
... | no notNull with byte ≟ (# 116)
...   | yes refl = consume (boundary frames true) (# 116) (Controls.identifier ((# 114) ∷ (# 117) ∷ (# 101) ∷ []) rest)
...   | no notTrue with byte ≟ (# 102)
...     | yes refl = consume (boundary frames true) (# 102) (Controls.identifier ((# 97) ∷ (# 108) ∷ (# 115) ∷ (# 101) ∷ []) rest)
...     | no notFalse with byte ≟ (# 45)
...       | yes refl = number frames (# 45) rest
...       | no notMinus with Digits.classify (Wire.character byte)
...         | yes digit = number frames byte rest
...         | no notDigit with byte ≟ (# 34)
...           | yes refl = consume (boundary frames true) (# 34) (stringBody rest)
...           | no notQuote with byte ≟ (# 91)
...             | yes refl = consume (boundary (array ∷ frames) false) (# 91) (C.done tt rest)
...             | no notArray with byte ≟ (# 123)
...               | yes refl = consume (boundary (object ∷ frames) false) (# 123) (C.done tt rest)
...               | no notObject = reject (Controls.expectedValue , Numeric.peek) input

keyAt : ∀ frames input → Step input
keyAt frames [] = reject (Controls.eofObject , Numeric.peek) []
keyAt frames input@(byte ∷ rest) with byte ≟ (# 34)
... | yes refl = consume (value frames) (# 34)
    (C.andThen (stringBody rest) (λ unit suffix → Controls.colon suffix))
... | no notQuote = reject (Controls.keyString , Numeric.peek) input

closer : Frame → Byte
closer array = # 93
closer object = # 125

eof : Frame → Controls.Reason
eof array = Controls.eofList
eof object = Controls.eofObject

commaError : Frame → Controls.Reason
commaError array = Controls.expectedListCommaOrEnd
commaError object = Controls.expectedObjectCommaOrEnd

memberState : Frame → List Frame → State
memberState array frames = value (array ∷ frames)
memberState object frames = key (object ∷ frames)

memberAt : Frame → List Frame → ∀ input → Step input
memberAt array frames = valueAt (array ∷ frames)
memberAt object frames = keyAt (object ∷ frames)

boundaryAt : Frame → List Frame → Bool → ∀ input → Step input
boundaryAt frame frames acceptComma [] = reject (eof frame , Numeric.peek) []
boundaryAt frame frames acceptComma input@(byte ∷ rest) with byte ≟ closer frame
... | yes closed = consume (boundary frames true) byte (C.done tt rest)
boundaryAt frame frames false input@(byte ∷ rest) | no notClosed = memberAt frame frames input
boundaryAt frame frames true input@(byte ∷ rest) | no notClosed with byte ≟ (# 44)
... | yes refl = consume (memberState frame frames) (# 44) (C.done tt rest)
... | no notComma = reject (commaError frame , Numeric.peek) input

prefixProgress : ∀ prefix {input} (result : C.Result Move input) → Advances result →
  Advances (C.prefix prefix result)
prefixProgress prefix (C.success finished consumed remaining exact) positive = tt
prefixProgress prefix (C.success (next state) consumed remaining exact) positive =
  ≤-trans positive (length-++-≤ʳ consumed {xs = prefix})
prefixProgress prefix (C.failure code consumed remaining exact) positive = tt

skip : ∀ input → (∀ rest → Step rest) → Step input
skip input action with White.take input
... | White.run prefix spaces rest refl stopped with action rest
...   | step result positive = step (C.prefix prefix result) (prefixProgress prefix result positive)

transition : State → ∀ input → Step input
transition (value frames) input = skip input (valueAt frames)
transition (key frames) input = skip input (keyAt frames)
transition (boundary [] acceptComma) input = step (C.done finished input) tt
transition (boundary (frame ∷ frames) acceptComma) input = skip input (boundaryAt frame frames acceptComma)

{-# OPTIONS --safe #-}
-- Numeric syntax success transports to exact byte suffixes without value conversion.
import Mimir.FloatConversion
module Mimir.JsonIgnoredNumberWireReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (∷-injectiveˡ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import Mimir.Bits using (Byte)
import Mimir.ByteText as Wire
import Mimir.JsonIgnoredNumber as Number
import Mimir.JsonIgnoredStep as StepDependency
private
  module Step = StepDependency floatConversion
import Mimir.JsonIgnoredNumberReadBack as Character
import Mimir.JsonIgnoredNumberSyntax as Syntax
import Mimir.JsonNumberWire as Encoding
import Mimir.Unsigned as Decimal
import Mimir.JsonIgnoredRun as RunDependency
private
  module Run = RunDependency floatConversion
import Mimir.JsonIgnoredReadBack as IgnoredDependency
private
  module Ignored = IgnoredDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
module Bridge = Number.Bridge
module C = Step.C

data Start : Byte → Set where
  minus : Start (# 45)
  digit : ∀ value → Start (Wire.byte (Decimal.character value) (Encoding.digitBounded value))

record Starts (input : List Byte) : Set where
  constructor starts
  field first : Byte; rest : List Byte; exact : input ≡ first ∷ rest; valid : Start first

characterStart : ∀ byte value → Wire.character byte ≡ Decimal.character value → Start byte
characterStart byte value same = subst Start
  (sym
   (Wire.characterInjective byte
    (Wire.byte (Decimal.character value) (Encoding.digitBounded value))
    (trans same
     (sym
      (Wire.byteCharacter (Decimal.character value)
       (Encoding.digitBounded value))))))
  (digit value)

fromDigit : ∀ input value tail → Wire.text input ≡ Decimal.character value ∷ tail → Starts input
fromDigit (byte ∷ rest) value tail same = starts byte rest refl
  (characterStart byte value (∷-injectiveˡ same))

fromMinus : ∀ input tail → Wire.text input ≡ '-' ∷ tail → Starts input
fromMinus (byte ∷ rest) tail same = starts byte rest refl
  (subst Start
   (sym (Wire.characterInjective byte (# 45) (∷-injectiveˡ same)))
   minus)

syntaxStart : ∀ input value suffix → Wire.text input ≡ Syntax.spell value suffix → Starts input
syntaxStart input (Syntax.lexeme false Syntax.zero fractional exponential) suffix same = fromDigit input Decimal.d0
  (Syntax.fractionBytes fractional
   (Syntax.exponentBytes exponential suffix))
  same
syntaxStart input (Syntax.lexeme false (Syntax.nonzero first valid rest) fractional exponential) suffix same = fromDigit input first
  (map Decimal.character rest ++
   Syntax.fractionBytes fractional
   (Syntax.exponentBytes exponential suffix))
  same
syntaxStart input (Syntax.lexeme true value fractional exponential) suffix same = fromMinus input
  (Syntax.integerBytes value
   (Syntax.fractionBytes fractional
    (Syntax.exponentBytes exponential suffix)))
  same

dispatch : ∀ frames byte rest → Start byte →
  Step.Step.result (Step.transition (Step.value frames) (byte ∷ rest)) ≡
  C.prefix [] (Step.advance (Step.boundary frames true) (Step.numberResult (Number.readBytes (byte ∷ rest))))
dispatch frames .(# 45) rest minus = refl
dispatch frames .(Wire.byte (Decimal.character Decimal.d0) (Encoding.digitBounded Decimal.d0)) rest (digit Decimal.d0) = refl
dispatch frames .(Wire.byte (Decimal.character Decimal.d1) (Encoding.digitBounded Decimal.d1)) rest (digit Decimal.d1) = refl
dispatch frames .(Wire.byte (Decimal.character Decimal.d2) (Encoding.digitBounded Decimal.d2)) rest (digit Decimal.d2) = refl
dispatch frames .(Wire.byte (Decimal.character Decimal.d3) (Encoding.digitBounded Decimal.d3)) rest (digit Decimal.d3) = refl
dispatch frames .(Wire.byte (Decimal.character Decimal.d4) (Encoding.digitBounded Decimal.d4)) rest (digit Decimal.d4) = refl
dispatch frames .(Wire.byte (Decimal.character Decimal.d5) (Encoding.digitBounded Decimal.d5)) rest (digit Decimal.d5) = refl
dispatch frames .(Wire.byte (Decimal.character Decimal.d6) (Encoding.digitBounded Decimal.d6)) rest (digit Decimal.d6) = refl
dispatch frames .(Wire.byte (Decimal.character Decimal.d7) (Encoding.digitBounded Decimal.d7)) rest (digit Decimal.d7) = refl
dispatch frames .(Wire.byte (Decimal.character Decimal.d8) (Encoding.digitBounded Decimal.d8)) rest (digit Decimal.d8) = refl
dispatch frames .(Wire.byte (Decimal.character Decimal.d9) (Encoding.digitBounded Decimal.d9)) rest (digit Decimal.d9) = refl

advanceFinish : ∀ input (result : C.Result ⊤ input) suffix →
  Back.Returned (Flow.lift result) tt suffix →
  Step.Step.result (Step.transition (Step.value []) input) ≡
    C.prefix [] (Step.advance (Step.boundary [] true) result) →
  Back.Returned (Flow.lift (Run.read input)) tt suffix
advanceFinish input (C.failure code consumed remaining exact) suffix (Back.returned position () end) equation
advanceFinish input (C.success tt consumed remaining exact) suffix (Back.returned position refl end) equation = Back.retarget (Ignored.finish consumed remaining _ equation) refl
  end

read : ∀ input suffix → Starts input →
  Back.Returned (Flow.lift (Step.numberResult (Number.readBytes input))) tt suffix →
  Back.Returned (Flow.lift (Run.read input)) tt suffix
read .(byte ∷ rest) suffix (starts byte rest refl valid) receipt = advanceFinish (byte ∷ rest)
  (Step.numberResult (Number.readBytes (byte ∷ rest))) suffix receipt
  (dispatch [] byte rest valid)

transport : ∀ input suffix {result : Number.C.Result ⊤ (Wire.text input)} →
  Character.Returned result (Wire.text suffix) →
  Back.Returned (Flow.lift (Step.numberResult (Bridge.transport result))) tt suffix
transport input suffix (Character.returned consumed exact refl) = Back.returned _ refl
  (Wire.textInjective _ suffix
   (Bridge.remainingText
    (Number.C.success tt consumed (Wire.text suffix) exact)))

complete : ∀ (input suffix : List Byte) value →
  Wire.text input ≡ Syntax.spell value (Wire.text suffix) →
  Character.Stopped (Wire.text suffix) →
  Back.Returned (Flow.lift (Step.numberResult (Number.readBytes input))) tt suffix
complete input suffix value spelling stopped = transport input suffix
  (subst
   (λ text → Character.Returned (Number.read text) (Wire.text suffix))
   (sym spelling) (Syntax.complete value (Wire.text suffix) stopped))

ignored : ∀ (input suffix : List Byte) value →
  Wire.text input ≡ Syntax.spell value (Wire.text suffix) →
  Character.Stopped (Wire.text suffix) →
  Back.Returned (Flow.lift (Run.read input)) tt suffix
ignored input suffix value spelling stopped = read input suffix
  (syntaxStart input value (Wire.text suffix) spelling)
  (complete input suffix value spelling stopped)

{-# OPTIONS --safe #-}
-- Productive scalar parsers and object-member composition for recursive JSON.
import Mimir.FloatConversion
module Mimir.JsonAtoms (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (_≤_; s≤s; z≤n)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Mimir.Bits using (Byte)
import Mimir.JsonString as String
import Mimir.JsonStringParser as Strings
import Mimir.JsonControls as Controls
import Mimir.JsonFlow as Flow
import Mimir.JsonWhitespace as White
import Mimir.NumericTokens as Numeric
import Mimir.SerdeNumericWire as NumericWireDependency
private
  module NumericWire = NumericWireDependency floatConversion
import Mimir.SerdeNumericProgress as NumericProgressDependency
private
  module NumericProgress = NumericProgressDependency floatConversion
import Mimir.SignedMachine as Machine
module F = Flow.F

stringCode : Strings.Code → Controls.Code
stringCode Strings.expectedQuote = Controls.stringError Strings.expectedQuote , Numeric.peek
stringCode code = Controls.stringError code , Numeric.current

string : Flow.Parser String.StringValue
string input with Strings.parse input
... | inj₁ (Strings.Fault.failed code consumed remaining exact) = Flow.productive
    (Flow.lift (Controls.C.failure (stringCode code) consumed remaining exact)) tt
... | inj₂ (Strings.parsed value rest exact) = Flow.productive
    (Flow.ordinary (F.success value (F.cursor (String.spellString (String.StringValue.body value)) rest exact))) (s≤s z≤n)

literal : ∀ {Value} → Value → (first : Byte) → List Byte → ∀ rest → Flow.Productive Value (first ∷ rest)
literal value first expected rest = Flow.productive (Flow.prefix before parsed) (Flow.prefixProgress before (s≤s z≤n) parsed)
  where
  before = F.cursor (first ∷ []) rest refl
  parsed = Flow.map (λ unit → value) (Flow.lift (Controls.identifier expected rest))

whitespace : ∀ {Value} input → Flow.Parser Value → Flow.Productive Value input
whitespace input next with White.take input
... | White.run consumed spaces remaining exact stopped with next remaining
...   | Flow.productive result progress = Flow.productive (Flow.prefix before result) (Flow.preserveProgress before result progress)
  where before = F.cursor consumed remaining exact

numericResult : ∀ {input} → NumericWire.Bridge.B.Result Numeric.Number input → Flow.Result Numeric.Number input
numericResult (NumericWire.Bridge.B.success value consumed remaining exact) = Flow.ordinary (F.success value (F.cursor consumed remaining exact))
numericResult (NumericWire.Bridge.B.failure (Numeric.arithmeticPanic , position) consumed remaining exact) = Flow.panicked (F.cursor consumed remaining exact)
numericResult (NumericWire.Bridge.B.failure (Numeric.invalidNumber , position) consumed remaining exact) =
  Flow.lift (Controls.C.failure (Controls.numericError Numeric.invalidNumber , position) consumed remaining exact)
numericResult (NumericWire.Bridge.B.failure (Numeric.eofValue , position) consumed remaining exact) =
  Flow.lift (Controls.C.failure (Controls.numericError Numeric.eofValue , position) consumed remaining exact)
numericResult (NumericWire.Bridge.B.failure (Numeric.numberOutOfRange , position) consumed remaining exact) =
  Flow.lift (Controls.C.failure (Controls.numericError Numeric.numberOutOfRange , position) consumed remaining exact)

numericResultProgress : ∀ {input} (result : NumericWire.Bridge.B.Result Numeric.Number input) →
  1 ≤ length (NumericWire.Bridge.B.consumed result) → Flow.Progress (numericResult result)
numericResultProgress (NumericWire.Bridge.B.success value consumed remaining exact) progress = progress
numericResultProgress (NumericWire.Bridge.B.failure (Numeric.arithmeticPanic , position) consumed remaining exact) progress = tt
numericResultProgress (NumericWire.Bridge.B.failure (Numeric.invalidNumber , position) consumed remaining exact) progress = tt
numericResultProgress (NumericWire.Bridge.B.failure (Numeric.eofValue , position) consumed remaining exact) progress = tt
numericResultProgress (NumericWire.Bridge.B.failure (Numeric.numberOutOfRange , position) consumed remaining exact) progress = tt

module Numbers (checks : Machine.OverflowChecks) where
  module N = NumericWire.Parser checks
  module P = NumericProgress.Parser checks

  number : Flow.Parser Numeric.Number
  number [] = Flow.productive (Flow.fail (Controls.numericError Numeric.eofValue , Numeric.current) []) tt
  number (byte ∷ rest) = Flow.productive (numericResult parsed) (numericResultProgress parsed (P.wireConsumes byte rest))
    where parsed = N.read (byte ∷ rest)

member : ∀ {Value} → Flow.Parser Value → Flow.Parser (String.StringValue × Value)
member child input = Flow.bindProductive (string input) λ key rest →
  Flow.andThen (Flow.lift (Controls.colon rest)) λ unit valueInput →
    Flow.map (λ value → key , value) (Flow.Productive.result (child valueInput))

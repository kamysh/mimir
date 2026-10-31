{-# OPTIONS --safe #-}
-- Failures retain their reason, position mode and exact unread suffix through
-- whitespace and every preceding successful transition of the ignored reader.
import Mimir.FloatConversion
module Mimir.JsonIgnoredFailure (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (#_; _≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-cancelʳ)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.JsonIgnoredStep as StepDependency
private
  module Step = StepDependency floatConversion
import Mimir.JsonIgnoredRun as RunDependency
private
  module Run = RunDependency floatConversion
import Mimir.JsonIgnoredPath as PathDependency
private
  module Path = PathDependency floatConversion
import Mimir.JsonIgnoredWhitespacePath as WhitespaceDependency
private
  module Whitespace = WhitespaceDependency floatConversion
import Mimir.JsonWhitespace as White
import Mimir.JsonControls as Controls
import Mimir.JsonIgnoredString as String
import Mimir.JsonIgnoredNumber as Number
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.NumericTokens as Numeric
module C = Step.C

data Failed {Value input} : C.Result Value input → Controls.Code → List Byte → Set where
  failed : ∀ {code consumed remaining exact} → Failed (C.failure code consumed remaining exact) code remaining

noSuccess : ∀ {Value input} (value : Value) consumed remaining (exact : input ≡ consumed ++ remaining)
  code suffix → Failed (C.success value consumed remaining exact) code suffix → ⊥
noSuccess value consumed remaining exact code suffix ()

prefix : ∀ {Value input code suffix} bytes (result : C.Result Value input) →
  Failed result code suffix → Failed (C.prefix bytes result) code suffix
prefix bytes (C.failure code consumed remaining exact) failed = failed

reframe : ∀ {Value input source code suffix} (exact : input ≡ source) (result : C.Result Value source) →
  Failed result code suffix → Failed (C.reframe exact result) code suffix
reframe refl result receipt = receipt

path : ∀ {Value state input target rest code suffix} (segment : Path.Path state input target rest)
  (result : C.Result Value rest) → Failed result code suffix → Failed (Path.prepend segment result) code suffix
path Path.stop result receipt = receipt
path (Path.next following consumed remaining exact observed tail) result receipt = reframe exact (C.prefix consumed (Path.prepend tail result))
  (prefix consumed (Path.prepend tail result)
   (path tail result receipt))

after : ∀ input target rest (segment : Path.Path (Step.value []) input target rest)
  code consumed remaining exact →
  Step.Step.result (Step.transition target rest) ≡ C.failure code consumed remaining exact →
  Failed (Run.read input) code remaining
after input target rest segment code consumed remaining exact observed = subst (λ result → Failed result code remaining)
  (sym
   (Run.complete input
    (Path.prepend segment (C.failure code consumed remaining exact))
    (Path.continue segment (C.failure code consumed remaining exact)
     (Run.rejected code consumed remaining exact observed))))
  (path segment (C.failure code consumed remaining exact) failed)

space : ∀ {state input code suffix} → Whitespace.Skips state → ∀ byte → White.Space byte →
  Failed (Step.Step.result (Step.transition state input)) code suffix →
  Failed (Step.Step.result (Step.transition state (byte ∷ input))) code suffix
space {state} {input} {code} {suffix} skips byte admitted receipt = subst (λ result → Failed result code suffix)
  (sym (Whitespace.transitionSpace skips byte admitted input))
  (prefix (byte ∷ [])
   (Step.Step.result (Step.transition state input)) receipt)

spaces : ∀ {state input code suffix} → Whitespace.Skips state → ∀ before → All White.Space before →
  Failed (Step.Step.result (Step.transition state input)) code suffix →
  Failed (Step.Step.result (Step.transition state (before ++ input))) code suffix
spaces skips [] All.[] receipt = receipt
spaces skips (byte ∷ before) (admitted All.∷ valid) receipt = space skips byte admitted (spaces skips before valid receipt)

skipStopped : ∀ input → White.Stopped input → ∀ action →
  Step.Step.result (Step.skip input action) ≡ C.prefix [] (Step.Step.result (action input))
skipStopped input stopped action with White.take input | White.stoppedRun input stopped
... | White.run .[] valid .input refl terminal | refl , refl = refl

valueEof : ∀ frames → Failed (Step.Step.result (Step.transition (Step.value frames) []))
  (Controls.eofValue , Numeric.peek) []
valueEof frames = failed

keyEof : ∀ frames → Failed (Step.Step.result (Step.transition (Step.key frames) []))
  (Controls.eofObject , Numeric.peek) []
keyEof frames = failed

boundaryEof : ∀ frame frames comma →
  Failed (Step.Step.result (Step.transition (Step.boundary (frame ∷ frames) comma) []))
    (Step.eof frame , Numeric.peek) []
boundaryEof frame frames comma = failed

keyAtUnquoted : ∀ frames byte rest → byte ≢ (# 34) →
  Failed (Step.Step.result (Step.keyAt frames (byte ∷ rest))) (Controls.keyString , Numeric.peek) (byte ∷ rest)
keyAtUnquoted frames byte rest notQuote with byte ≟ (# 34)
... | yes same = ⊥-elim (notQuote same)
... | no other = failed

keyUnquoted : ∀ frames byte rest → White.Stopped (byte ∷ rest) → byte ≢ (# 34) →
  Failed (Step.Step.result (Step.transition (Step.key frames) (byte ∷ rest)))
    (Controls.keyString , Numeric.peek) (byte ∷ rest)
keyUnquoted frames byte rest stopped notQuote = subst
  (λ result →
     Failed result (Controls.keyString , Numeric.peek) (byte ∷ rest))
  (sym (skipStopped (byte ∷ rest) stopped (Step.keyAt frames)))
  (prefix [] (Step.Step.result (Step.keyAt frames (byte ∷ rest)))
   (keyAtUnquoted frames byte rest notQuote))

missingCommaAt : ∀ frame frames byte rest → byte ≢ Step.closer frame → byte ≢ (# 44) →
  Failed (Step.Step.result (Step.boundaryAt frame frames true (byte ∷ rest)))
    (Step.commaError frame , Numeric.peek) (byte ∷ rest)
missingCommaAt frame frames byte rest notClosed notComma with byte ≟ Step.closer frame
... | yes closed = ⊥-elim (notClosed closed)
... | no other with byte ≟ (# 44)
...   | yes comma = ⊥-elim (notComma comma)
...   | no absent = failed

missingComma : ∀ frame frames byte rest → White.Stopped (byte ∷ rest) →
  byte ≢ Step.closer frame → byte ≢ (# 44) →
  Failed (Step.Step.result (Step.transition (Step.boundary (frame ∷ frames) true) (byte ∷ rest)))
    (Step.commaError frame , Numeric.peek) (byte ∷ rest)
missingComma frame frames byte rest stopped notClosed notComma = subst
  (λ result →
     Failed result (Step.commaError frame , Numeric.peek) (byte ∷ rest))
  (sym
   (skipStopped (byte ∷ rest) stopped
    (Step.boundaryAt frame frames true)))
  (prefix []
   (Step.Step.result
    (Step.boundaryAt frame frames true (byte ∷ rest)))
   (missingCommaAt frame frames byte rest notClosed notComma))

trailingArray : ∀ frames suffix →
  Failed (Step.Step.result (Step.transition (Step.value (Step.array ∷ frames)) ((# 93) ∷ suffix)))
    (Controls.expectedValue , Numeric.peek) ((# 93) ∷ suffix)
trailingArray frames suffix = failed

trailingObject : ∀ frames suffix →
  Failed (Step.Step.result (Step.transition (Step.key (Step.object ∷ frames)) ((# 125) ∷ suffix)))
    (Controls.keyString , Numeric.peek) ((# 125) ∷ suffix)
trailingObject frames suffix = failed

consumedExactly : ∀ {Value} before suffix code (result : C.Result Value (before ++ suffix)) →
  Failed result code suffix → C.consumed result ≡ before
consumedExactly before suffix code (C.failure .code consumed .suffix exact) failed = ++-cancelʳ suffix consumed before (sym exact)

andThen : ∀ {First Second input code suffix} (result : C.Result First input)
  (next : First → ∀ rest → C.Result Second rest) → Failed result code suffix →
  Failed (C.andThen result next) code suffix
andThen (C.failure code consumed remaining exact) next failed = failed

advance : ∀ {input code suffix} state result → Failed {input = input} result code suffix →
  Failed (Step.advance state result) code suffix
advance state (C.failure code consumed remaining exact) failed = failed

consume : ∀ {input code suffix} state byte result → Failed {input = input} result code suffix →
  Failed (Step.Step.result (Step.consume state byte result)) code suffix
consume state byte result receipt = advance state (C.prefix (byte ∷ []) result)
  (prefix (byte ∷ []) result receipt)

stringBody : ∀ input code consumed remaining exact →
  String.readBody input ≡ inj₁ (String.Fault.failed code consumed remaining exact) →
  Failed (Step.stringBody input) (Atoms.stringCode code) remaining
stringBody input code consumed remaining exact observed with String.readBody input
... | inj₁ (String.Fault.failed actual before after precise) with observed
...   | refl = failed
stringBody input code consumed remaining exact () | inj₂ accepted

numeric : ∀ input reason position consumed remaining exact →
  Number.readBytes input ≡ Number.Bridge.B.failure (reason , position) consumed remaining exact →
  Failed (Step.numberResult (Number.readBytes input)) (Controls.numericError reason , position) remaining
numeric input reason position consumed remaining exact observed = subst
  (λ result →
     Failed (Step.numberResult result)
     (Controls.numericError reason , position) remaining)
  (sym observed) failed

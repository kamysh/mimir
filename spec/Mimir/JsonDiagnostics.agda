{-# OPTIONS --safe #-}
-- Every ordinary error from the complete JSON parser has a source message.
-- Checked-profile arithmetic panics remain separate, never fabricated as a
-- generic syntax error. The result holds for both overflow profiles.
import Mimir.FloatConversion
module Mimir.JsonDiagnostics (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (#_)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
import Mimir.JsonFlow as Flow
import Mimir.JsonControls as Controls
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonStringParser as Strings
import Mimir.JsonWhitespace as White
import Mimir.JsonCollection as Collection
import Mimir.JsonTreeParser as TreeDependency
private
  module Tree = TreeDependency floatConversion
import Mimir.JsonTreeBounds as Bounds
import Mimir.JsonDecode as DecodeDependency
private
  module Decode = DecodeDependency floatConversion
import Mimir.NumericTokens as Numeric
import Mimir.SerdeNumericWire as WireDependency
private
  module Wire = WireDependency floatConversion
import Mimir.SignedMachine as Machine
import Mimir.JsonDiagnosticCode as Safe
import Mimir.JsonControlDiagnostics as Control
module F = Flow.F

numeric : ∀ {input} (result : Wire.Bridge.B.Result Numeric.Number input) → Safe.Safe (Atoms.numericResult result)
numeric (Wire.Bridge.B.success value consumed remaining exact) = tt
numeric (Wire.Bridge.B.failure (Numeric.arithmeticPanic , mode) consumed remaining exact) = tt
numeric (Wire.Bridge.B.failure (Numeric.invalidNumber , mode) consumed remaining exact) = λ ()
numeric (Wire.Bridge.B.failure (Numeric.eofValue , mode) consumed remaining exact) = λ ()
numeric (Wire.Bridge.B.failure (Numeric.numberOutOfRange , mode) consumed remaining exact) = λ ()

stringCode : ∀ code → Safe.CodeSafe (Atoms.stringCode code)
stringCode Strings.eofString = λ ()
stringCode Strings.controlCharacter = λ ()
stringCode Strings.expectedQuote = λ ()
stringCode (Strings.escapeError code) = λ ()
stringCode (Strings.invalidUnicode code) = λ ()

string : ∀ input → Safe.Safe (Flow.Productive.result (Atoms.string input))
string input with Strings.parse input
... | inj₁ (Strings.Fault.failed code consumed remaining exact) = stringCode code
... | inj₂ (Strings.parsed value rest exact) = tt

literal : ∀ {Value} (value : Value) first expected rest → Safe.Safe (Flow.Productive.result (Atoms.literal value first expected rest))
literal value first expected rest = Safe.prefix (F.cursor (first ∷ []) rest refl) _
  (Safe.map (λ unit → value) (Flow.lift (Controls.identifier expected rest))
    (Safe.lift (Controls.identifier expected rest) (Control.identifier expected rest)))

whitespace : ∀ {Value} input (child : Flow.Parser Value) →
  (∀ remaining → Safe.Safe (Flow.Productive.result (child remaining))) → Safe.Safe (Flow.Productive.result (Atoms.whitespace input child))
whitespace input child safe with White.take input
... | White.run consumed spaces remaining exact stopped with child remaining | safe remaining
...   | Flow.productive result progress | checked = Safe.prefix (F.cursor consumed remaining exact) result checked

member : ∀ {Value} (child : Flow.Parser Value) → (∀ remaining → Safe.Safe (Flow.Productive.result (child remaining))) →
  ∀ input → Safe.Safe (Flow.Productive.result (Atoms.member child input))
member child safe input = Safe.productiveBind (Atoms.string input) _ (string input) λ key rest →
  Safe.andThen (Flow.lift (Controls.colon rest)) _ (Safe.lift (Controls.colon rest) (Control.colon rest)) λ unit valueInput →
    Safe.map (λ value → key , value) (Flow.Productive.result (child valueInput)) (safe valueInput)

loop : ∀ {Value} control → Safe.CodeSafe (Collection.Control.emptyCode control) →
  (∀ first input → Safe.Atomic (Collection.Control.next control first input)) →
  (child : Flow.Parser Value) → (∀ input → Safe.Safe (Flow.Productive.result (child input))) →
  ∀ fuel first input bounded → Safe.Safe (Collection.loop control child fuel first input bounded)
loop control emptySafe nextSafe child childSafe zero first [] bounded = emptySafe
loop control emptySafe nextSafe child childSafe zero first (byte ∷ rest) ()
loop {Value} control emptySafe nextSafe child childSafe (suc fuel) first input bounded
  with Collection.Control.next control first input | nextSafe first input
... | Controls.C.failure code consumed remaining exact | safe = safe
... | Controls.C.success false consumed remaining exact | safe = tt
... | Controls.C.success true consumed remaining exact | safe with child remaining | childSafe remaining
...   | Flow.productive (Flow.panicked position) progress | checked = tt
...   | Flow.productive (Flow.ordinary (F.failure faultValue)) progress | checked =
  Safe.prefix {Value = Data.List.List Value} (F.cursor consumed remaining exact) (Flow.ordinary (F.failure faultValue)) checked
...   | Flow.productive (Flow.ordinary (F.success value position)) progress | checked =
  Safe.prefix (F.cursor consumed remaining exact) _ (Safe.prefix position _ (Safe.map (value ∷_) _
    (loop control emptySafe nextSafe child childSafe fuel false (F.Cursor.remaining position)
      (Collection.childBound fuel (F.cursor consumed remaining exact) position bounded progress))))

collection : ∀ {Value} control → Safe.CodeSafe (Collection.Control.emptyCode control) →
  (∀ first input → Safe.Atomic (Collection.Control.next control first input)) →
  (child : Flow.Parser Value) → (∀ input → Safe.Safe (Flow.Productive.result (child input))) →
  ∀ input → Safe.Safe (Collection.run control child input)
collection control emptySafe nextSafe child childSafe input =
  loop control emptySafe nextSafe child childSafe (length input) true input ≤-refl

container : ∀ {Value Output} (wrap : Value → Output) byte rest result finish → Safe.Safe result →
  (∀ input → Safe.Atomic (finish input)) → Safe.Safe (Flow.Productive.result (Tree.container wrap byte rest result finish))
container wrap byte rest result finish checked finishSafe = Safe.prefix (F.cursor (byte ∷ []) rest refl) _
  (Safe.map wrap (Flow.finalize result finish) (Safe.finalize result finish checked finishSafe))

module Parser (checks : Machine.OverflowChecks) where
  module T = Tree.Parser checks
  module N = Atoms.Numbers checks
  module D = Decode.Parser checks

  number : ∀ input → Safe.Safe (Flow.Productive.result (N.number input))
  number [] = λ ()
  number (byte ∷ rest) = numeric (N.N.read (byte ∷ rest))

  mutual
    value : ∀ allowance input → Safe.Safe (Flow.Productive.result (T.value allowance input))
    value allowance input = whitespace input (T.dispatch allowance) (dispatch allowance)

    dispatch : ∀ allowance input → Safe.Safe (Flow.Productive.result (T.dispatch allowance input))
    dispatch allowance [] = λ ()
    dispatch allowance input@(byte ∷ rest) with Tree.classify byte
    ... | Tree.nullToken = literal _ byte ((# 117) ∷ (# 108) ∷ (# 108) ∷ []) rest
    ... | Tree.trueToken = literal _ byte ((# 114) ∷ (# 117) ∷ (# 101) ∷ []) rest
    ... | Tree.falseToken = literal _ byte ((# 97) ∷ (# 108) ∷ (# 115) ∷ (# 101) ∷ []) rest
    ... | Tree.numberToken = Safe.productiveMap Bounds.numericValue (N.number input) (number input)
    ... | Tree.stringToken = Safe.productiveMap _ (Atoms.string input) (string input)
    ... | Tree.invalidToken = λ ()
    ... | Tree.arrayToken with allowance
    ...   | zero = λ ()
    ...   | suc remaining = container Bounds.arrayValue byte rest _ Controls.arrayEnd
      (collection Collection.arrayControl (λ ()) Control.arrayNext (T.value remaining) (value remaining) rest) Control.arrayEnd
    dispatch allowance input@(byte ∷ rest) | Tree.objectToken with allowance
    ... | zero = λ ()
    ... | suc remaining = container Bounds.objectValue byte rest _ Controls.objectEnd
      (collection Collection.objectControl (λ ()) Control.objectNext (Atoms.member (T.value remaining))
        (member (T.value remaining) (value remaining)) rest) Control.objectEnd

  endAt : ∀ input → Safe.Atomic (T.endAt input)
  endAt [] = tt
  endAt (byte ∷ rest) = λ ()

  boundedDocument : ∀ input → Safe.Safe (Flow.Productive.result (T.boundedDocument input))
  boundedDocument input = Safe.productiveBind (T.value 127 input) _ (value 127 input) λ tree rest →
    Safe.map (λ unit → tree) (Flow.lift (Controls.skipWhitespace rest T.endAt))
      (Safe.lift (Controls.skipWhitespace rest T.endAt) (Control.whitespace rest T.endAt endAt))

  decodedDocument : ∀ input → Safe.Safe (Flow.Productive.result (D.read input))
  decodedDocument input = Safe.productiveMap Decode.build (T.boundedDocument input) (boundedDocument input)

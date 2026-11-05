{-# OPTIONS --safe #-}
-- Complete release-profile JSON parsing has no checked-arithmetic panic
-- outcome. Ordinary syntax/number/depth errors remain explicit results.
import Mimir.FloatConversion
module Mimir.JsonOrdinary (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (zero; suc; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)
import Mimir.JsonFlow as Flow
import Mimir.JsonControls as Controls
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonStringParser as Strings
import Mimir.JsonString as String
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
import Mimir.SerdeNumericOrdinary as OrdinaryDependency
private
  module Ordinary = OrdinaryDependency floatConversion
import Mimir.SerdeNumericWire as WireDependency
private
  module Wire = WireDependency floatConversion
import Mimir.ByteText as ByteText
import Mimir.SignedMachine as Machine
module F = Flow.F
module T = Tree.Parser Machine.disabled
module N = Atoms.Numbers Machine.disabled
module D = Decode.Parser Machine.disabled

Normal : ∀ {Value input} → Flow.Result Value input → Set
Normal (Flow.ordinary result) = ⊤
Normal (Flow.panicked position) = ⊥

lift : ∀ {Value input} (result : Controls.C.Result Value input) → Normal (Flow.lift result)
lift result = tt

prefix : ∀ {Value input} before (result : Flow.Result Value (F.Cursor.remaining {input} before)) →
  Normal result → Normal (Flow.prefix before result)
prefix before (Flow.ordinary (F.success value after)) normal = tt
prefix before (Flow.ordinary (F.failure faultValue)) normal = tt
prefix before (Flow.panicked position) ()

map : ∀ {A B input} (change : A → B) (result : Flow.Result A input) → Normal result → Normal (Flow.map change result)
map change (Flow.ordinary (F.success value position)) normal = tt
map change (Flow.ordinary (F.failure faultValue)) normal = tt
map change (Flow.panicked position) ()

finalize : ∀ {Value input} (result : Flow.Result Value input) finish → Normal result → Normal (Flow.finalize result finish)
finalize (Flow.ordinary result) finish normal = tt
finalize (Flow.panicked position) finish ()

andThen : ∀ {A B input} (result : Flow.Result A input) next → Normal result →
  (∀ value rest → Normal (next value rest)) → Normal (Flow.andThen {Second = B} result next)
andThen (Flow.panicked position) next () children
andThen (Flow.ordinary (F.failure faultValue)) next normal children = tt
andThen (Flow.ordinary (F.success value before)) next normal children =
  prefix before (next value (F.Cursor.remaining before)) (children value (F.Cursor.remaining before))

productiveMap : ∀ {A B input} (change : A → B) (result : Flow.Productive A input) →
  Normal (Flow.Productive.result result) → Normal (Flow.Productive.result (Flow.mapProductive change result))
productiveMap change (Flow.productive result progress) = map change result

productiveBind : ∀ {A B input} (result : Flow.Productive A input) next → Normal (Flow.Productive.result result) →
  (∀ value rest → Normal (next value rest)) → Normal (Flow.Productive.result (Flow.bindProductive {Second = B} result next))
productiveBind (Flow.productive result progress) next = andThen result next

numericTransport : ∀ {input} (result : Numeric.C.Result Numeric.Number (ByteText.text input)) →
  Ordinary.Ordinary result → Normal (Atoms.numericResult (Wire.Bridge.transport result))
numericTransport {input} (Numeric.C.success value consumed remaining exact) normal
  with Wire.Bridge.splitAt input consumed remaining exact
... | Wire.Bridge.split before after beforeText afterText exactBytes = tt
numericTransport {input} (Numeric.C.failure (Numeric.arithmeticPanic , position) consumed remaining exact) normal = ⊥-elim (normal refl)
numericTransport {input} (Numeric.C.failure (Numeric.invalidNumber , position) consumed remaining exact) normal
  with Wire.Bridge.splitAt input consumed remaining exact
... | Wire.Bridge.split before after beforeText afterText exactBytes = tt
numericTransport {input} (Numeric.C.failure (Numeric.eofValue , position) consumed remaining exact) normal
  with Wire.Bridge.splitAt input consumed remaining exact
... | Wire.Bridge.split before after beforeText afterText exactBytes = tt
numericTransport {input} (Numeric.C.failure (Numeric.numberOutOfRange , position) consumed remaining exact) normal
  with Wire.Bridge.splitAt input consumed remaining exact
... | Wire.Bridge.split before after beforeText afterText exactBytes = tt

number : ∀ input → Normal (Flow.Productive.result (N.number input))
number [] = tt
number (byte ∷ rest) = numericTransport (Ordinary.P.read (ByteText.text (byte ∷ rest))) (Ordinary.read (ByteText.text (byte ∷ rest)))

string : ∀ input → Normal (Flow.Productive.result (Atoms.string input))
string input with Strings.parse input
... | inj₁ (Strings.Fault.failed code consumed remaining exact) = tt
... | inj₂ (Strings.parsed value rest exact) = tt

literal : ∀ {Value} (value : Value) first expected rest → Normal (Flow.Productive.result (Atoms.literal value first expected rest))
literal value first expected rest = prefix (F.cursor (first ∷ []) rest refl) _
  (map (λ unit → value) (Flow.lift (Controls.identifier expected rest)) tt)

whitespace : ∀ {Value} input (child : Flow.Parser Value) →
  (∀ remaining → Normal (Flow.Productive.result (child remaining))) → Normal (Flow.Productive.result (Atoms.whitespace input child))
whitespace input child normal with White.take input
... | White.run consumed spaces remaining exact stopped with child remaining | normal remaining
...   | Flow.productive result progress | checked = prefix (F.cursor consumed remaining exact) result checked

member : ∀ {Value} (child : Flow.Parser Value) → (∀ remaining → Normal (Flow.Productive.result (child remaining))) →
  ∀ input → Normal (Flow.Productive.result (Atoms.member child input))
member child normal input = productiveBind (Atoms.string input) _ (string input) λ key rest →
  andThen (Flow.lift (Controls.colon rest)) _ tt λ unit valueInput →
    map (λ value → key , value) (Flow.Productive.result (child valueInput)) (normal valueInput)

loop : ∀ {Value} control (child : Flow.Parser Value) → (∀ input → Normal (Flow.Productive.result (child input))) →
  ∀ fuel first input bounded → Normal (Collection.loop control child fuel first input bounded)
loop control child normal zero first [] bounded = tt
loop control child normal zero first (byte ∷ rest) ()
loop control child normal (suc fuel) first input bounded with Collection.Control.next control first input
... | Controls.C.failure code consumed remaining exact = tt
... | Controls.C.success false consumed remaining exact = tt
... | Controls.C.success true consumed remaining exact with child remaining | normal remaining
...   | Flow.productive (Flow.panicked position) progress | ()
...   | Flow.productive (Flow.ordinary (F.failure faultValue)) progress | checked = tt
...   | Flow.productive (Flow.ordinary (F.success value position)) progress | checked =
  prefix (F.cursor consumed remaining exact) _ (prefix position _ (map (value ∷_) _
    (loop control child normal fuel false (F.Cursor.remaining position)
      (Collection.childBound fuel (F.cursor consumed remaining exact) position bounded progress))))

collection : ∀ {Value} control (child : Flow.Parser Value) → (∀ input → Normal (Flow.Productive.result (child input))) →
  ∀ input → Normal (Collection.run control child input)
collection control child normal input = loop control child normal (length input) true input ≤-refl

container : ∀ {Value Output} (wrap : Value → Output) byte rest result finish → Normal result →
  Normal (Flow.Productive.result (Tree.container wrap byte rest result finish))
container wrap byte rest result finish normal = prefix (F.cursor (byte ∷ []) rest refl) _
  (map wrap (Flow.finalize result finish) (finalize result finish normal))

mutual
  value : ∀ allowance input → Normal (Flow.Productive.result (T.value allowance input))
  value allowance input = whitespace input (T.dispatch allowance) (dispatch allowance)

  dispatch : ∀ allowance input → Normal (Flow.Productive.result (T.dispatch allowance input))
  dispatch allowance [] = tt
  dispatch allowance input@(byte ∷ rest) with Tree.classify byte
  ... | Tree.nullToken = literal _ byte ((# 117) ∷ (# 108) ∷ (# 108) ∷ []) rest
  ... | Tree.trueToken = literal _ byte ((# 114) ∷ (# 117) ∷ (# 101) ∷ []) rest
  ... | Tree.falseToken = literal _ byte ((# 97) ∷ (# 108) ∷ (# 115) ∷ (# 101) ∷ []) rest
  ... | Tree.numberToken = productiveMap Bounds.numericValue (N.number input) (number input)
  ... | Tree.stringToken = productiveMap _ (Atoms.string input) (string input)
  ... | Tree.invalidToken = tt
  ... | Tree.arrayToken with allowance
  ...   | zero = tt
  ...   | suc remaining = container Bounds.arrayValue byte rest _ Controls.arrayEnd
    (collection Collection.arrayControl (T.value remaining) (value remaining) rest)
  dispatch allowance input@(byte ∷ rest) | Tree.objectToken with allowance
  ... | zero = tt
  ... | suc remaining = container Bounds.objectValue byte rest _ Controls.objectEnd
    (collection Collection.objectControl (Atoms.member (T.value remaining)) (member (T.value remaining) (value remaining)) rest)

boundedDocument : ∀ input → Normal (Flow.Productive.result (T.boundedDocument input))
boundedDocument input = productiveBind (T.value 127 input) _ (value 127 input) λ tree rest →
  map (λ unit → tree) (Flow.lift (Controls.skipWhitespace rest T.endAt)) tt

decodedDocument : ∀ input → Normal (Flow.Productive.result (D.read input))
decodedDocument input = productiveMap Decode.build (T.boundedDocument input) (boundedDocument input)

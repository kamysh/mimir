{-# OPTIONS --safe #-}
-- Every RFC 8259 number is accepted by the ignored-number scanner, regardless
-- of significand/exponent magnitude. JSON-delimited suffixes are preserved.
module Mimir.JsonIgnoredNumberComplete where

open import Data.Char using (Char; _≟_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Mimir.Text using (Text)
import Mimir.JsonIgnoredNumber as N
import Mimir.JsonNumber as G
import Mimir.JsonNumberSuffix as Suffix
import Mimir.DecimalLexer as Digits
import Mimir.Unsigned as D
module C = N.C

data Succeeded {input : Text} (suffix : Text) : C.Result ⊤ input → Set where
  success : ∀ consumed exact → Succeeded suffix (C.success tt consumed suffix exact)

prepend : ∀ prefix {input suffix} {result : C.Result ⊤ input} → Succeeded suffix result →
  Succeeded suffix (C.prefix prefix result)
prepend prefix (success consumed exact) = success _ _

reframe : ∀ {input source suffix} (exact : input ≡ source) {result : C.Result ⊤ source} →
  Succeeded suffix result → Succeeded suffix (C.reframe exact result)
reframe refl succeeded = succeeded

digitsComplete : ∀ next digits rest suffix → Digits.Stopped rest → Succeeded suffix (next rest) →
  Succeeded suffix (N.digits next (map D.character digits ++ rest))
digitsComplete next digits rest suffix stopped succeeded
  with Digits.take (map D.character digits ++ rest) | Digits.complete digits rest stopped
... | Digits.run scanned remaining exact terminal | refl , refl = reframe exact (prepend (map D.character digits) succeeded)

exponentFirstComplete : ∀ head tail rest → Suffix.Terminal rest →
  Succeeded rest (N.exponentFirst (G.spellDigits (head , tail) ++ rest))
exponentFirstComplete head tail rest terminal rewrite Digits.classifyComplete head = prepend (D.character head ∷ []) (digitsComplete N.finish tail rest rest (Suffix.stopped rest terminal) (success [] refl))

exponentSignComplete : ∀ sign head tail rest → Suffix.Terminal rest →
  Succeeded rest (N.exponentSign (G.spellExponentSign sign ++ (G.spellDigits (head , tail) ++ rest)))
exponentSignComplete G.implicit head tail rest terminal with D.character head ≟ '+'
... | yes same = ⊥-elim (D.digitNotPlus head same)
... | no notPlus with D.character head ≟ '-'
...   | yes same = ⊥-elim (D.digitNotMinus head same)
...   | no notMinus = exponentFirstComplete head tail rest terminal
exponentSignComplete G.plus head tail rest terminal = prepend ('+' ∷ []) (exponentFirstComplete head tail rest terminal)
exponentSignComplete G.minus head tail rest terminal = prepend ('-' ∷ []) (exponentFirstComplete head tail rest terminal)

afterFractionTerminal : ∀ rest → Suffix.Terminal rest → Succeeded rest (N.afterFraction rest)
afterFractionTerminal [] terminal = success [] refl
afterFractionTerminal (char ∷ rest) Suffix.space = success [] refl
afterFractionTerminal (char ∷ rest) Suffix.horizontalTab = success [] refl
afterFractionTerminal (char ∷ rest) Suffix.lineFeed = success [] refl
afterFractionTerminal (char ∷ rest) Suffix.carriageReturn = success [] refl
afterFractionTerminal (char ∷ rest) Suffix.comma = success [] refl
afterFractionTerminal (char ∷ rest) Suffix.arrayEnd = success [] refl
afterFractionTerminal (char ∷ rest) Suffix.objectEnd = success [] refl

afterFractionComplete : ∀ expo rest → Suffix.Terminal rest →
  Succeeded rest (N.afterFraction (G.spellExponent expo ++ rest))
afterFractionComplete G.absent rest terminal = afterFractionTerminal rest terminal
afterFractionComplete (G.exponent G.lower sign (head , tail)) rest terminal
  rewrite ++-assoc (G.spellExponentSign sign) (G.spellDigits (head , tail)) rest = prepend ('e' ∷ []) (exponentSignComplete sign head tail rest terminal)
afterFractionComplete (G.exponent G.upper sign (head , tail)) rest terminal
  rewrite ++-assoc (G.spellExponentSign sign) (G.spellDigits (head , tail)) rest = prepend ('E' ∷ []) (exponentSignComplete sign head tail rest terminal)

fractionComplete : ∀ head tail expo rest → Suffix.Terminal rest →
  Succeeded rest (N.fraction (G.spellDigits (head , tail) ++ (G.spellExponent expo ++ rest)))
fractionComplete head tail expo rest terminal
  with Digits.take (G.spellDigits (head , tail) ++ (G.spellExponent expo ++ rest)) |
    Digits.complete (head ∷ tail) (G.spellExponent expo ++ rest) (Suffix.exponentStopped expo rest terminal)
... | Digits.run scanned remaining exact stopped | refl , refl = reframe exact (prepend (D.character head ∷ map D.character tail) (afterFractionComplete expo rest terminal))

afterIntegerTerminal : ∀ rest → Suffix.Terminal rest → Succeeded rest (N.afterInteger rest)
afterIntegerTerminal [] terminal = success [] refl
afterIntegerTerminal (char ∷ rest) Suffix.space = success [] refl
afterIntegerTerminal (char ∷ rest) Suffix.horizontalTab = success [] refl
afterIntegerTerminal (char ∷ rest) Suffix.lineFeed = success [] refl
afterIntegerTerminal (char ∷ rest) Suffix.carriageReturn = success [] refl
afterIntegerTerminal (char ∷ rest) Suffix.comma = success [] refl
afterIntegerTerminal (char ∷ rest) Suffix.arrayEnd = success [] refl
afterIntegerTerminal (char ∷ rest) Suffix.objectEnd = success [] refl

afterIntegerComplete : ∀ frac expo rest → Suffix.Terminal rest →
  Succeeded rest (N.afterInteger (G.spellFraction frac ++ (G.spellExponent expo ++ rest)))
afterIntegerComplete G.absent G.absent rest terminal = afterIntegerTerminal rest terminal
afterIntegerComplete G.absent expo@(G.exponent G.lower sign digits) rest terminal = afterFractionComplete expo rest terminal
afterIntegerComplete G.absent expo@(G.exponent G.upper sign digits) rest terminal = afterFractionComplete expo rest terminal
afterIntegerComplete (G.fraction (head , tail)) expo rest terminal = prepend ('.' ∷ []) (fractionComplete head tail expo rest terminal)

afterZeroStopped : ∀ input → Digits.Stopped input → N.afterZero input ≡ N.afterInteger input
afterZeroStopped [] stopped = refl
afterZeroStopped (char ∷ input) stopped with Digits.classify char
... | yes (digit , same) = ⊥-elim (stopped digit same)
... | no notDigit = refl

afterZeroComplete : ∀ frac expo rest → Suffix.Terminal rest →
  Succeeded rest (N.afterZero (G.spellFraction frac ++ (G.spellExponent expo ++ rest)))
afterZeroComplete frac expo rest terminal = subst (Succeeded rest) (sym (afterZeroStopped _ (Suffix.fractionStopped frac expo rest terminal))) (afterIntegerComplete frac expo rest terminal)

integerComplete : ∀ whole frac expo rest → Suffix.Terminal rest →
  Succeeded rest (N.integer (G.spellWhole whole ++ (G.spellFraction frac ++ (G.spellExponent expo ++ rest))))
integerComplete G.zero frac expo rest terminal = prepend ('0' ∷ []) (afterZeroComplete frac expo rest terminal)
integerComplete (G.nonzero head notZero tail) frac expo rest terminal with D.character head ≟ '0'
... | yes same = ⊥-elim (notZero (D.zeroOnly head same))
... | no checked rewrite Digits.classifyComplete head = prepend (D.character head ∷ []) (digitsComplete N.afterInteger tail (G.spellFraction frac ++ (G.spellExponent expo ++ rest)) rest (Suffix.fractionStopped frac expo rest terminal) (afterIntegerComplete frac expo rest terminal))

readComplete : ∀ form rest → Suffix.Terminal rest → Succeeded rest (N.read (G.spell form ++ rest))
readComplete (G.minus , whole , frac , expo) rest terminal
  rewrite ++-assoc (G.spellWhole whole) (G.spellFraction frac ++ G.spellExponent expo) rest |
    ++-assoc (G.spellFraction frac) (G.spellExponent expo) rest = prepend ('-' ∷ []) (integerComplete whole frac expo rest terminal)
readComplete (G.unsigned , G.zero , frac , expo) rest terminal
  rewrite ++-assoc (G.spellFraction frac) (G.spellExponent expo) rest = integerComplete G.zero frac expo rest terminal
readComplete (G.unsigned , G.nonzero head notZero tail , frac , expo) rest terminal
  rewrite ++-assoc (map D.character tail) (G.spellFraction frac ++ G.spellExponent expo) rest |
    ++-assoc (G.spellFraction frac) (G.spellExponent expo) rest with D.character head ≟ '-'
... | yes same = ⊥-elim (D.digitNotMinus head same)
... | no notMinus = integerComplete (G.nonzero head notZero tail) frac expo rest terminal

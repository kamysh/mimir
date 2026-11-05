{-# OPTIONS --safe #-}
-- serde_json's container/token control protocol for an in-memory byte source.
-- Finalizers are separate because they also run after visitor parse failure.
module Mimir.JsonControls where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (#_; _≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.NumericTokens using (Position; current; peek)
import Mimir.JsonStringParser as Strings
import Mimir.NumericTokens as Numeric
import Mimir.JsonWhitespace as White
import Mimir.SequenceCursor as Cursor

data Reason : Set where
  eofValue eofList eofObject expectedIdent expectedValue expectedColon : Reason
  expectedListCommaOrEnd expectedObjectCommaOrEnd keyString trailingComma trailingCharacters recursionLimit : Reason
  numericError : Numeric.Reason → Reason
  stringError : Strings.Code → Reason

Code = Reason × Position
module C = Cursor.Over Byte Code

skipWhitespace : ∀ {Value} input → (∀ rest → C.Result Value rest) → C.Result Value input
skipWhitespace input next with White.take input
... | White.run prefix spaces rest exact stopped = C.reframe exact (C.prefix prefix (next rest))

identifier : (expected : List Byte) → ∀ input → C.Result ⊤ input
identifier [] input = C.done tt input
identifier (wanted ∷ expected) [] = C.fail (eofValue , current) []
identifier (wanted ∷ expected) (byte ∷ input) with byte ≟ wanted
... | no mismatch = C.prefix (byte ∷ []) (C.fail (expectedIdent , current) input)
... | yes same = C.prefix (byte ∷ []) (identifier expected input)

identifierComplete : ∀ expected rest → identifier expected (expected ++ rest) ≡ C.success tt expected rest refl
identifierComplete [] rest = refl
identifierComplete (byte ∷ expected) rest with byte ≟ byte
... | no impossible = ⊥-elim (impossible refl)
... | yes same rewrite identifierComplete expected rest = refl

colonAt : ∀ input → C.Result ⊤ input
colonAt [] = C.fail (eofObject , peek) []
colonAt input@(byte ∷ rest) with byte ≟ (# 58)
... | yes colon = C.prefix (byte ∷ []) (C.done tt rest)
... | no missing = C.fail (expectedColon , peek) input

colon : ∀ input → C.Result ⊤ input
colon input = skipWhitespace input colonAt

arrayAfterCommaEnd : ∀ input → C.Result ⊤ input
arrayAfterCommaEnd [] = C.fail (trailingCharacters , peek) []
arrayAfterCommaEnd input@(byte ∷ rest) with byte ≟ (# 93)
... | yes closed = C.fail (trailingComma , peek) input
... | no other = C.fail (trailingCharacters , peek) input

arrayEndAt : ∀ input → C.Result ⊤ input
arrayEndAt [] = C.fail (eofList , peek) []
arrayEndAt input@(byte ∷ rest) with byte ≟ (# 93)
... | yes closed = C.prefix (byte ∷ []) (C.done tt rest)
... | no notClosed with byte ≟ (# 44)
...   | yes comma = C.prefix (byte ∷ []) (skipWhitespace rest arrayAfterCommaEnd)
...   | no other = C.fail (trailingCharacters , peek) input

arrayEnd : ∀ input → C.Result ⊤ input
arrayEnd input = skipWhitespace input arrayEndAt

objectEndAt : ∀ input → C.Result ⊤ input
objectEndAt [] = C.fail (eofObject , peek) []
objectEndAt input@(byte ∷ rest) with byte ≟ (# 125)
... | yes closed = C.prefix (byte ∷ []) (C.done tt rest)
... | no notClosed with byte ≟ (# 44)
...   | yes comma = C.fail (trailingComma , peek) input
...   | no other = C.fail (trailingCharacters , peek) input

objectEnd : ∀ input → C.Result ⊤ input
objectEnd input = skipWhitespace input objectEndAt

arrayAfterComma : ∀ input → C.Result Bool input
arrayAfterComma [] = C.fail (eofValue , peek) []
arrayAfterComma input@(byte ∷ rest) with byte ≟ (# 93)
... | yes trailing = C.fail (trailingComma , peek) input
... | no next = C.done true input

arrayNextAt : Bool → ∀ input → C.Result Bool input
arrayNextAt first [] = C.fail (eofList , peek) []
arrayNextAt first input@(byte ∷ rest) with byte ≟ (# 93)
... | yes closed = C.done false input
arrayNextAt true input@(byte ∷ rest) | no next = C.done true input
arrayNextAt false input@(byte ∷ rest) | no notClosed with byte ≟ (# 44)
... | yes comma = C.prefix (byte ∷ []) (skipWhitespace rest arrayAfterComma)
... | no missing = C.fail (expectedListCommaOrEnd , peek) input

arrayNext : Bool → ∀ input → C.Result Bool input
arrayNext first input = skipWhitespace input (arrayNextAt first)

objectAfterComma : ∀ input → C.Result Bool input
objectAfterComma [] = C.fail (eofValue , peek) []
objectAfterComma input@(byte ∷ rest) with byte ≟ (# 34)
... | yes quoteByte = C.done true input
... | no notQuote with byte ≟ (# 125)
...   | yes trailing = C.fail (trailingComma , peek) input
...   | no other = C.fail (keyString , peek) input

objectFirstKey : ∀ input → C.Result Bool input
objectFirstKey [] = C.fail (eofObject , peek) []
objectFirstKey input@(byte ∷ rest) with byte ≟ (# 34)
... | yes quoteByte = C.done true input
... | no other = C.fail (keyString , peek) input

objectNextAt : Bool → ∀ input → C.Result Bool input
objectNextAt first [] = C.fail (eofObject , peek) []
objectNextAt first input@(byte ∷ rest) with byte ≟ (# 125)
... | yes closed = C.done false input
objectNextAt true input@(byte ∷ rest) | no next = objectFirstKey input
objectNextAt false input@(byte ∷ rest) | no notClosed with byte ≟ (# 44)
... | yes comma = C.prefix (byte ∷ []) (skipWhitespace rest objectAfterComma)
... | no missing = C.fail (expectedObjectCommaOrEnd , peek) input

objectNext : Bool → ∀ input → C.Result Bool input
objectNext first input = skipWhitespace input (objectNextAt first)

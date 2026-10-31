{-# OPTIONS --safe #-}
-- Every token/container-control failure has a renderable syntax reason.
module Mimir.JsonControlDiagnostics where

open import Data.Bool using (true; false)
open import Data.Fin using (#_; _≟_)
open import Data.List using ([]; _∷_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
import Mimir.JsonControls as C
import Mimir.JsonWhitespace as White
open import Mimir.JsonDiagnosticCode using (Atomic; atomicPrefix; atomicReframe)

whitespace : ∀ {Value} input (next : ∀ rest → C.C.Result Value rest) →
  (∀ rest → Atomic (next rest)) → Atomic (C.skipWhitespace input next)
whitespace input next checked with White.take input
... | White.run consumed spaces remaining exact stopped =
  atomicReframe exact (C.C.prefix consumed (next remaining)) (atomicPrefix consumed (next remaining) (checked remaining))

identifier : ∀ expected input → Atomic (C.identifier expected input)
identifier [] input = tt
identifier (wanted ∷ expected) [] = λ ()
identifier (wanted ∷ expected) (byte ∷ input) with byte ≟ wanted
... | no mismatch = λ ()
... | yes same = atomicPrefix (byte ∷ []) (C.identifier expected input) (identifier expected input)

colonAt : ∀ input → Atomic (C.colonAt input)
colonAt [] = λ ()
colonAt (byte ∷ rest) with byte ≟ (# 58)
... | yes colon = tt
... | no missing = λ ()

colon : ∀ input → Atomic (C.colon input)
colon input = whitespace input C.colonAt colonAt

arrayAfterCommaEnd : ∀ input → Atomic (C.arrayAfterCommaEnd input)
arrayAfterCommaEnd [] = λ ()
arrayAfterCommaEnd (byte ∷ rest) with byte ≟ (# 93)
... | yes closed = λ ()
... | no other = λ ()

arrayEndAt : ∀ input → Atomic (C.arrayEndAt input)
arrayEndAt [] = λ ()
arrayEndAt (byte ∷ rest) with byte ≟ (# 93)
... | yes closed = tt
... | no notClosed with byte ≟ (# 44)
...   | yes comma = atomicPrefix (byte ∷ []) (C.skipWhitespace rest C.arrayAfterCommaEnd)
  (whitespace rest C.arrayAfterCommaEnd arrayAfterCommaEnd)
...   | no other = λ ()

arrayEnd : ∀ input → Atomic (C.arrayEnd input)
arrayEnd input = whitespace input C.arrayEndAt arrayEndAt

objectEndAt : ∀ input → Atomic (C.objectEndAt input)
objectEndAt [] = λ ()
objectEndAt (byte ∷ rest) with byte ≟ (# 125)
... | yes closed = tt
... | no notClosed with byte ≟ (# 44)
...   | yes comma = λ ()
...   | no other = λ ()

objectEnd : ∀ input → Atomic (C.objectEnd input)
objectEnd input = whitespace input C.objectEndAt objectEndAt

arrayAfterComma : ∀ input → Atomic (C.arrayAfterComma input)
arrayAfterComma [] = λ ()
arrayAfterComma (byte ∷ rest) with byte ≟ (# 93)
... | yes trailing = λ ()
... | no next = tt

arrayNextAt : ∀ first input → Atomic (C.arrayNextAt first input)
arrayNextAt first [] = λ ()
arrayNextAt first (byte ∷ rest) with byte ≟ (# 93)
... | yes closed = tt
arrayNextAt true (byte ∷ rest) | no next = tt
arrayNextAt false (byte ∷ rest) | no notClosed with byte ≟ (# 44)
... | yes comma = atomicPrefix (byte ∷ []) (C.skipWhitespace rest C.arrayAfterComma)
  (whitespace rest C.arrayAfterComma arrayAfterComma)
... | no missing = λ ()

arrayNext : ∀ first input → Atomic (C.arrayNext first input)
arrayNext first input = whitespace input (C.arrayNextAt first) (arrayNextAt first)

objectAfterComma : ∀ input → Atomic (C.objectAfterComma input)
objectAfterComma [] = λ ()
objectAfterComma (byte ∷ rest) with byte ≟ (# 34)
... | yes quoteByte = tt
... | no notQuote with byte ≟ (# 125)
...   | yes trailing = λ ()
...   | no other = λ ()

objectFirstKey : ∀ input → Atomic (C.objectFirstKey input)
objectFirstKey [] = λ ()
objectFirstKey (byte ∷ rest) with byte ≟ (# 34)
... | yes quoteByte = tt
... | no other = λ ()

objectNextAt : ∀ first input → Atomic (C.objectNextAt first input)
objectNextAt first [] = λ ()
objectNextAt first input@(byte ∷ rest) with byte ≟ (# 125)
... | yes closed = tt
objectNextAt true input@(byte ∷ rest) | no next = objectFirstKey input
objectNextAt false input@(byte ∷ rest) | no notClosed with byte ≟ (# 44)
... | yes comma = atomicPrefix (byte ∷ []) (C.skipWhitespace rest C.objectAfterComma)
  (whitespace rest C.objectAfterComma objectAfterComma)
... | no missing = λ ()

objectNext : ∀ first input → Atomic (C.objectNext first input)
objectNext first input = whitespace input (C.objectNextAt first) (objectNextAt first)

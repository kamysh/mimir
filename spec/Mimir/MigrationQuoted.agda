{-# OPTIONS --safe #-}
-- Winnow quoted_char in Kryzhen is not a JSON escape parser. It decodes
-- backslash-quote and backslash-backslash; other backslashes remain literal.
-- Newlines and other characters except unescaped quotes are admitted.
module Mimir.MigrationQuoted where

open import Data.Char using (Char)
import Data.Char.Properties as Char
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Mimir.Text using (Text)

data Body : Text → Text → Text → Set where
  closed : ∀ rest → Body ('"' ∷ rest) [] rest
  escapedQuote : ∀ {input value rest} → Body input value rest →
    Body ('\\' ∷ '"' ∷ input) ('"' ∷ value) rest
  escapedSlash : ∀ {input value rest} → Body input value rest →
    Body ('\\' ∷ '\\' ∷ input) ('\\' ∷ value) rest
  ordinary : ∀ {char input value rest} → char ≢ '"' → char ≢ '\\' → Body input value rest →
    Body (char ∷ input) (char ∷ value) rest
  literalSlash : ∀ {next input value rest} → next ≢ '"' → next ≢ '\\' → Body (next ∷ input) value rest →
    Body ('\\' ∷ next ∷ input) ('\\' ∷ value) rest

record Parsed (input : Text) : Set where
  constructor parsed
  field value rest : Text; grammar : Body input value rest

extend : ∀ {input tail} char →
  (∀ {value rest} → Body tail value rest → Body input (char ∷ value) rest) →
  Maybe (Parsed tail) → Maybe (Parsed input)
extend char prepend nothing = nothing
extend char prepend (just (parsed value rest grammar)) = just (parsed (char ∷ value) rest (prepend grammar))

mutual
  scan : ∀ input → Maybe (Parsed input)
  scan [] = nothing
  scan (char ∷ input) with char Char.≟ '"'
  ... | yes refl = just (parsed [] input (closed input))
  ... | no notQuote with char Char.≟ '\\'
  ...   | no notSlash = extend char (ordinary notQuote notSlash) (scan input)
  ...   | yes refl = afterSlash input

  afterSlash : ∀ input → Maybe (Parsed ('\\' ∷ input))
  afterSlash [] = nothing
  afterSlash (next ∷ tail) with next Char.≟ '"'
  ... | yes refl = extend '"' escapedQuote (scan tail)
  ... | no nextNotQuote with next Char.≟ '\\'
  ...   | yes refl = extend '\\' escapedSlash (scan tail)
  ...   | no nextNotSlash = extend '\\' (literalSlash nextNotQuote nextNotSlash)
    (extend next (ordinary nextNotQuote nextNotSlash) (scan tail))

data Succeeds {A : Set} : Maybe A → Set where success : ∀ value → Succeeds (just value)

extendSucceeds : ∀ {input tail} char
  (prepend : ∀ {value rest} → Body tail value rest → Body input (char ∷ value) rest)
  parsedTail → Succeeds parsedTail → Succeeds (extend char prepend parsedTail)
extendSucceeds char prepend (just (parsed value rest grammar)) (success _) = success _

complete : ∀ {input value rest} → Body input value rest → Succeeds (scan input)
complete (closed rest) = success _
complete (escapedQuote tail) = extendSucceeds '"' escapedQuote _ (complete tail)
complete (escapedSlash tail) = extendSucceeds '\\' escapedSlash _ (complete tail)
complete (ordinary {char} notQuote notSlash tail) with char Char.≟ '"'
... | yes same = ⊥-elim (notQuote same)
... | no otherQuote with char Char.≟ '\\'
...   | yes same = ⊥-elim (notSlash same)
...   | no otherSlash = extendSucceeds char (ordinary otherQuote otherSlash) _ (complete tail)
complete (literalSlash notQuote notSlash (closed _)) = ⊥-elim (notQuote refl)
complete (literalSlash notQuote notSlash (escapedQuote tail)) = ⊥-elim (notSlash refl)
complete (literalSlash notQuote notSlash (escapedSlash tail)) = ⊥-elim (notSlash refl)
complete (literalSlash notQuote notSlash (literalSlash _ _ tail)) = ⊥-elim (notSlash refl)
complete (literalSlash {next} notQuote notSlash (ordinary _ _ tail)) with next Char.≟ '"'
... | yes same = ⊥-elim (notQuote same)
... | no otherQuote with next Char.≟ '\\'
...   | yes same = ⊥-elim (notSlash same)
...   | no otherSlash = extendSucceeds '\\' (literalSlash otherQuote otherSlash) _
  (extendSucceeds next (ordinary otherQuote otherSlash) _ (complete tail))

erase : ∀ {input} → Maybe (Parsed input) → Maybe (Text × Text)
erase nothing = nothing
erase (just (parsed value rest grammar)) = just (value , rest)

eraseSucceeds : ∀ {input} (result : Maybe (Parsed input)) → Succeeds result → Succeeds (erase result)
eraseSucceeds (just (parsed value rest grammar)) (success _) = success _

prefixEquality : ∀ (char : Char) {first second rest remainder : Text} → first ≡ second × rest ≡ remainder →
  (char ∷ first) ≡ (char ∷ second) × rest ≡ remainder
prefixEquality char (same , tail) = cong (char ∷_) same , tail

unique : ∀ {input first second rest remainder} →
  Body input first rest → Body input second remainder → first ≡ second × rest ≡ remainder
unique (closed _) (closed _) = refl , refl
unique (closed _) (ordinary notQuote notSlash tail) = ⊥-elim (notQuote refl)
unique (escapedQuote first) (escapedQuote second) = prefixEquality '"' (unique first second)
unique (escapedQuote first) (ordinary notQuote notSlash second) = ⊥-elim (notSlash refl)
unique (escapedQuote first) (literalSlash notQuote notSlash second) = ⊥-elim (notQuote refl)
unique (escapedSlash first) (escapedSlash second) = prefixEquality '\\' (unique first second)
unique (escapedSlash first) (ordinary notQuote notSlash second) = ⊥-elim (notSlash refl)
unique (escapedSlash first) (literalSlash notQuote notSlash second) = ⊥-elim (notSlash refl)
unique (ordinary notQuote notSlash first) (closed _) = ⊥-elim (notQuote refl)
unique (ordinary notQuote notSlash first) (escapedQuote second) = ⊥-elim (notSlash refl)
unique (ordinary notQuote notSlash first) (escapedSlash second) = ⊥-elim (notSlash refl)
unique (ordinary {char} notQuote notSlash first) (ordinary otherQuote otherSlash second) =
  prefixEquality char (unique first second)
unique (ordinary notQuote notSlash first) (literalSlash otherQuote otherSlash second) = ⊥-elim (notSlash refl)
unique (literalSlash notQuote notSlash first) (escapedQuote second) = ⊥-elim (notQuote refl)
unique (literalSlash notQuote notSlash first) (escapedSlash second) = ⊥-elim (notSlash refl)
unique (literalSlash notQuote notSlash first) (ordinary otherQuote otherSlash second) = ⊥-elim (otherSlash refl)
unique (literalSlash notQuote notSlash first) (literalSlash otherQuote otherSlash second) =
  prefixEquality '\\' (unique first second)

data Quoted : Text → Text → Text → Set where
  quoted : ∀ {input value rest} → Body input value rest → Quoted ('"' ∷ input) value rest

read : Text → Maybe (Text × Text)
read [] = nothing
read (char ∷ input) with char Char.≟ '"'
... | yes _ = erase (scan input)
... | no _ = nothing

readComplete : ∀ {input value rest} → Quoted input value rest → Succeeds (read input)
readComplete (quoted {input} grammar) = eraseSucceeds (scan input) (complete grammar)

readSound : ∀ input value rest → read input ≡ just (value , rest) → Quoted input value rest
readSound [] value rest ()
readSound (char ∷ input) value rest accepted with char Char.≟ '"'
... | no other with accepted
...   | ()
readSound (char ∷ input) value rest accepted | yes refl with scan input
...   | nothing with accepted
...     | ()
readSound (char ∷ input) value rest accepted | yes refl | just (parsed actual remainder grammar) with accepted
...     | refl = quoted grammar

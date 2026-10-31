{-# OPTIONS --safe #-}
-- PostgreSQL password-file language and source selection.  The parser operates
-- on Unicode scalar values, after the file's fallible UTF-8 decoding.  It does
-- not silently treat a read failure as a successful empty password.
module Mimir.Password where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Char using (Char; _≟_)
open import Data.List using (List; []; _∷_; reverse)
open import Data.List.Properties using (≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

Text = List Char

record Field : Set where
  constructor scanned
  field
    value : Text
    remaining : Maybe Text
open Field public

-- This relation is the grammar, independently of the executable parser.
data Scans : Text → Field → Set where
  end : Scans [] (scanned [] nothing)
  separator : ∀ xs → Scans (':' ∷ xs) (scanned [] (just xs))
  trailingEscape : Scans ('\\' ∷ []) (scanned ('\\' ∷ []) nothing)
  escape : ∀ c xs v r → Scans xs (scanned v r) →
    Scans ('\\' ∷ c ∷ xs) (scanned (c ∷ v) r)
  literal : ∀ c xs v r → c ≢ ':' → c ≢ '\\' →
    Scans xs (scanned v r) → Scans (c ∷ xs) (scanned (c ∷ v) r)

record Parsed (input : Text) : Set where
  constructor parsed
  field
    result : Field
    sound : Scans input result
open Parsed public

parseField : (input : Text) → Parsed input
parseField [] = parsed (scanned [] nothing) end
parseField (c ∷ xs) with c ≟ ':'
... | yes refl = parsed (scanned [] (just xs)) (separator xs)
... | no notColon with c ≟ '\\'
...   | yes refl with xs
...     | [] = parsed (scanned ('\\' ∷ []) nothing) trailingEscape
...     | d ∷ ds with parseField ds
...       | parsed (scanned v r) proof =
            parsed (scanned (d ∷ v) r) (escape d ds v r proof)
parseField (c ∷ xs) | no notColon | no notSlash with parseField xs
... | parsed (scanned v r) proof =
      parsed (scanned (c ∷ v) r) (literal c xs v r notColon notSlash proof)

grammarDeterministic : ∀ {input first second} →
  Scans input first → Scans input second → first ≡ second
grammarDeterministic end end = refl
grammarDeterministic (separator xs) (separator .xs) = refl
grammarDeterministic (separator xs) (literal .':' .xs v r notColon notSlash p) =
  ⊥-elim (notColon refl)
grammarDeterministic trailingEscape trailingEscape = refl
grammarDeterministic trailingEscape (literal .'\\' .[] v r notColon notSlash p) =
  ⊥-elim (notSlash refl)
grammarDeterministic (escape c xs v r p) (escape .c .xs w s q) =
  cong (λ f → scanned (c ∷ value f) (remaining f)) (grammarDeterministic p q)
grammarDeterministic (escape c xs v r p)
  (literal .'\\' .(c ∷ xs) w s notColon notSlash q) = ⊥-elim (notSlash refl)
grammarDeterministic (literal .':' xs v r notColon notSlash p) (separator .xs) =
  ⊥-elim (notColon refl)
grammarDeterministic (literal .'\\' .[] v r notColon notSlash p) trailingEscape =
  ⊥-elim (notSlash refl)
grammarDeterministic (literal .'\\' .(c ∷ xs) v r notColon notSlash p)
  (escape c xs w s q) = ⊥-elim (notSlash refl)
grammarDeterministic (literal c xs v r nc ns p) (literal .c .xs w s mc ms q) =
  cong (λ f → scanned (c ∷ value f) (remaining f)) (grammarDeterministic p q)

parserComplete : ∀ input expected → Scans input expected →
  result (parseField input) ≡ expected
parserComplete input expected proof = grammarDeterministic (sound (parseField input)) proof

-- A wildcard is recognized before escape decoding, and only when it occupies
-- the entire raw field.  Thus an escaped '*' never becomes a wildcard.
wildcard : Text → Bool
wildcard [] = false
wildcard (c ∷ []) = false
wildcard (c ∷ d ∷ xs) with c ≟ '*' | d ≟ ':'
... | yes _ | yes _ = true
... | _ | _ = false

matches : Text → Text → Field → Bool
matches raw expected f with wildcard raw
... | true = true
... | false with ≡-dec _≟_ (value f) expected
...   | yes _ = true
...   | no _ = false

-- Exactly one separating colon is required after each selector.  The final
-- password uses the same escape grammar and ignores any following field,
-- matching the current PostgreSQL-compatible reader's behavior.
selectors : List Text → Text → Maybe Text
selectors [] raw = just (value (result (parseField raw)))
selectors (expected ∷ rest) raw with result (parseField raw)
... | scanned v nothing = nothing
... | f@(scanned v (just tail)) with matches raw expected f
...   | true = selectors rest tail
...   | false = nothing

stripLeadingCR : Text → Text
stripLeadingCR [] = []
stripLeadingCR (c ∷ cs) with c ≟ '\r'
... | yes _ = stripLeadingCR cs
... | no _ = c ∷ cs

trimCR : Text → Text
trimCR xs = reverse (stripLeadingCR (reverse xs))

line : List Text → Text → Maybe Text
line expected raw with trimCR raw
... | [] = nothing
... | c ∷ cs with c ≟ '#'
...   | yes _ = nothing
...   | no _ = selectors expected (c ∷ cs)

splitLines : Text → List Text
splitLines [] = [] ∷ []
splitLines (c ∷ cs) with c ≟ '\n' | splitLines cs
... | yes _ | rest = [] ∷ rest
... | no _ | [] = (c ∷ []) ∷ []
... | no _ | first ∷ rest = (c ∷ first) ∷ rest

-- The result includes a proof that every preceding line was inapplicable.
data FirstMatch (expected : List Text) : List Text → Text → Set where
  here : ∀ raw rest password → line expected raw ≡ just password →
    FirstMatch expected (raw ∷ rest) password
  later : ∀ raw rest password → line expected raw ≡ nothing →
    FirstMatch expected rest password → FirstMatch expected (raw ∷ rest) password

lookup : List Text → List Text → Maybe Text
lookup expected [] = nothing
lookup expected (raw ∷ rest) with line expected raw
... | just password = just password
... | nothing = lookup expected rest

firstMatchSound : ∀ expected rows password →
  lookup expected rows ≡ just password → FirstMatch expected rows password
firstMatchSound expected (raw ∷ rest) password eq with line expected raw in outcome
... | just found with eq
...   | refl = here raw rest password outcome
firstMatchSound expected (raw ∷ rest) password eq | nothing =
  later raw rest password outcome (firstMatchSound expected rest password eq)

firstMatchComplete : ∀ {expected rows password} → FirstMatch expected rows password →
  lookup expected rows ≡ just password
firstMatchComplete (here raw rest password eq) rewrite eq = refl
firstMatchComplete (later raw rest password eq proof) rewrite eq = firstMatchComplete proof

record Selectors : Set where
  constructor connection
  field host port database user : Text

lookupFile : Selectors → Text → Maybe Text
lookupFile (connection host port database user) content =
  lookup (host ∷ port ∷ database ∷ user ∷ []) (splitLines content)

-- Every external file outcome is represented. Permission denial is distinct
-- from no match internally even though both produce no password downstream.
data FileInput : Set where
  noPath metadataFailure notRegular insecurePermissions readFailure : FileInput
  readable : Text → FileInput

filePassword : Selectors → FileInput → Maybe Text
filePassword s (readable content) = lookupFile s content
filePassword s _ = nothing

nonempty : Maybe Text → Maybe Text
nonempty (just []) = nothing
nonempty other = other

resolve : Maybe Text → Maybe Text → Selectors → FileInput → Maybe Text
resolve (just configured) environment s input = just configured
resolve nothing environment s input with nonempty environment
... | just password = just password
... | nothing = filePassword s input

configuredPreserved : ∀ configured environment s input →
  resolve (just configured) environment s input ≡ just configured
configuredPreserved configured environment s input = refl

environmentPreserved : ∀ c cs s input →
  resolve nothing (just (c ∷ cs)) s input ≡ just (c ∷ cs)
environmentPreserved c cs s input = refl

emptyEnvironmentFallsBack : ∀ s input →
  resolve nothing (just []) s input ≡ filePassword s input
emptyEnvironmentFallsBack s input = refl

insecureFileIgnored : ∀ s → filePassword s insecurePermissions ≡ nothing
insecureFileIgnored s = refl

{-# OPTIONS --safe #-}
-- The MCP server's read_line boundary has no application byte limit. A final
-- nonempty line at EOF is delivered; an empty EOF ends the loop. Newline bytes
-- remain in the delivered line. UTF-8 failure is an I/O failure, not JSON input.
module Mimir.ReadLine where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Fin using (toℕ)
open import Data.Nat using (_≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)
open import Mimir.Bits using (Byte)
import Mimir.UTF8Text as UTF8
import Mimir.UTF8Packet as Packet
open import Data.Sum using (inj₁; inj₂)
import Data.Empty

NotLF : Byte → Set
NotLF byte = toℕ byte ≢ 10

data Boundary : List Byte → Set where
  newline : ∀ prefix last → All NotLF prefix → toℕ last ≡ 10 →
    Boundary (prefix ++ (last ∷ []))
  final : ∀ first rest → All NotLF (first ∷ rest) → Boundary (first ∷ rest)

record Line (input : List Byte) : Set where
  constructor line
  field
    bytes remainder : List Byte
    exact : input ≡ bytes ++ remainder
    boundary : Boundary bytes
    finalRemainder : (∀ {first rest} → bytes ≡ first ∷ rest →
      All NotLF bytes → remainder ≡ [])

-- A structural grammar records the first newline, including the final-line
-- case. It keeps EOF separate from a blank (newline-only) line.
data Split : List Byte → List Byte → List Byte → Set where
  atEOF : Split [] [] []
  atLF : ∀ byte rest → toℕ byte ≡ 10 → Split (byte ∷ rest) (byte ∷ []) rest
  beforeLF : ∀ byte input prefix rest → NotLF byte → Split input prefix rest →
    Split (byte ∷ input) (byte ∷ prefix) rest

record Scanned (input : List Byte) : Set where
  constructor scanned
  field bytes remainder : List Byte; meaning : Split input bytes remainder

scan : ∀ input → Scanned input
scan [] = scanned [] [] atEOF
scan (byte ∷ input) with toℕ byte ≟ 10
... | yes lfProof = scanned (byte ∷ []) input (atLF byte input lfProof)
... | no ordinary with scan input
...   | scanned prefix rest split = scanned (byte ∷ prefix) rest
    (beforeLF byte input prefix rest ordinary split)

exactSplit : ∀ {input prefix rest} → Split input prefix rest → input ≡ prefix ++ rest
exactSplit atEOF = refl
exactSplit (atLF byte rest lfProof) = refl
exactSplit (beforeLF byte input prefix rest ordinary split) = cong (byte ∷_) (exactSplit split)

onlyEOFIsEmpty : ∀ {input rest} → Split input [] rest → input ≡ [] × rest ≡ []
onlyEOFIsEmpty atEOF = refl , refl

noLFMeansEOF : ∀ {input prefix rest} → Split input prefix rest → All NotLF prefix → rest ≡ []
noLFMeansEOF atEOF ordinary = refl
noLFMeansEOF (atLF byte rest lfProof) (ordinary ∷ tail) = Data.Empty.⊥-elim (ordinary lfProof)
noLFMeansEOF (beforeLF byte input prefix rest ordinary split) (head ∷ tail) = noLFMeansEOF split tail

prependBoundary : ∀ byte prefix → NotLF byte → Boundary prefix → Boundary (byte ∷ prefix)
prependBoundary byte .(prefix ++ (last ∷ [])) ordinary (newline prefix last earlier end) =
  newline (byte ∷ prefix) last (ordinary ∷ earlier) end
prependBoundary byte .(first ∷ rest) ordinary (final first rest earlier) =
  final byte (first ∷ rest) (ordinary ∷ earlier)

boundaryOfNonempty : ∀ {input first prefix rest} → Split input (first ∷ prefix) rest → Boundary (first ∷ prefix)
boundaryOfNonempty (atLF byte rest end) = newline [] byte [] end
boundaryOfNonempty (beforeLF byte .[] .[] .[] ordinary atEOF) = final byte [] (ordinary ∷ [])
boundaryOfNonempty (beforeLF byte input .(next ∷ []) rest ordinary (atLF next rest end)) =
  newline (byte ∷ []) next (ordinary ∷ []) end
boundaryOfNonempty (beforeLF byte input .(next ∷ prefix) rest ordinary (beforeLF next following prefix rest nextOrdinary split)) =
  prependBoundary byte (next ∷ prefix) ordinary (boundaryOfNonempty (beforeLF next following prefix rest nextOrdinary split))

data Read (input : List Byte) : Set where
  eof : input ≡ [] → Read input
  success : (result : Line input) → UTF8.Decoded (Line.bytes result) → Read input
  invalidUTF8 : (result : Line input) → Packet.Error → Read input

decode : ∀ input → Read input
decode input with scan input
... | scanned [] rest meaning = eof (Data.Product.proj₁ (onlyEOFIsEmpty meaning))
... | scanned (first ∷ prefix) rest meaning with UTF8.decode (first ∷ prefix)
...   | inj₁ failure = invalidUTF8 result failure
  where result = line (first ∷ prefix) rest (exactSplit meaning) (boundaryOfNonempty meaning)
          (λ same ordinary → noLFMeansEOF meaning ordinary)
...   | inj₂ value = success result value
  where result = line (first ∷ prefix) rest (exactSplit meaning) (boundaryOfNonempty meaning)
          (λ same ordinary → noLFMeansEOF meaning ordinary)

scanConservesBytes : ∀ input → input ≡ Scanned.bytes (scan input) ++ Scanned.remainder (scan input)
scanConservesBytes input = exactSplit (Scanned.meaning (scan input))

scanComplete : ∀ {input prefix rest} → Split input prefix rest →
  Scanned.bytes (scan input) ≡ prefix × Scanned.remainder (scan input) ≡ rest
scanComplete atEOF = refl , refl
scanComplete (atLF byte rest end) with toℕ byte ≟ 10
... | yes proof = refl , refl
... | no ordinary = Data.Empty.⊥-elim (ordinary end)
scanComplete (beforeLF byte input prefix rest ordinary split) with toℕ byte ≟ 10
... | yes end = Data.Empty.⊥-elim (ordinary end)
... | no proof with scan input | scanComplete split
...   | scanned found remainder meaning | samePrefix , sameRest = cong (byte ∷_) samePrefix , sameRest

splitUnique : ∀ {input firstPrefix firstRest secondPrefix secondRest} →
  Split input firstPrefix firstRest → Split input secondPrefix secondRest →
  firstPrefix ≡ secondPrefix × firstRest ≡ secondRest
splitUnique first second =
  trans (Relation.Binary.PropositionalEquality.sym (Data.Product.proj₁ (scanComplete first)))
    (Data.Product.proj₁ (scanComplete second)) ,
  trans (Relation.Binary.PropositionalEquality.sym (Data.Product.proj₂ (scanComplete first)))
    (Data.Product.proj₂ (scanComplete second))

{-# OPTIONS --safe #-}
-- Every successful plain UUID parse has an independent grammar derivation.
-- Wrapper bytes, case alternatives and inner source boundaries stay explicit.
module Mimir.UUIDParseGrammar where

open import Data.Fin using (#_)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; _++_; take; drop; length)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Mimir.Bits using (Byte)
import Mimir.HexBytes as Hex
import Mimir.UUIDGroups as G
import Mimir.UUIDHyphenated as H
import Mimir.UUIDHyphenatedGrammar as Grammar
import Mimir.UUIDParse as P

record Regular (input : List Byte) (value : G.UUID) : Set where
  constructor regular
  field groups : G.Groups; meaning : Grammar.Read input groups []; exact : G.flatten groups ≡ value

data Prefix : List (Byte × Byte) → List Byte → List Byte → Set where
  done : ∀ rest → Prefix [] rest rest
  lower : ∀ small large byte expected input rest → byte ≡ small → Prefix expected input rest →
    Prefix ((small , large) ∷ expected) (byte ∷ input) rest
  upper : ∀ small large byte expected input rest → byte ≡ large → Prefix expected input rest →
    Prefix ((small , large) ∷ expected) (byte ∷ input) rest

data Accepted (input : List Byte) (value : G.UUID) : Set where
  simple : Hex.Pairs input value [] → Accepted input value
  hyphenated : Regular input value → Accepted input value
  braced : ∀ body → input ≡ (# 123) ∷ (body ++ ((# 125) ∷ [])) → Regular body value → Accepted input value
  urn : ∀ body → Prefix P.urnPrefix input body → Regular body value → Accepted input value

finishSound : ∀ input requested decoded value → P.finish input requested decoded ≡ P.accepted value → decoded ≡ just (value , [])
finishSound input requested nothing value ()
finishSound input requested (just (value , [])) .value refl = refl
finishSound input requested (just (value , byte ∷ rest)) output ()

decodeRegular : ∀ input value → H.decode input ≡ just (value , []) → Regular input value
decodeRegular input value observed with H.read input in parsed
... | nothing with observed
...   | ()
decodeRegular input .(G.flatten parts) refl | just (parts , []) = regular parts (Grammar.sound input parts [] parsed) refl

hyphenatedSizedSound : ∀ size input value → P.hyphenatedSized size input ≡ P.accepted value → Regular input value
hyphenatedSizedSound size input value observed with size ≟ 36
... | yes sized = decodeRegular input value (finishSound input P.hyphenated (H.decode input) value observed)
... | no wrongSize with observed
...   | ()

prefixSound : ∀ expected input rest → P.prefix expected input ≡ just rest → Prefix expected input rest
prefixSound [] input .input refl = done input
prefixSound (pair ∷ expected) [] rest ()
prefixSound ((small , large) ∷ expected) (byte ∷ input) rest observed with byte Fin.≟ small
... | yes same = lower small large byte expected input rest same (prefixSound expected input rest observed)
... | no notLower with byte Fin.≟ large
...   | yes same = upper small large byte expected input rest same (prefixSound expected input rest observed)
...   | no notUpper with observed
...     | ()

bracedSound : ∀ input value → P.braced input ≡ P.accepted value → Accepted input value
bracedSound [] value ()
bracedSound input@(first ∷ rest) value observed with first Fin.≟ (# 123)
... | no notOpen with observed
...   | ()
bracedSound input@(first ∷ rest) value observed | yes opened with drop 36 rest in dropped
... | [] with observed
...   | ()
bracedSound input@(first ∷ rest) value observed | yes opened | last ∷ next ∷ following with observed
... | ()
bracedSound input@(first ∷ rest) value observed | yes opened | last ∷ [] with last Fin.≟ (# 125)
... | no notClosed with observed
...   | ()
bracedSound input@(first ∷ rest) value observed | yes opened | last ∷ [] | yes closed = braced (take 36 rest)
  (cong₂ _∷_ opened (trans (sym (take++drop≡id 36 rest))
    (cong (take 36 rest ++_) (trans dropped (cong (_∷ []) closed)))))
  (hyphenatedSizedSound (length (take 36 rest)) (take 36 rest) value observed)

urnSound : ∀ input value → P.urn input ≡ P.accepted value → Accepted input value
urnSound input value observed with P.prefix P.urnPrefix input in prefixed
... | nothing with observed
...   | ()
urnSound input value observed | just body = urn body (prefixSound P.urnPrefix input body prefixed)
  (hyphenatedSizedSound (length body) body value observed)

readSizedSound : ∀ size input value → P.readSized size input ≡ P.accepted value → Accepted input value
readSizedSound size input value observed with size ≟ 32
... | yes sized = simple (Hex.sound 16 input value [] (finishSound input P.any (Hex.read 16 input) value observed))
... | no notSimple with size ≟ 36
...   | yes sized = hyphenated (hyphenatedSizedSound (length input) input value observed)
...   | no notRegular with size ≟ 38
...     | yes sized = bracedSound input value observed
...     | no notBraced with size ≟ 45
...       | yes sized = urnSound input value observed
...       | no notURN with observed
...         | ()

sound : ∀ input value → P.read input ≡ P.accepted value → Accepted input value
sound input value = readSizedSound (length input) input value

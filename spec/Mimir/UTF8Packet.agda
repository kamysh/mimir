{-# OPTIONS --safe #-}
-- Exact UTF-8 packet assembly with explicit continuation count and suffix.
-- Canonical scalar admission excludes overlong forms, surrogate code points
-- and values beyond Unicode's maximum.
module Mimir.UTF8Packet where

open import Data.List using (List; []; _∷_; _++_; map; length)
import Data.Vec as V
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_; _<_; _<?_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (_×-dec_; _⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; subst)
open import Mimir.Bits using (Byte; Word)
import Mimir.Bits as Bits
import Mimir.UTF8Byte as B

data Raw : Set where
  one : Word 7 → Raw
  two : Word 5 → Word 6 → Raw
  three : Word 4 → Word 6 → Word 6 → Raw
  four : Word 3 → Word 6 → Word 6 → Word 6 → Raw

encode : Raw → List Byte
encode (one payload) = B.singleByte payload ∷ []
encode (two high low) = B.twoByte high ∷ B.continuationByte low ∷ []
encode (three high middle low) = B.threeByte high ∷ B.continuationByte middle ∷ B.continuationByte low ∷ []
encode (four high middle next low) = B.fourByte high ∷ B.continuationByte middle ∷ B.continuationByte next ∷ B.continuationByte low ∷ []

fromSeven : Word 7 → Raw
fromSeven word = one word

fromEleven : Word 11 → Raw
fromEleven (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ high) = two high (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ V.[])

fromSixteen : Word 16 → Raw
fromSixteen (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ high) = three high (g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ V.[]) (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ V.[])

fromTwentyOne : Word 21 → Raw
fromTwentyOne (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ m V.∷ n V.∷ o V.∷ p V.∷ q V.∷ r V.∷ high) = four high (m V.∷ n V.∷ o V.∷ p V.∷ q V.∷ r V.∷ V.[]) (g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ V.[]) (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ V.[])

abstract
  codePoint : Raw → ℕ
  codePoint (one payload) = Bits.Binary.value payload
  codePoint (two high low) = Bits.Binary.value (low V.++ high)
  codePoint (three high middle low) = Bits.Binary.value (low V.++ (middle V.++ high))
  codePoint (four high middle next low) = Bits.Binary.value (low V.++ (next V.++ (middle V.++ high)))

  fromSevenValue : ∀ word → codePoint (fromSeven word) ≡ Bits.Binary.value word
  fromSevenValue word = refl

  fromElevenValue : ∀ word → codePoint (fromEleven word) ≡ Bits.Binary.value word
  fromElevenValue (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ high) = refl

  fromSixteenValue : ∀ word → codePoint (fromSixteen word) ≡ Bits.Binary.value word
  fromSixteenValue (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ high) = refl

  fromTwentyOneValue : ∀ word → codePoint (fromTwentyOne word) ≡ Bits.Binary.value word
  fromTwentyOneValue (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ m V.∷ n V.∷ o V.∷ p V.∷ q V.∷ r V.∷ high) = refl


minimum : Raw → ℕ
minimum (one _) = 0
minimum (two _ _) = 128
minimum (three _ _ _) = 2048
minimum (four _ _ _ _) = 65536

fromSevenMinimum : ∀ word → minimum (fromSeven word) ≡ 0
fromSevenMinimum word = refl

fromElevenMinimum : ∀ word → minimum (fromEleven word) ≡ 128
fromElevenMinimum (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ high) = refl

fromSixteenMinimum : ∀ word → minimum (fromSixteen word) ≡ 2048
fromSixteenMinimum (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ high) = refl

fromTwentyOneMinimum : ∀ word → minimum (fromTwentyOne word) ≡ 65536
fromTwentyOneMinimum (a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ f V.∷ g V.∷ h V.∷ i V.∷ j V.∷ k V.∷ l V.∷ m V.∷ n V.∷ o V.∷ p V.∷ q V.∷ r V.∷ high) = refl


Canonical : Raw → Set
Canonical raw = minimum raw ≤ codePoint raw ×
  (codePoint raw ≤ 1114111 × (codePoint raw < 55296 ⊎ 57344 ≤ codePoint raw))

canonical? : ∀ raw → Dec (Canonical raw)
canonical? raw = (minimum raw ≤? codePoint raw) ×-dec
  ((codePoint raw ≤? 1114111) ×-dec ((codePoint raw <? 55296) ⊎-dec (57344 ≤? codePoint raw)))

record Scalar : Set where
  constructor scalar
  field raw : Raw; canonical : Canonical raw

data Error : Set where truncated unexpectedContinuation invalidLeading invalidContinuation noncanonical : Error

record Continuations (count : ℕ) (input : List Byte) : Set where
  constructor continuations
  field
    payloads : V.Vec (Word 6) count
    suffix : List Byte
    exact : input ≡ map B.continuationByte (V.toList payloads) ++ suffix

readContinuations : ∀ count input → Error ⊎ Continuations count input
readContinuations zero input = inj₂ (continuations V.[] input refl)
readContinuations (suc count) [] = inj₁ truncated
readContinuations (suc count) (byte ∷ input) with B.classify byte | B.classifySound byte
... | B.single _ | _ = inj₁ invalidContinuation
... | B.leadingTwo _ | _ = inj₁ invalidContinuation
... | B.leadingThree _ | _ = inj₁ invalidContinuation
... | B.leadingFour _ | _ = inj₁ invalidContinuation
... | B.invalid | _ = inj₁ invalidContinuation
... | B.continuation payload | meaning with readContinuations count input
...   | inj₁ failure = inj₁ failure
...   | inj₂ (continuations payloads suffix exact) = inj₂
    (continuations (payload V.∷ payloads) suffix
      (cong₂ _∷_ meaning exact))

record Parsed (input : List Byte) : Set where
  constructor parsed
  field raw : Raw; suffix : List Byte; exact : input ≡ encode raw ++ suffix

read : ∀ input → Error ⊎ Parsed input
read [] = inj₁ truncated
read (byte ∷ input) with B.classify byte | B.classifySound byte
... | B.invalid | _ = inj₁ invalidLeading
... | B.continuation _ | _ = inj₁ unexpectedContinuation
... | B.single payload | meaning = inj₂ (parsed (one payload) input
    (cong (_∷ input) meaning))
... | B.leadingTwo high | meaning with readContinuations 1 input
...   | inj₁ failure = inj₁ failure
...   | inj₂ (continuations (low V.∷ V.[]) suffix exact) = inj₂ (parsed (two high low) suffix
    (cong₂ _∷_ meaning exact))
read (byte ∷ input) | B.leadingThree high | meaning with readContinuations 2 input
... | inj₁ failure = inj₁ failure
... | inj₂ (continuations (middle V.∷ low V.∷ V.[]) suffix exact) = inj₂ (parsed (three high middle low) suffix
    (cong₂ _∷_ meaning exact))
read (byte ∷ input) | B.leadingFour high | meaning with readContinuations 3 input
... | inj₁ failure = inj₁ failure
... | inj₂ (continuations (middle V.∷ next V.∷ low V.∷ V.[]) suffix exact) = inj₂ (parsed (four high middle next low) suffix
    (cong₂ _∷_ meaning exact))

record Decoded (input : List Byte) : Set where
  constructor decoded
  field value : Scalar; suffix : List Byte; exact : input ≡ encode (Scalar.raw value) ++ suffix

decode : ∀ input → Error ⊎ Decoded input
decode input with read input
... | inj₁ failure = inj₁ failure
... | inj₂ (parsed raw suffix exact) with canonical? raw
...   | no invalid = inj₁ noncanonical
...   | yes valid = inj₂ (decoded (scalar raw valid) suffix exact)

-- Exact byte reconstruction is carried by every successful decoded packet.
preservesBytes : ∀ {input} (result : Decoded input) →
  input ≡ encode (Scalar.raw (Decoded.value result)) ++ Decoded.suffix result
preservesBytes = Decoded.exact

equalProofs : ∀ {A : Set} {left right : A} (first second : left ≡ right) → first ≡ second
equalProofs refl refl = refl

continuationsRoundTrip : ∀ {count} (payloads : V.Vec (Word 6) count) suffix →
  readContinuations count (map B.continuationByte (V.toList payloads) ++ suffix) ≡
    inj₂ (continuations payloads suffix refl)
continuationsRoundTrip V.[] suffix = refl
continuationsRoundTrip (payload V.∷ rest) suffix
  with B.classify (B.continuationByte payload) | B.classifySound (B.continuationByte payload) | B.continuationRoundTrip payload
... | .(B.continuation payload) | meaning | refl
  rewrite continuationsRoundTrip rest suffix =
  cong inj₂ (cong (continuations (payload V.∷ rest) suffix) (equalProofs _ refl))

readRoundTrip : ∀ raw suffix → read (encode raw ++ suffix) ≡ inj₂ (parsed raw suffix refl)
readRoundTrip (one payload) suffix
  with B.classify (B.singleByte payload) | B.classifySound (B.singleByte payload) | B.singleRoundTrip payload
... | .(B.single payload) | meaning | refl =
  cong inj₂ (cong (parsed (one payload) suffix) (equalProofs _ refl))
readRoundTrip (two high low) suffix
  with B.classify (B.twoByte high) | B.classifySound (B.twoByte high) | B.twoRoundTrip high
... | .(B.leadingTwo high) | meaning | refl
  rewrite continuationsRoundTrip (low V.∷ V.[]) suffix =
  cong inj₂ (cong (parsed (two high low) suffix) (equalProofs _ refl))
readRoundTrip (three high middle low) suffix
  with B.classify (B.threeByte high) | B.classifySound (B.threeByte high) | B.threeRoundTrip high
... | .(B.leadingThree high) | meaning | refl
  rewrite continuationsRoundTrip (middle V.∷ low V.∷ V.[]) suffix =
  cong inj₂ (cong (parsed (three high middle low) suffix) (equalProofs _ refl))
readRoundTrip (four high middle next low) suffix
  with B.classify (B.fourByte high) | B.classifySound (B.fourByte high) | B.fourRoundTrip high
... | .(B.leadingFour high) | meaning | refl
  rewrite continuationsRoundTrip (middle V.∷ next V.∷ low V.∷ V.[]) suffix =
  cong inj₂ (cong (parsed (four high middle next low) suffix) (equalProofs _ refl))

readGiven : ∀ {input} (result : Parsed input) → read input ≡ inj₂ result
readGiven (parsed raw suffix refl) = readRoundTrip raw suffix

parsedUnique : ∀ {input} (first second : Parsed input) → first ≡ second
parsedUnique first second = inj₂-injective
  (trans (Relation.Binary.PropositionalEquality.sym (readGiven first)) (readGiven second))

-- The output proof may differ from the supplied proof, but the raw scalar
-- and the untouched suffix are identical. No proof-irrelevance assumption is
-- used for the compound canonicality predicate.
decodeComplete : ∀ raw → Canonical raw → ∀ suffix →
  Σ (Decoded (encode raw ++ suffix)) (λ result →
    decode (encode raw ++ suffix) ≡ inj₂ result ×
      (Scalar.raw (Decoded.value result) ≡ raw × Decoded.suffix result ≡ suffix))
decodeComplete raw valid suffix rewrite readRoundTrip raw suffix with canonical? raw
... | yes checked = decoded (scalar raw checked) suffix refl , refl , refl , refl
... | no impossible = ⊥-elim (impossible valid)

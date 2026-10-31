{-# OPTIONS --safe #-}
-- Full UTF-8 byte sequences. The recursion budget is the actual byte count;
-- every successful packet consumes at least one byte, so valid input cannot
-- fail because of an arbitrary parser fuel limit.
module Mimir.UTF8Text where

open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (++-assoc; length-++-≤ʳ; length-++-≤ˡ)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; s≤s⁻¹; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.UTF8Packet as Packet
open Packet using (Raw; Scalar; scalar; Error)

encode : List Scalar → List Byte
encode [] = []
encode (value ∷ rest) = Packet.encode (Scalar.raw value) ++ encode rest

record Decoded (input : List Byte) : Set where
  constructor decoded
  field values : List Scalar; exact : input ≡ encode values

packetPositive : ∀ raw → 1 ≤ length (Packet.encode raw)
packetPositive (Packet.one _) = s≤s z≤n
packetPositive (Packet.two _ _) = s≤s z≤n
packetPositive (Packet.three _ _ _) = s≤s z≤n
packetPositive (Packet.four _ _ _ _) = s≤s z≤n

dropNonemptyPrefix : ∀ (prefix suffix : List Byte) fuel → 1 ≤ length prefix →
  length (prefix ++ suffix) ≤ suc fuel → length suffix ≤ fuel
dropNonemptyPrefix [] suffix fuel () bound
dropNonemptyPrefix (first ∷ rest) suffix fuel positive bound =
  ≤-trans (length-++-≤ʳ suffix {xs = rest}) (s≤s⁻¹ bound)

suffixBound : ∀ {input} fuel (result : Packet.Decoded input) → length input ≤ suc fuel →
  length (Packet.Decoded.suffix result) ≤ fuel
suffixBound fuel (Packet.decoded (scalar raw canonical) suffix exact) bound rewrite exact =
  dropNonemptyPrefix (Packet.encode raw) suffix fuel (packetPositive raw) bound

readBounded : ∀ fuel input → length input ≤ fuel → Error ⊎ Decoded input
readBounded fuel [] bound = inj₂ (decoded [] refl)
readBounded zero (byte ∷ rest) ()
readBounded (suc fuel) (byte ∷ rest) bound with Packet.decode (byte ∷ rest)
... | inj₁ failure = inj₁ failure
... | inj₂ result with readBounded fuel (Packet.Decoded.suffix result) (suffixBound fuel result bound)
...   | inj₁ failure = inj₁ failure
...   | inj₂ (decoded values exact) = inj₂ (decoded (Packet.Decoded.value result ∷ values)
    (trans (Packet.Decoded.exact result) (cong (Packet.encode (Scalar.raw (Packet.Decoded.value result)) ++_) exact)))

decode : ∀ input → Error ⊎ Decoded input
decode input = readBounded (length input) input ≤-refl

preservesAllBytes : ∀ {input} (result : Decoded input) → input ≡ encode (Decoded.values result)
preservesAllBytes = Decoded.exact

boundProofIrrelevant : ∀ fuel input first second → readBounded fuel input first ≡ readBounded fuel input second
boundProofIrrelevant fuel input first second = cong (readBounded fuel input) (≤-irrelevant first second)

Successful : ∀ fuel input → length input ≤ fuel → Set
Successful fuel input bound = Σ (Decoded input) (λ result → readBounded fuel input bound ≡ inj₂ result)

combineSuccess : ∀ fuel input bound (packet : Packet.Decoded input) →
  Packet.decode input ≡ inj₂ packet →
  Successful fuel (Packet.Decoded.suffix packet) (suffixBound fuel packet bound) →
  Successful (suc fuel) input bound
combineSuccess fuel [] bound packet () rest
combineSuccess fuel (byte ∷ input) bound packet observed (decoded values exact , rest)
  rewrite observed | rest = _ , refl

encodedPositive : ∀ first rest → 1 ≤ length (encode (first ∷ rest))
encodedPositive first rest = ≤-trans (packetPositive (Scalar.raw first))
  (length-++-≤ˡ (Packet.encode (Scalar.raw first)))

oneNotZero : 1 ≤ 0 → ⊥
oneNotZero ()

encodedComplete : ∀ fuel values bound → Successful fuel (encode values) bound
encodedComplete fuel [] bound = decoded [] refl , refl
encodedComplete zero (first ∷ rest) bound = ⊥-elim (oneNotZero (≤-trans (encodedPositive first rest) bound))
encodedComplete (suc fuel) (scalar raw valid ∷ rest) bound
  with Packet.decodeComplete raw valid (encode rest)
... | Packet.decoded (scalar .raw checked) .(encode rest) exact , observed , refl , refl =
  combineSuccess fuel _ bound (Packet.decoded (scalar raw checked) (encode rest) exact) observed
    (encodedComplete fuel rest (suffixBound fuel (Packet.decoded (scalar raw checked) (encode rest) exact) bound))

decodeComplete : ∀ values → Σ (Decoded (encode values)) (λ result → decode (encode values) ≡ inj₂ result)
decodeComplete values = encodedComplete (length (encode values)) values ≤-refl

encodedNotEmpty : ∀ first rest → encode (first ∷ rest) ≡ [] → ⊥
encodedNotEmpty first rest same = oneNotZero (subst (λ bytes → 1 ≤ length bytes) same (encodedPositive first rest))

sameBytesSameRawValues : ∀ first second → encode first ≡ encode second → map Scalar.raw first ≡ map Scalar.raw second
sameBytesSameRawValues [] [] equal = refl
sameBytesSameRawValues [] (second ∷ tail) equal = ⊥-elim (encodedNotEmpty second tail (sym equal))
sameBytesSameRawValues (first ∷ rest) [] equal = ⊥-elim (encodedNotEmpty first rest equal)
sameBytesSameRawValues (first ∷ rest) (second ∷ tail) equal = cong₂ _∷_
  (cong Packet.Parsed.raw samePacket)
  (sameBytesSameRawValues rest tail (cong Packet.Parsed.suffix samePacket))
  where
  samePacket = Packet.parsedUnique
    (Packet.parsed (Scalar.raw first) (encode rest) refl)
    (Packet.parsed (Scalar.raw second) (encode tail) equal)

decodePreservesRawValues : ∀ values (result : Decoded (encode values)) →
  map Scalar.raw values ≡ map Scalar.raw (Decoded.values result)
decodePreservesRawValues values result = sameBytesSameRawValues values (Decoded.values result) (Decoded.exact result)

decodeGiven : ∀ {input} (expected : Decoded input) →
  Σ (Decoded input) (λ actual → decode input ≡ inj₂ actual ×
    map Scalar.raw (Decoded.values actual) ≡ map Scalar.raw (Decoded.values expected))
decodeGiven (decoded values refl) with decodeComplete values
... | result , observed = result , observed , sym (decodePreservesRawValues values result)

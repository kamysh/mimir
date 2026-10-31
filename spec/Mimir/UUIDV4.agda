{-# OPTIONS --safe #-}
-- Entropy is an observed input, not an axiom of freshness or randomness.
-- Byte normalization models from_ne_bytes followed by the UUID big-endian
-- representation. The 128-bit numeric-mask adapter is a separate obligation.
module Mimir.UUIDV4 where

open import Data.Vec using ([]; _∷_; reverse)
import Data.List as List
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Bits using (Word; unpackByte)
open import Mimir.UUIDGroups using (UUID)
import Mimir.WordBytes as Bytes
import Mimir.UUIDVersionBits as Version
import Mimir.Effects as Effects

data Endian : Set where littleEndian bigEndian : Endian

nativeWord : Endian → UUID → Word 128
nativeWord littleEndian = Bytes.fromLittle 16
nativeWord bigEndian = Bytes.fromBig 16

represented : Endian → UUID → UUID
represented endian input = Bytes.big 16 (nativeWord endian input)

littleRepresentation : ∀ input → represented littleEndian input ≡ reverse input
littleRepresentation input = cong reverse (Bytes.littleBytesRoundTrip 16 input)

bigRepresentation : ∀ input → represented bigEndian input ≡ input
bigRepresentation input = Bytes.bigBytesRoundTrip 16 input

mark : UUID → UUID
mark (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) =
  a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ Version.versionByte g ∷ h ∷ Version.variantByte i ∷
  j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []

-- Every byte outside the version/variant positions is exactly retained.
-- The two exceptional bytes retain their full input-derived bit equations.
data Marked : UUID → UUID → Set where
  marked : ∀ a b c d e f g h i j k l m n o p changedG changedI →
    unpackByte changedG ≡ Version.version (unpackByte g) →
    unpackByte changedI ≡ Version.variant (unpackByte i) →
    Marked (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ [])
      (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ changedG ∷ h ∷ changedI ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ [])

markCorrect : ∀ input → Marked input (mark input)
markCorrect (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ p ∷ []) =
  marked a b c d e f g h i j k l m n o p (Version.versionByte g)
    (Version.variantByte i) (Version.versionByteBits g) (Version.variantByteBits i)

fromRandom : Endian → UUID → UUID
fromRandom endian input = mark (represented endian input)

module With (RandomError : Set) where
  data Request : Set where randomBytes16 : Request

  Reply : Request → Set
  Reply randomBytes16 = RandomError ⊎ UUID

  module P = Effects.Protocol Request Reply
  open P

  data Outcome : Set where
    panicked : RandomError → Outcome
    generated : UUID → Outcome

  accept : Endian → Reply randomBytes16 → Outcome
  accept endian (inj₁ error) = panicked error
  accept endian (inj₂ bytes) = generated (fromRandom endian bytes)

  generate : Endian → Script Outcome
  generate endian = ask randomBytes16 (λ response → done (accept endian response))

  successfulReceipt : ∀ endian {events value} → Runs (generate endian) events (generated value) →
    Σ UUID (λ bytes → events ≡ (randomBytes16 , inj₂ bytes) List.∷ List.[] ×
      value ≡ fromRandom endian bytes)
  successfulReceipt endian (replied effect continuation (inj₂ bytes) (returned value)) = bytes , refl , refl

  failedReceipt : ∀ endian {events error} → Runs (generate endian) events (panicked error) →
    events ≡ (randomBytes16 , inj₁ error) List.∷ List.[]
  failedReceipt endian (replied effect continuation (inj₁ error) (returned value)) = refl

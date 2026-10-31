{-# OPTIONS --safe #-}
-- The two changed UUID bytes, with exact preservation of all remaining bits.
module Mimir.UUIDVersionBits where

open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Mimir.Bits using (Word; Byte; O; I; packByte; unpackByte; unpackPack)
import Mimir.BitLogic as Logic
open import Mimir.BitOverwrite using (wordMaskMeaning)

versionKeep versionForce variantKeep variantForce : Word 8
versionKeep = I ∷ I ∷ I ∷ I ∷ O ∷ O ∷ I ∷ O ∷ []
versionForce = O ∷ O ∷ O ∷ O ∷ O ∷ O ∷ I ∷ O ∷ []
variantKeep = I ∷ I ∷ I ∷ I ∷ I ∷ I ∷ O ∷ I ∷ []
variantForce = O ∷ O ∷ O ∷ O ∷ O ∷ O ∷ O ∷ I ∷ []

version variant : Word 8 → Word 8
version bits = Logic.wordOr (Logic.wordAnd bits versionKeep) versionForce
variant bits = Logic.wordOr (Logic.wordAnd bits variantKeep) variantForce

versionShape : ∀ a b c d e f g h →
  version (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) ≡
  a ∷ b ∷ c ∷ d ∷ O ∷ O ∷ I ∷ O ∷ []
versionShape a b c d e f g h =
  wordMaskMeaning (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) versionKeep versionForce

variantShape : ∀ a b c d e f g h →
  variant (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) ≡
  a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ O ∷ I ∷ []
variantShape a b c d e f g h =
  wordMaskMeaning (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) variantKeep variantForce

versionByte variantByte : Byte → Byte
versionByte byte = packByte (version (unpackByte byte))
variantByte byte = packByte (variant (unpackByte byte))

versionByteBits : ∀ byte → unpackByte (versionByte byte) ≡ version (unpackByte byte)
versionByteBits byte = unpackPack (version (unpackByte byte))

variantByteBits : ∀ byte → unpackByte (variantByte byte) ≡ variant (unpackByte byte)
variantByteBits byte = unpackPack (variant (unpackByte byte))

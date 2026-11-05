{-# OPTIONS --safe #-}
-- Schema byte limits count the exact UTF-8 bytes, including all non-ASCII
-- scalars; they do not accidentally count characters after conversion.
module Mimir.DecodedTextByteLength where

open import Data.List using ([]; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat using (_≤?_; _+_; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (≤⇒≯; ≤-trans)
open import Data.Product using (proj₁)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong₂)
import Mimir.Text as Text
import Mimir.UTF8Packet as P
import Mimir.UTF8Text as UTF8
import Mimir.UTF8ScalarIdentity as Identity
import Mimir.UnicodeScalar as U
import Mimir.ScalarCharacter as Character
import Mimir.DecodedText as Decoded

scalarWidth : ∀ value → Text.width (Character.character value) ≡ length (P.encode (P.Scalar.raw value))
scalarWidth value@(P.scalar (P.one payload) admitted) rewrite Character.exact value with P.codePoint (P.one payload) ≤? 127
... | yes fits = refl
... | no outside = ⊥-elim (outside (s≤s⁻¹ (Identity.oneBound payload)))
scalarWidth value@(P.scalar (P.two high low) admitted) rewrite Character.exact value with P.codePoint (P.two high low) ≤? 127
... | yes tooSmall = ⊥-elim (≤⇒≯ (proj₁ admitted) (s≤s tooSmall))
... | no aboveOne with P.codePoint (P.two high low) ≤? 2047
...   | yes fits = refl
...   | no outside = ⊥-elim (outside (s≤s⁻¹ (Identity.twoBound high low)))
scalarWidth value@(P.scalar (P.three high middle low) admitted) rewrite Character.exact value with P.codePoint (P.three high middle low) ≤? 127
... | yes tooSmall = ⊥-elim (≤⇒≯ (proj₁ admitted) (s≤s (≤-trans tooSmall (U.padding 127 1920))))
... | no aboveOne with P.codePoint (P.three high middle low) ≤? 2047
...   | yes tooSmall = ⊥-elim (≤⇒≯ (proj₁ admitted) (s≤s tooSmall))
...   | no aboveTwo with P.codePoint (P.three high middle low) ≤? 65535
...     | yes fits = refl
...     | no outside = ⊥-elim (outside (s≤s⁻¹ (Identity.threeBound high middle low)))
scalarWidth value@(P.scalar (P.four high middle next low) admitted) rewrite Character.exact value with P.codePoint (P.four high middle next low) ≤? 127
... | yes tooSmall = ⊥-elim (≤⇒≯ (proj₁ admitted) (s≤s (≤-trans tooSmall (U.padding 127 65408))))
... | no aboveOne with P.codePoint (P.four high middle next low) ≤? 2047
...   | yes tooSmall = ⊥-elim (≤⇒≯ (proj₁ admitted) (s≤s (≤-trans tooSmall (U.padding 2047 63488))))
...   | no aboveTwo with P.codePoint (P.four high middle next low) ≤? 65535
...     | yes tooSmall = ⊥-elim (≤⇒≯ (proj₁ admitted) (s≤s tooSmall))
...     | no fits = refl

exactByteLength : ∀ values → Text.byteLength (Decoded.text values) ≡ length (UTF8.encode values)
exactByteLength [] = refl
exactByteLength (value ∷ rest) = trans (cong₂ _+_ (scalarWidth value) (exactByteLength rest))
  (sym (length-++ (P.encode (P.Scalar.raw value)) {ys = UTF8.encode rest}))

{-# OPTIONS --safe #-}
-- Line extraction used by ParseError's Display implementation. The index
-- produced by translate_position always selects an existing split line.
module Mimir.WinnowLines where

open import Data.List using (List; []; _∷_; length; take)
open import Data.Nat using (ℕ; zero; suc; _⊓_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin using (#_; _≟_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.JsonPosition as Lines
import Mimir.WinnowPosition as Position

firstLine : List Byte → List Byte
firstLine [] = []
firstLine (byte ∷ rest) with byte ≟ (# 10)
... | yes newline = []
... | no other = byte ∷ firstLine rest

lineAt : ℕ → List Byte → Maybe (List Byte)
lineAt zero input = just (firstLine input)
lineAt (suc index) [] = nothing
lineAt (suc index) (byte ∷ rest) with byte ≟ (# 10)
... | yes newline = lineAt index rest
... | no other = lineAt (suc index) rest

prefixCountBound : ∀ count input → Lines.newlines (take count input) ≤ Lines.newlines input
prefixCountBound zero input = z≤n
prefixCountBound (suc count) [] = z≤n
prefixCountBound (suc count) (byte ∷ rest) with byte ≟ (# 10)
... | yes newline = s≤s (prefixCountBound count rest)
... | no other = prefixCountBound count rest

lineExists : ∀ index input → index ≤ Lines.newlines input → Σ (List Byte) λ line → lineAt index input ≡ just line
lineExists zero input bounded = firstLine input , refl
lineExists (suc index) [] ()
lineExists (suc index) (byte ∷ rest) bounded with byte ≟ (# 10)
... | yes newline = lineExists index rest (Data.Nat.s≤s⁻¹ bounded)
... | no other = lineExists (suc index) rest bounded

translatedLineExists : ∀ input offset → Σ (List Byte) λ line →
  lineAt (Position.Location.line (Position.translate input offset)) input ≡ just line
translatedLineExists [] offset = [] , refl
translatedLineExists input@(byte ∷ rest) offset = lineExists _ input
  (prefixCountBound (Lines.start (take (offset ⊓ length rest) input)) input)

{-# OPTIONS --safe #-}
-- Slicing and trimming preserve arbitrary per-character predicates. Unicode
-- admission is one instance; these operations cannot manufacture a scalar.
module Mimir.TextPredicatePreservation where

open import Data.Char using (Char)
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_; reverse)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
import Data.List.Properties as List
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Mimir.Text using (Text; trim; trimStart; isWhitespace)
import Mimir.MigrationSlices as Slices

module Preserve (Predicate : Char → Set) where
  reverseAll : ∀ {text} → All Predicate text → All Predicate (reverse text)
  reverseAll [] = []
  reverseAll {char ∷ rest} (head ∷ tail) = subst (All Predicate) (sym (List.unfold-reverse char rest))
    (All.++⁺ (reverseAll tail) (head ∷ []))

  trimStartAll : ∀ {text} → All Predicate text → All Predicate (trimStart text)
  trimStartAll [] = []
  trimStartAll {char ∷ rest} (head ∷ tail) with isWhitespace char
  ... | true = trimStartAll tail
  ... | false = head ∷ tail

  trimAll : ∀ {text} → All Predicate text → All Predicate (trim text)
  trimAll admitted = reverseAll (trimStartAll (reverseAll (trimStartAll admitted)))

  trimEndAll : ∀ {text} → All Predicate text → All Predicate (Slices.trimEnd text)
  trimEndAll admitted = reverseAll (trimStartAll (reverseAll admitted))

  suffix : ∀ input before after → input ≡ before ++ after → All Predicate input → All Predicate after
  suffix input before after exact admitted = All.++⁻ʳ before (subst (All Predicate) exact admitted)

  prefix : ∀ input before after → input ≡ before ++ after → All Predicate input → All Predicate before
  prefix input before after exact admitted = All.++⁻ˡ before (subst (All Predicate) exact admitted)

  body : ∀ input (parsed : Slices.Body input) → All Predicate input → All Predicate (Slices.script parsed)
  body input parsed admitted with Slices.conservation input parsed
  ... | spaces , whitespace , exact = trimEndAll
    (All.++⁻ˡ (Slices.Body.raw parsed) (suffix input spaces (Slices.Body.raw parsed ++ Slices.Body.rest parsed) exact admitted))

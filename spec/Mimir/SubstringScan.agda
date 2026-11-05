{-# OPTIONS --safe #-}
-- First substring occurrence, with exact conservation and minimality.
-- Searches are not implicitly anchored to line boundaries.
module Mimir.SubstringScan where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
import Mimir.SourceText as Source

module Scan (Character : Set) (equal : DecidableEquality Character) where
  module Match = Source.Matching Character equal
  Text = List Character

  data First (needle : Text) : Text → Text → Text → Set where
    here : ∀ {input} → Match.Prefix needle input → First needle input [] input
    later : ∀ {char input before after} → ¬ Match.Prefix needle (char ∷ input) →
      First needle input before after → First needle (char ∷ input) (char ∷ before) after

  data Result (needle input : Text) : Set where
    absent : ¬ Match.Contains needle input → Result needle input
    found : ∀ before after → First needle input before after → Result needle input

  search : ∀ needle input → Result needle input
  search needle [] with Match.prefix? needle []
  ... | yes prefix = found [] [] (here prefix)
  ... | no missing = absent (λ { (Match.here prefix) → missing prefix })
  search needle (char ∷ input) with Match.prefix? needle (char ∷ input)
  ... | yes prefix = found [] (char ∷ input) (here prefix)
  ... | no notHere with search needle input
  ...   | found before after occurrence = found (char ∷ before) after (later notHere occurrence)
  ...   | absent missing = absent λ where
    (Match.here prefix) → notHere prefix
    (Match.later occurrence) → missing occurrence

  exact : ∀ {needle input before after} → First needle input before after → input ≡ before ++ after
  exact (here prefix) = refl
  exact (later {char} notHere occurrence) = cong (char ∷_) (exact occurrence)

  startsAtBoundary : ∀ {needle input before after} → First needle input before after → Match.Prefix needle after
  startsAtBoundary (here prefix) = prefix
  startsAtBoundary (later notHere occurrence) = startsAtBoundary occurrence

  occurrence : ∀ {needle input before after} → First needle input before after → Match.Contains needle input
  occurrence (here prefix) = Match.here prefix
  occurrence (later notHere witness) = Match.later (occurrence witness)

  unique : ∀ {needle input firstBefore firstAfter secondBefore secondAfter} →
    First needle input firstBefore firstAfter → First needle input secondBefore secondAfter →
    firstBefore ≡ secondBefore × firstAfter ≡ secondAfter
  unique (here prefix) (here other) = refl , refl
  unique (here prefix) (later notHere witness) = ⊥-elim (notHere prefix)
  unique (later notHere witness) (here prefix) = ⊥-elim (notHere prefix)
  unique (later {char} notHere first) (later other second) with unique first second
  ... | beforeSame , afterSame = cong (char ∷_) beforeSame , afterSame

  stripPrefix : ∀ {needle input} → Match.Prefix needle input → Σ Text λ rest → input ≡ needle ++ rest
  stripPrefix {input = input} Match.empty = input , refl
  stripPrefix (Match.next {x = char} prefix) with stripPrefix prefix
  ... | rest , same = rest , cong (char ∷_) same

  consumeMatch : ∀ {needle input before after} → First needle input before after →
    Σ Text λ rest → input ≡ before ++ (needle ++ rest)
  consumeMatch {before = before} witness with stripPrefix (startsAtBoundary witness)
  ... | rest , matched = rest , trans (exact witness) (cong (before ++_) matched)

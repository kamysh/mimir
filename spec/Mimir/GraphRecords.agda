{-# OPTIONS --safe #-}
module Mimir.GraphRecords where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
import Data.Integer.Properties as Integer
open import Data.List using (List; []; _∷_; map; filterᵇ; length; drop; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_; _≤?_; _<?_; _+_)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.CandidateGraph as G
import Mimir.LearningCandidates as C
import Mimir.PosteriorComputation as P
import Mimir.GraphNumerics as N
import Mimir.RetrievalRanking as R
import Mimir.RevisionBounds as Bounds
import Mimir.EvidenceValidity as Evidence

newBelief : ℕ → ℤ → Text → Float → Float → Maybe Text → C.Memory → Maybe G.BeliefValues
newBelief id now content probability confidence project memory = Evidence.admit
  (G.beliefValues id content project memory now now probability confidence
    (P.Beta.alpha prior) (P.Beta.negative prior) (P.Beta.alpha prior) (P.Beta.negative prior))
  where prior = P.prior probability confidence

newBeliefHasValidEvidence : ∀ id now content probability confidence project memory value →
  newBelief id now content probability confidence project memory ≡ just value → Evidence.ValidBelief value
newBeliefHasValidEvidence id now content probability confidence project memory value =
  Evidence.admitSound _ value

newPattern : ℕ → ℤ → Text → Text → Float → Maybe G.PatternValues
newPattern id now situation approach success with N.probability success
... | false = nothing
... | true = just (G.patternValues id situation approach nothing now 0 success)

memoryMatches : Maybe C.Memory → C.Memory → Bool
memoryMatches nothing actual = true
memoryMatches (just wanted) actual = R.sameMemory wanted actual

listBeliefs : Maybe Text → Maybe C.Memory → List G.BeliefValues → List G.BeliefValues
listBeliefs project memory = filterᵇ (λ b → R.visible project (G.BeliefValues.project b) ∧
  memoryMatches memory (G.BeliefValues.memory b))

listPatterns : Maybe Text → List G.PatternValues → List G.PatternValues
listPatterns project = filterᵇ (λ p → R.visible project (G.PatternValues.project p))

pageBefore : G.BeliefValues → G.BeliefValues → Bool
pageBefore a b with G.BeliefValues.created a Integer.≟ G.BeliefValues.created b
... | yes _ = does (G.BeliefValues.identity a ≤? G.BeliefValues.identity b)
... | no _ = does (G.BeliefValues.created a Integer.≤? G.BeliefValues.created b)

pageAdmitted : ℕ → ℕ → Bool
pageAdmitted limit offset = does (1 ≤? limit)

everyPositivePageAdmitted : ∀ limit offset → pageAdmitted (suc limit) offset ≡ true
everyPositivePageAdmitted limit offset = refl

zeroPageRefused : ∀ offset → pageAdmitted 0 offset ≡ false
zeroPageRefused offset = refl

record Page : Set where
  constructor page
  field beliefs : List G.BeliefValues; total offset : ℕ; nextOffset : Maybe ℕ

-- Count and page SELECTs are separate READ COMMITTED observations. The total
-- must therefore not be silently recalculated from the later page snapshot.
pageResult : Maybe Text → Maybe C.Memory → ℕ → ℕ → ℕ → List G.BeliefValues → Page
pageResult project memory limit offset total observed = page rows total offset next
  where
  rows = take limit (drop offset (R.sort pageBefore (listBeliefs project memory observed)))
  next : Maybe ℕ
  next with (offset + length rows) <? total
  ... | yes _ = just (offset + length rows)
  ... | no _ = nothing

getPattern : ℕ → List G.PatternValues → Maybe G.PatternValues
getPattern id [] = nothing
getPattern id (p ∷ ps) with id ≟ G.PatternValues.identity p
... | yes _ = just p
... | no _ = getPattern id ps

-- Read adapters have already resolved legacy absent/unknown memory values to
-- Fact. Input parsers remain strict: unknown requested memory kinds are errors.
noMemoryFilter : ∀ memory → memoryMatches nothing memory ≡ true
noMemoryFilter memory = refl

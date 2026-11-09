{-# OPTIONS --safe #-}
-- Dependency operations are explicit parameters, not application callbacks.
-- F32 denotes IEEE binary32 operations (Rust f32); UnicodeLower denotes Rust's
-- full Unicode lowercase, which may expand one scalar into several scalars.
-- No implementation or correctness axiom for those standard dependencies is
-- asserted here. All Mimir selection, weights and accumulation are defined.
module Mimir.RetrievalRanking where


open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Char using (Char)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ; foldl; length; take; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_; _≤_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; isWhitespace)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Candidates

record F32 : Set₁ where
  field
    Value : Set
    fromNat : ℕ → Value
    decimal : ℕ → ℕ → Value -- nearest binary32 to numerator / denominator
    add divide : Value → Value → Value
    less : Value → Value → Bool -- unordered compares false

record Unicode : Set where
  field
    lowercase : Text → Text
    alphanumeric : Char → Bool

member : ℕ → List ℕ → Bool
member id [] = false
member id (x ∷ xs) = does (id ≟ x) ∨ member id xs

unique : List ℕ → List ℕ
unique = go []
  where
  go : List ℕ → List ℕ → List ℕ
  go seen [] = []
  go seen (x ∷ xs) with member x seen
  ... | true = go seen xs
  ... | false = x ∷ go (x ∷ seen) xs

sameMemory : Candidates.Memory → Candidates.Memory → Bool
sameMemory a b = does (Candidates.memoryEqual a b)

visible : Maybe Text → Maybe Text → Bool
visible nothing actual = true
visible (just wanted) nothing = true
visible (just wanted) (just actual) = does (wanted ≟Text actual)

eligible : Maybe Text → List ℕ → Graph.BeliefValues → Bool
eligible scope superseded b = visible scope (Graph.BeliefValues.project b) ∧
  not (sameMemory (Graph.BeliefValues.memory b) Candidates.working) ∧
  not (member (Graph.BeliefValues.identity b) superseded)

lookup : ℕ → List Graph.BeliefValues → Maybe Graph.BeliefValues
lookup id [] = nothing
lookup id (b ∷ bs) with id ≟ Graph.BeliefValues.identity b
... | yes _ = just b
... | no _ = lookup id bs

materialize : List ℕ → List Graph.BeliefValues → List Graph.BeliefValues
materialize [] all = []
materialize (id ∷ ids) all with lookup id all
... | nothing = materialize ids all
... | just b = b ∷ materialize ids all

prefix : Text → Text → Bool
prefix [] text = true
prefix (c ∷ cs) [] = false
prefix (c ∷ cs) (d ∷ ds) = does ((c ∷ []) ≟Text (d ∷ [])) ∧ prefix cs ds

contains : Text → Text → Bool
contains term [] = prefix term []
contains term text@(_ ∷ rest) = prefix term text ∨ contains term rest

-- Split on a supplied character predicate; empty pieces are discarded.
split : (Char → Bool) → Text → List Text
split separator = go []
  where
  flush : Text → List Text → List Text
  flush [] rest = rest
  flush word rest = reverse word ∷ rest
  go : Text → Text → List Text
  go word [] = flush word []
  go word (c ∷ cs) with separator c
  ... | true = flush word (go [] cs)
  ... | false = go (c ∷ word) cs

-- Insert before equals. Recursing from the right preserves original tie order.
insert : ∀ {A : Set} → (A → A → Bool) → A → List A → List A
insert before x [] = x ∷ []
insert before x (y ∷ ys) with before x y
... | true = x ∷ y ∷ ys
... | false = y ∷ insert before x ys

sort : ∀ {A : Set} → (A → A → Bool) → List A → List A
sort before [] = []
sort before (x ∷ xs) = insert before x (sort before xs)

hits : List Text → Text → ℕ
hits terms content = length (filterᵇ (λ term → contains term content) terms)

identityBefore : Graph.BeliefValues → Graph.BeliefValues → Bool
identityBefore first second = does (Graph.BeliefValues.identity first ≤? Graph.BeliefValues.identity second)

byIdentity : List Graph.BeliefValues → List Graph.BeliefValues
byIdentity = sort identityBefore

probabilityBefore : Graph.BeliefValues → Graph.BeliefValues → Bool
probabilityBefore first second with Graph.BeliefValues.probability second <ᵇ Graph.BeliefValues.probability first
... | true = true
... | false with Graph.BeliefValues.probability first <ᵇ Graph.BeliefValues.probability second
...   | true = false
...   | false = identityBefore first second

probabilityTiesUseIdentity : ∀ first second →
  (Graph.BeliefValues.probability second <ᵇ Graph.BeliefValues.probability first) ≡ false →
  (Graph.BeliefValues.probability first <ᵇ Graph.BeliefValues.probability second) ≡ false →
  probabilityBefore first second ≡ identityBefore first second
probabilityTiesUseIdentity first second reverse forward rewrite reverse | forward = refl

tokenBefore : (ℕ × Graph.BeliefValues) → (ℕ × Graph.BeliefValues) → Bool
tokenBefore (n , b) (m , c) with n ≟ m
... | yes _ = probabilityBefore b c
... | no _ = does (m ≤? n)

tokenRanking : Unicode → Text → List Graph.BeliefValues → List ℕ
tokenRanking unicode query all = map (λ { (_ , b) → Graph.BeliefValues.identity b })
  (sort tokenBefore (filterᵇ (λ { (n , _) → not (does (n ≟ 0)) })
    (map (λ b → hits terms (Unicode.lowercase unicode (Graph.BeliefValues.content b)) , b) all)))
  where terms = split isWhitespace (Unicode.lowercase unicode query)

priorRanking : List Graph.BeliefValues → List ℕ
priorRanking all = map Graph.BeliefValues.identity (sort probabilityBefore all)

typeRanking : Maybe Candidates.Memory → List Graph.BeliefValues → List ℕ
typeRanking nothing all = []
typeRanking (just wanted) all = map Graph.BeliefValues.identity
  (filterᵇ matching all ++ filterᵇ (λ b → not (matching b)) all)
  where matching = λ b → sameMemory wanted (Graph.BeliefValues.memory b)

record PositiveCount : Set where
  constructor positiveCount
  field count : ℕ; positive : 1 ≤ count

-- Omission means all matches; a supplied zero has no representation here.
Selection = Maybe PositiveCount

cap : ∀ {A : Set} → Selection → List A → List A
cap nothing xs = xs
cap (just selected) xs = take (PositiveCount.count selected) xs

module Fusion (ops : F32) where
  open F32 ops
  Scores = List (ℕ × Value)

  get : ℕ → Scores → Value
  get id [] = fromNat 0
  get id ((key , value) ∷ rest) with id ≟ key
  ... | yes _ = value
  ... | no _ = get id rest

  credit : ℕ → Value → Scores → Scores
  credit id delta [] = (id , add (fromNat 0) delta) ∷ []
  credit id delta ((key , value) ∷ rest) with id ≟ key
  ... | yes _ = (key , add value delta) ∷ rest
  ... | no _ = (key , value) ∷ credit id delta rest

  leg : Value → ℕ → List ℕ → Scores → Scores
  leg weight rank [] scores = scores
  leg weight rank (id ∷ ids) scores = leg weight (suc rank) ids
    (credit id (divide weight (add (fromNat 60) (fromNat rank))) scores)

  scores : List ℕ → List ℕ → List ℕ → List ℕ → Scores
  scores vector token prior preferred =
    leg (decimal 5 10) 0 preferred
      (leg (decimal 1 10) 0 prior
        (leg (decimal 3 10) 0 token (leg (fromNat 1) 0 vector [])))

  before : Scores → Graph.BeliefValues → Graph.BeliefValues → Bool
  before fused first second with less (get (Graph.BeliefValues.identity second) fused) (get (Graph.BeliefValues.identity first) fused)
  ... | true = true
  ... | false with less (get (Graph.BeliefValues.identity first) fused) (get (Graph.BeliefValues.identity second) fused)
  ...   | true = false
  ...   | false = identityBefore first second

  tiedScoresUseIdentity : ∀ fused first second →
    less (get (Graph.BeliefValues.identity second) fused) (get (Graph.BeliefValues.identity first) fused) ≡ false →
    less (get (Graph.BeliefValues.identity first) fused) (get (Graph.BeliefValues.identity second) fused) ≡ false →
    before fused first second ≡ identityBefore first second
  tiedScoresUseIdentity fused first second reverse forward rewrite reverse | forward = refl

  greaterScoreComesFirst : ∀ fused first second →
    less (get (Graph.BeliefValues.identity second) fused) (get (Graph.BeliefValues.identity first) fused) ≡ true →
    before fused first second ≡ true
  greaterScoreComesFirst fused first second greater rewrite greater = refl

  rank : List ℕ → List ℕ → Maybe Candidates.Memory → Selection →
    List Graph.BeliefValues → List Graph.BeliefValues
  rank vector token preferred limit matched = cap limit
    (sort (before fused) matched)
    where fused = scores vector token (priorRanking matched) (typeRanking preferred matched)

unlimited : ∀ {A : Set} (xs : List A) → cap nothing xs ≡ xs
unlimited xs = refl

globalVisible : ∀ scope → visible scope nothing ≡ true
globalVisible nothing = refl
globalVisible (just scope) = refl

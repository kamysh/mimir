{-# OPTIONS --safe #-}
module Mimir.BeliefExplanation where

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; length; take; drop)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤?_; _<?_; _+_)
open import Relation.Nullary using (yes; no; does)
open import Mimir.Text using (member)
open import Mimir.ReviewSchema using (Review; Feedback; Link)
import Mimir.CandidateGraph as Graph
import Mimir.ReviewEdges as Edges
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewPreparationPublication as Publication
import Mimir.LearningStore as Store
import Mimir.CandidateProvenance as Candidate
import Mimir.IndependentProvenance as Independent
import Mimir.PosteriorComputation as Numeric
import Mimir.ApplicationFloat as FloatInput

findBelief : ℕ → List Graph.Node → Maybe Graph.BeliefValues
findBelief id [] = nothing
findBelief id (Graph.patternNode p ∷ ns) = findBelief id ns
findBelief id (Graph.beliefNode b ∷ ns) with id ≟ Graph.BeliefValues.identity b
... | yes same = just b
... | no different = findBelief id ns

record Incoming : Set where
  constructor incoming
  field edge : Edges.Edge; sourceProbability : Float

parents : ℕ → List Graph.Node → List Edges.Edge → List Incoming
parents id nodes [] = []
parents id nodes (e ∷ es) with id ≟ Edges.Edge.to e
... | no different = parents id nodes es
... | yes same with findBelief (Edges.Edge.from e) nodes
...   | nothing = parents id nodes es
...   | just b = incoming e (Numeric.mean (Numeric.beta (Graph.BeliefValues.alpha b)
  (Graph.BeliefValues.beta b))) ∷ parents id nodes es

feedbackMentions : ℕ → List Feedback → Bool
feedbackMentions id [] = false
feedbackMentions id (f ∷ fs) = does (id ≟ Feedback.beliefID f) ∨ feedbackMentions id fs

linkMentions : ℕ → List Link → Bool
linkMentions id [] = false
linkMentions id (l ∷ ls) = does (id ≟ Link.from l) ∨ does (id ≟ Link.to l) ∨ linkMentions id ls

mentions : ℕ → Review → Bool
mentions id r = feedbackMentions id (Review.feedbacks r) ∨
  member id (Review.superseded r) ∨ linkMentions id (Review.links r)

insert : Review → List Review → List Review
insert r [] = r ∷ []
insert r (s ∷ ss) with Review.experienceID r ≤? Review.experienceID s
... | yes before = r ∷ s ∷ ss
... | no after = s ∷ insert r ss

reviews : ℕ → List ℕ → Ledger.World → List Review
reviews id [] ledger = []
reviews id (owner ∷ owners) ledger with Ledger.activeApplied
  (Ledger.World.cells ledger owner) (Ledger.World.histories ledger owner)
... | nothing = reviews id owners ledger
... | just r with mentions id r
...   | false = reviews id owners ledger
...   | true = insert r (reviews id owners ledger)

record Page : Set where
  constructor page
  field entries : List Review; total : ℕ; nextOffset : Maybe ℕ

paginate : ℕ → ℕ → List Review → Page
paginate offset limit rows with (offset + length (take limit (drop offset rows))) <? length rows
... | yes more = page (take limit (drop offset rows)) (length rows)
  (just (offset + length (take limit (drop offset rows))))
... | no finished = page (take limit (drop offset rows)) (length rows) nothing

record Explanation : Set where
  constructor explanation
  field
    belief : Graph.BeliefValues
    incomingEdges : List Incoming
    learning : Page
    candidateProvenance : Maybe Candidate.Provenance
    independentProvenance : Independent.Read

data Result : Set where
  beliefMissing invalidLimit invalidStoredProvenance : Result
  explained : Explanation → Result

origin : ℕ → Store.World → Independent.Read
origin id w with Numeric.lookup id (Store.World.independentOrigins w)
... | nothing = Independent.noProvenance
... | just value = Independent.decode value

get : ℕ → ℕ → ℕ → Store.World → Result
get id offset limit w with findBelief id (Publication.World.nodes (Store.World.publication w))
... | nothing = beliefMissing
... | just b with does (1 ≤? limit) ∧ does (limit ≤? 20)
...   | false = invalidLimit
...   | true with origin id w
...     | Independent.malformed = invalidStoredProvenance
...     | provenance = explained (explanation b
  (parents id (Publication.World.nodes (Store.World.publication w)) (Publication.World.edges (Store.World.publication w)))
  (paginate offset limit (reviews id (Store.identities w) (Publication.World.ledger (Store.World.publication w))))
  (Candidate.get id w) provenance)

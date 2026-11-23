# Explaining a stored belief

`explain_belief` returns the belief, its incoming propagation links, a page
of active reviews that mention the belief, and its available provenance.
A direct source names a user instruction or document. A review-owned
candidate points to the originating experience and reports whether the
candidate is still active or retired. This is evidence about where the
belief came from and how it is connected.

The entire explanation describes one database snapshot. For example, if a
review is corrected concurrently, the explanation cannot combine the old
belief values with the new review contributions. The current review page
excludes superseded review versions and orders active versions by creation
time and revision. Equal keys retain observation order. Omitting the count
returns all matching reviews after the requested offset.

[The application's read operation](GraphReadProtocol.agda) projects this
contract. [The Rust store](../../crates/core/src/store/learning.rs) holds one
read-only snapshot while reading the belief, links, reviews, and origins.

```agda
{-# OPTIONS --safe #-}
module Mimir.BeliefExplanation where

open import Mimir.Collections using (limitResults; validSelection)

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; length; take; drop; map)
open import Data.Integer using (ℤ)
import Data.Integer.Properties as Integer
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤?_; _<?_; _+_)
open import Relation.Nullary using (yes; no; does)
open import Mimir.UUIDGroups using (UUID; _≟UUID_; member)
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
import Mimir.RetrievalRanking as Ranking

findBelief : UUID → List Graph.Node → Maybe Graph.BeliefValues
findBelief id [] = nothing
findBelief id (Graph.patternNode p ∷ ns) = findBelief id ns
findBelief id (Graph.beliefNode b ∷ ns) with id ≟UUID Graph.BeliefValues.identity b
... | yes same = just b
... | no different = findBelief id ns

record Incoming : Set where
  constructor incoming
  field edge : Edges.Edge; sourceProbability : Float

parents : UUID → List Graph.Node → List Edges.Edge → List Incoming
parents id nodes [] = []
parents id nodes (e ∷ es) with id ≟UUID Edges.Edge.to e
... | no different = parents id nodes es
... | yes same with findBelief (Edges.Edge.from e) nodes
...   | nothing = parents id nodes es
...   | just b = incoming e (Numeric.mean (Numeric.beta (Graph.BeliefValues.alpha b)
  (Graph.BeliefValues.beta b))) ∷ parents id nodes es

feedbackMentions : UUID → List Feedback → Bool
feedbackMentions id [] = false
feedbackMentions id (f ∷ fs) = does (id ≟UUID Feedback.beliefID f) ∨ feedbackMentions id fs

linkMentions : UUID → List Link → Bool
linkMentions id [] = false
linkMentions id (l ∷ ls) = does (id ≟UUID Link.from l) ∨ does (id ≟UUID Link.to l) ∨ linkMentions id ls

mentions : UUID → Review → Bool
mentions id r = feedbackMentions id (Review.feedbacks r) ∨
  member id (Review.superseded r) ∨ linkMentions id (Review.links r)

OrderKey = ℤ × ℕ

before : (OrderKey × Review) → (OrderKey × Review) → Bool
before ((a , n) , r) ((b , m) , s) with a Integer.≟ b
... | yes _ = does (n ≤? m)
... | no _ = does (a Integer.≤? b)

reviews : UUID → Store.World → List Review
reviews id w = map proj₂ (Ranking.sort before (collect (Store.identities w)))
  where
  ledger = Publication.World.ledger (Store.World.publication w)
  collect : List UUID → List (OrderKey × Review)
  collect [] = []
  collect (owner ∷ owners) with Ledger.activeApplied
    (Ledger.World.cells ledger owner) (Ledger.World.histories ledger owner)
    | Store.timestamp owner (Ledger.R.Cell.review (Ledger.World.cells ledger owner)) (Store.World.reviewTimes w)
  ... | just r | just time with mentions id r
  ...   | true = ((time , Ledger.R.Cell.review (Ledger.World.cells ledger owner)) , r) ∷ collect owners
  ...   | false = collect owners
  collect (owner ∷ owners) | _ | _ = collect owners

record Page : Set where
  constructor page
  field entries : List Review; total : ℕ; nextOffset : Maybe ℕ

paginate : ℕ → Maybe ℕ → List Review → Page
paginate offset limit rows with (offset + length (limitResults limit (drop offset rows))) <? length rows
... | yes more = page (limitResults limit (drop offset rows)) (length rows)
  (just (offset + length (limitResults limit (drop offset rows))))
... | no finished = page (limitResults limit (drop offset rows)) (length rows) nothing

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

origin : UUID → Store.World → Independent.Read
origin id w with Numeric.lookup id (Store.World.independentOrigins w)
... | nothing = Independent.noProvenance
... | just value = Independent.decode value

get : UUID → ℕ → Maybe ℕ → Store.World → Result
get id offset limit w with findBelief id (Publication.World.nodes (Store.World.publication w))
... | nothing = beliefMissing
... | just b with validSelection limit
...   | false = invalidLimit
...   | true with origin id w
...     | Independent.malformed = invalidStoredProvenance
...     | provenance = explained (explanation b
  (parents id (Publication.World.nodes (Store.World.publication w)) (Publication.World.edges (Store.World.publication w)))
  (paginate offset limit (reviews id w))
  (Candidate.get id w) provenance)
```

{-# OPTIONS --safe #-}
-- Pure meanings of direct graph statements. Transaction orchestration and
-- multi-statement failures are separate from this single-statement write set.
module Mimir.GraphWrites where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Integer using (ℤ)
open import Data.String using (toList)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Binary64 using (Number)
import Mimir.ApplicationFloat as Numeric
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as G
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewEdges as Edges
import Mimir.ReviewSchema as R
import Mimir.IndependentProvenance as Origin
import Mimir.GraphNumerics as N
import Mimir.RetrievalRanking as Ranking

basisText : Origin.Basis → Text
basisText Origin.userInstruction = toList "user_instruction"
basisText Origin.document = toList "document"

insertBelief : G.BeliefValues → Maybe Origin.Provenance → Store.World → Store.World
insertBelief b nothing w = Store.insertNode (G.beliefNode b) w
insertBelief b (just origin) w = record inserted { learning = record learn
  { independentOrigins = (G.BeliefValues.identity b , Origin.stored
      (just (basisText (Origin.Provenance.basis origin))) (just (Origin.Provenance.reference origin)))
    ∷ Learning.World.independentOrigins learn } }
  where
  open import Data.Product using (_,_)
  inserted = Store.insertNode (G.beliefNode b) w
  learn = Store.World.learning inserted

insertPattern : G.PatternValues → Store.World → Store.World
insertPattern p = Store.insertNode (G.patternNode p)

directEdges : ℕ → ℕ → R.Relation → Number → List Edges.Edge
directEdges from to R.contradicts weight = Edges.edge nothing from to R.contradicts weight ∷
  Edges.edge nothing to from R.contradicts weight ∷ []
directEdges from to R.supports weight = Edges.edge nothing from to R.supports weight ∷ []
directEdges from to R.defeats weight = Edges.edge nothing from to R.defeats weight ∷ []
directEdges from to R.causes weight = Edges.edge nothing from to R.causes weight ∷ []

data Result : Set where
  invalidWeight missingEndpoint invalidRetirement : Result
  applied : Store.World → Result

addEdges : List Edges.Edge → Store.World → Store.World
addEdges edges w = record w { learning = record learn
  { publication = record pub { edges = Publication.World.edges pub ++ edges } } }
  where learn = Store.World.learning w; pub = Learning.World.publication learn

withDefeatClock : ℤ → R.Relation → ℕ → Store.World → Store.World
withDefeatClock received R.defeats target state = Store.recordDefeatTime received target state
withDefeatClock received _ target state = state

priorDefeat : ℕ → List Edges.Edge → Bool
priorDefeat target [] = false
priorDefeat target (edgeRow ∷ rest) with Edges.Edge.relation edgeRow
... | R.defeats = does (target ≟ Edges.Edge.to edgeRow) Data.Bool.∨ priorDefeat target rest
... | _ = priorDefeat target rest

clockAdmitted : R.Relation → ℕ → Store.World → Bool
clockAdmitted R.defeats target state with Store.lookupRetirement target state
... | just _ = true
... | nothing = not (priorDefeat target (Publication.World.edges (Learning.World.publication (Store.World.learning state))))
clockAdmitted _ target state = true

clockKeepsJournal : ∀ received relation target state → Store.World.operations (withDefeatClock received relation target state) ≡ Store.World.operations state
clockKeepsJournal received R.defeats target state with Store.lookupRetirement target state
... | nothing = refl
... | just _ = refl
clockKeepsJournal received R.supports target state = refl
clockKeepsJournal received R.causes target state = refl
clockKeepsJournal received R.contradicts target state = refl

insertEdge : ℤ → ℕ → ℕ → R.Relation → Number → Store.World → Result
insertEdge received from to relation weight w with Numeric.number weight
... | nothing = invalidWeight
... | just value with N.probability value
...   | false = invalidWeight
...   | true with Ranking.lookup from (Store.beliefs w) | Ranking.lookup to (Store.beliefs w)
...     | nothing | _ = missingEndpoint
...     | just _ | nothing = missingEndpoint
...     | just _ | just _ with clockAdmitted relation to w
...       | false = invalidRetirement
...       | true = applied (addEdges (directEdges from to relation weight) (withDefeatClock received relation to w))

insertEdgeKeepsJournal : ∀ received from to relation weight before after →
  insertEdge received from to relation weight before ≡ applied after →
  Store.World.operations after ≡ Store.World.operations before
insertEdgeKeepsJournal received from to relation weight before after accepted with Numeric.number weight
... | nothing with accepted
... | ()
insertEdgeKeepsJournal received from to relation weight before after accepted | just value with N.probability value
... | false with accepted
... | ()
insertEdgeKeepsJournal received from to relation weight before after accepted | just value | true
  with Ranking.lookup from (Store.beliefs before) | Ranking.lookup to (Store.beliefs before)
... | nothing | _ with accepted
... | ()
insertEdgeKeepsJournal received from to relation weight before after accepted | just value | true | just _ | nothing with accepted
... | ()
insertEdgeKeepsJournal received from to relation weight before after accepted | just value | true | just _ | just _
  with clockAdmitted relation to before
... | false with accepted
... | ()
insertEdgeKeepsJournal received from to relation weight before after accepted | just value | true | just _ | just _ | true with accepted
... | refl = clockKeepsJournal received relation to before

tagged : Text → Maybe Text → Bool
tagged project nothing = false
tagged project (just actual) = does (project ≟Text actual)

projectBeliefs : Text → Store.World → List ℕ
projectBeliefs project w = map G.BeliefValues.identity
  (filterᵇ (λ b → tagged project (G.BeliefValues.project b)) (Store.beliefs w))

projectPatterns : Text → Store.World → List ℕ
projectPatterns project w = map G.PatternValues.identity
  (filterᵇ (λ p → tagged project (G.PatternValues.project p)) (Store.patterns (Store.nodes w)))

deleteProjectBeliefs : Text → Store.World → Store.World
deleteProjectBeliefs project w = Store.removeNodes (projectBeliefs project w) false w

deleteProjectPatterns : Text → Store.World → Store.World
deleteProjectPatterns project w = Store.removeNodes (projectPatterns project w) false w

-- Bulk deletion deliberately uses exact ownership, not read visibility: global
-- beliefs/patterns are not selected by the project DELETE statement.
globalNotOwned : ∀ project → tagged project nothing ≡ false
globalNotOwned project = refl

contradictionBothDirections : ∀ from to weight → directEdges from to R.contradicts weight ≡
  (Edges.edge nothing from to R.contradicts weight ∷ Edges.edge nothing to from R.contradicts weight ∷ [])
contradictionBothDirections from to weight = refl

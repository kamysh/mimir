# How Mimir finds relevant beliefs

`query_relevant` takes a context string and can also take a project, a belief
type preference, a result count, and a request for citations. It returns the
original context, ranked beliefs, and a report of whether semantic search ran.
The [MCP request decoder](PublicRequest.agda) requires supplied counts to be
positive. The search only reads stored beliefs and their links.

## Report what was searched

The report distinguishes `performed`, `not_needed` because there were no
eligible beliefs, and `unavailable` with a cause, explanation, and suggested
next action. An unavailable semantic search can still return useful lexical
and graph results. For example, a configured provider that returns a zero
vector produces `invalid_provider_reply` even when lexical matches are found.
A blank context produces `unsupported_content` when eligible beliefs exist.
A database read failure returns an error. The
[MCP report encoder](ApplicationOutput.agda) defines the wire fields.

```agda
{-# OPTIONS --safe #-}
module Mimir.RetrievalProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; nonblank)
open import Mimir.DocumentQuery using (usableVector)
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Candidates
import Mimir.RetrievalRanking as R

-- Semantic retrieval can be unavailable for this particular input. It is not
-- equivalent to a completed search with no matches, and must survive every
-- later lexical/graph/evidence step into the public response.
data UnavailableCause : Set where
  notConfigured unsupportedContent providerFailure invalidProviderReply : UnavailableCause

record Unavailable : Set where
  constructor unavailable
  field
    cause : UnavailableCause
    reason nextAction : Text

data SemanticStatus : Set where
  performed noEligibleBeliefs : SemanticStatus
  notAvailable : Unavailable → SemanticStatus

record Report (A : Set) : Set where
  constructor report
  field
    context : Text
    beliefs : List A
    semanticSearch : SemanticStatus

EmbeddingReply = Unavailable ⊎ List (List Float)

record Request : Set where
  constructor request
  field query : Text; limit : Maybe ℕ; project : Maybe Text
        preference : Maybe Candidates.Memory; embeddingsEnabled : Bool

record Context : Set where
  constructor context
  field requestValue : Request; superseded : List UUID
        token vector : List UUID; matched : List Graph.BeliefValues
        semanticSearch : SemanticStatus

data State : Set where
  overlay : Request → State
  beliefs : Request → List UUID → State
  embedding : Request → List UUID → List Graph.BeliefValues → List UUID → State
  vectorQuery : Request → List UUID → List Graph.BeliefValues → List UUID → List Float → State
  closure : Context → UUID → List UUID → State
  neighbors : Context → Text → UUID → List UUID → List UUID → List UUID → State
  finished : Report Graph.BeliefValues → State
  failed : Text → State

Reply : State → Set
Reply (overlay r) = Text ⊎ List UUID
Reply (beliefs r retired) = Text ⊎ List Graph.BeliefValues
Reply (embedding r retired all token) = EmbeddingReply
Reply (vectorQuery r retired all token vector) = Text ⊎ List UUID
Reply (closure c id seeds) = Text ⊎ List Graph.BeliefValues
Reply (neighbors c project id seeds frontier next) = Text ⊎ List Graph.BeliefValues
Reply (finished result) = ⊤
Reply (failed message) = ⊤
```

## Select eligible beliefs before semantic ranking

Working beliefs and beliefs superseded by a review are excluded. A project
search includes beliefs tagged with that project and untagged global beliefs.
The current set of superseded beliefs applies to both scoped and unscoped
searches.
For example, a working belief with the closest vector cannot take the first
semantic rank and change the scores of the returned beliefs.

The embedding provider supplies one finite, nonzero query vector.
PostgreSQL ranks eligible stored vectors with a cosine direction by increasing
cosine distance. Equal distances may arrive in either order. Stored vectors
must be compatible with the configured provider for a cosine comparison.
Mimir sends all eligible identities and leaves the requested result count for
the final ranking step. The contract relies on PostgreSQL for distance and
on the embedding provider for vector production.

```agda
data Command : Set where
  readActiveOverlay : Command
  listBeliefs : Maybe Text → Command
  embedQuery : Text → Command
  queryVector : List Float → List UUID → Command
  readClosure : UUID → Command
  readNeighbors : UUID → Text → Command

command : State → Maybe Command
command (overlay r) = just readActiveOverlay
command (beliefs r retired) = just (listBeliefs (Request.project r))
command (embedding r retired all token) = just (embedQuery (Request.query r))
command (vectorQuery r retired all token v) =
  just (queryVector v (map Graph.BeliefValues.identity all))
command (closure c id seeds) = just (readClosure id)
command (neighbors c project id seeds frontier next) = just (readNeighbors id project)
command (finished result) = nothing
command (failed message) = nothing

unsupportedQuery : Unavailable
unsupportedQuery = unavailable unsupportedContent
  (toList "Semantic search is unavailable for a blank belief-search context.")
  (toList "Provide text describing the beliefs you want to find and resubmit.")

invalidVectorReply : Unavailable
invalidVectorReply = unavailable invalidProviderReply
  (toList "Semantic search requires one finite, nonzero vector for the query. The embedding provider did not return one.")
  (toList "These results use lexical and graph retrieval. Resolve the embedding provider response before requesting semantic search again.")

-- Keep first encountered row, preserving the service's append/visited order.
appendNew : List Graph.BeliefValues → List Graph.BeliefValues →
  List Graph.BeliefValues × List UUID
appendNew matched [] = matched , []
appendNew matched (b ∷ bs) with R.member (Graph.BeliefValues.identity b)
  (map Graph.BeliefValues.identity matched)
... | true = appendNew matched bs
... | false with appendNew (matched ++ (b ∷ [])) bs
...   | result , ids = result , (Graph.BeliefValues.identity b ∷ ids)
```

## Expand matches and rank the reply

Lexical search ignores case and counts the whitespace-separated query terms
that occur in the belief text. Lexical and semantic matches seed traversal
along support, cause, and defeat links. A project-scoped traversal stops at
ineligible neighbors. For example, a path through a belief in another project
cannot bring a later belief into scoped results. An unscoped traversal reads
the downstream closure and filters its returned beliefs. The search attaches
each candidate once.

The [ranking rules](RetrievalRanking.agda) combine semantic and lexical
positions, the belief probability ranking, and the optional type preference.
The preference contributes to score and leaves other types eligible. The
count takes the prefix of that final ranking. With the same observations,
asking for one result therefore selects the first result of the unlimited
reply. Ties in the final score preserve candidate encounter order. Belief
UUIDs are used for identity and deduplication.

Database reads are observations made during the search. The ranking rule
applies to those observations. Concurrent writes can change the observations
on a later request. [Rust search](../../crates/core/src/lib.rs) assembles the
results and [the vector query](../../crates/core/src/store.rs) supplies the
cosine ordering.

```agda
module Run (ops : R.F32) (unicode : R.Unicode) where
  module F = R.Fusion ops

  finish : Context → State
  finish c = finished (report (Request.query r)
    (F.rank (Context.vector c) (Context.token c)
      (Request.preference r) (Request.limit r) (Context.matched c))
    (Context.semanticSearch c))
    where r = Context.requestValue c

  seed : Context → List UUID → State
  seed c [] = finish c
  seed c (id ∷ seeds) with Request.project (Context.requestValue c)
  ... | nothing = closure c id seeds
  ... | just project = neighbors c project id seeds [] []

  seeded : Request → List UUID → List Graph.BeliefValues → List UUID → List UUID → SemanticStatus → State
  seeded r retired all token vector semantic = seed c (map Graph.BeliefValues.identity matched)
    where
    matched = R.materialize (R.unique (token ++ vector)) all
    c = context r retired token vector matched semantic

  loaded : Request → List UUID → List Graph.BeliefValues → State
  loaded r retired [] = finished (report (Request.query r) [] noEligibleBeliefs)
  loaded r retired all@(_ ∷ _) with nonblank (Request.query r) | Request.embeddingsEnabled r
  ... | false | _ = seeded r retired all [] [] (notAvailable unsupportedQuery)
  ... | true | true = embedding r retired all (R.tokenRanking unicode (Request.query r) all)
  ... | true | false = seeded r retired all (R.tokenRanking unicode (Request.query r) all) []
    (notAvailable (unavailable notConfigured
      (toList "Semantic search was not performed because no embedding provider is configured.")
      (toList "These results use lexical and graph retrieval. Configure an embedding provider if semantic search is required.")))

  nextHop : Context → Text → List UUID → List UUID → List UUID → State
  nextHop c project seeds (id ∷ rest) next = neighbors c project id seeds rest next
  nextHop c project seeds [] (id ∷ next) = neighbors c project id seeds next []
  nextHop c project seeds [] [] = seed c seeds

  advance : (s : State) → Reply s → State
  advance (overlay r) (inj₁ error) = failed error
  advance (overlay r) (inj₂ retired) = beliefs r retired
  advance (beliefs r retired) (inj₁ error) = failed error
  advance (beliefs r retired) (inj₂ all) = loaded r retired
    (filterᵇ (R.eligible (Request.project r) retired) all)
  advance (embedding r retired all token) (inj₁ why) = seeded r retired all token [] (notAvailable why)
  advance (embedding r retired all token) (inj₂ (v ∷ [])) with usableVector v
  ... | true = vectorQuery r retired all token v
  ... | false = seeded r retired all token [] (notAvailable invalidVectorReply)
  advance (embedding r retired all token) (inj₂ []) =
    seeded r retired all token [] (notAvailable invalidVectorReply)
  advance (embedding r retired all token) (inj₂ (_ ∷ _ ∷ _)) =
    seeded r retired all token [] (notAvailable invalidVectorReply)
  advance (vectorQuery r retired all token v) (inj₁ error) = failed error
  advance (vectorQuery r retired all token v) (inj₂ vector) =
    seeded r retired all token
      (filterᵇ (λ id → R.member id (map Graph.BeliefValues.identity all)) vector) performed
  advance (closure c id seeds) (inj₁ error) = failed error
  advance (closure c id seeds) (inj₂ rows) with appendNew (Context.matched c)
    (filterᵇ (R.eligible nothing (Context.superseded c)) rows)
  ... | matched , ids = seed (record c { matched = matched }) seeds
  advance (neighbors c project id seeds frontier next) (inj₁ error) = failed error
  advance (neighbors c project id seeds frontier next) (inj₂ rows) with
    appendNew (Context.matched c) (filterᵇ (R.eligible (just project) (Context.superseded c)) rows)
  ... | matched , ids = nextHop (record c { matched = matched }) project seeds frontier (next ++ ids)
  advance s@(finished result) reply = s
  advance s@(failed error) reply = s

  vectorFailureIsFailure : ∀ r retired all token v error →
    advance (vectorQuery r retired all token v) (inj₁ error) ≡ failed error
  vectorFailureIsFailure r retired all token v error = refl
```

## Preserve the availability report throughout traversal

Once the search has determined semantic availability, later graph reads
carry that status through to any completed reply. The theorem below applies
to every sequence of replies that reaches completion, including traversal
with repeated encounters. [ApplicationProtocol](ApplicationProtocol.agda)
assembles this search with the optional [evidence read](EvidenceRead.lagda.md).

```agda
  -- Once semantic availability is known, further graph traversal must not
  -- erase it. Database failures remain failures, not fabricated empty hits.
  data Retains : SemanticStatus → State → Set where
    atClosure : ∀ c id seeds → Retains (Context.semanticSearch c) (closure c id seeds)
    atNeighbors : ∀ c project id seeds frontier next →
      Retains (Context.semanticSearch c) (neighbors c project id seeds frontier next)
    atFinished : ∀ result → Retains (Report.semanticSearch result) (finished result)
    atFailure : ∀ status error → Retains status (failed error)

  seedRetains : ∀ c ids → Retains (Context.semanticSearch c) (seed c ids)
  seedRetains c [] = atFinished _
  seedRetains c (id ∷ seeds) with Request.project (Context.requestValue c)
  ... | nothing = atClosure c id seeds
  ... | just project = atNeighbors c project id seeds [] []

  nextHopRetains : ∀ c project seeds frontier next →
    Retains (Context.semanticSearch c) (nextHop c project seeds frontier next)
  nextHopRetains c project seeds (id ∷ rest) next = atNeighbors c project id seeds rest next
  nextHopRetains c project seeds [] (id ∷ next) = atNeighbors c project id seeds next []
  nextHopRetains c project seeds [] [] = seedRetains c seeds

  advanceRetains : ∀ {status state} (reply : Reply state) → Retains status state →
    Retains status (advance state reply)
  advanceRetains (inj₁ error) (atClosure c id seeds) = atFailure _ error
  advanceRetains (inj₂ rows) (atClosure c id seeds)
    with appendNew (Context.matched c) (filterᵇ (R.eligible nothing (Context.superseded c)) rows)
  ... | matched , ids = seedRetains (record c { matched = matched }) seeds
  advanceRetains (inj₁ error) (atNeighbors c project id seeds frontier next) = atFailure _ error
  advanceRetains (inj₂ rows) (atNeighbors c project id seeds frontier next)
    with appendNew (Context.matched c) (filterᵇ (R.eligible (just project) (Context.superseded c)) rows)
  ... | matched , ids = nextHopRetains (record c { matched = matched }) project seeds frontier (next ++ ids)
  advanceRetains reply (atFinished result) = atFinished result
  advanceRetains reply (atFailure status error) = atFailure status error

  data Returns : State → Report Graph.BeliefValues → Set where
    returned : ∀ result → Returns (finished result) result
    stepped : ∀ state (reply : Reply state) {result} →
      Returns (advance state reply) result → Returns state result

  completedRetainsStatus : ∀ {status state result} → Retains status state → Returns state result →
    Report.semanticSearch result ≡ status
  completedRetainsStatus (atFinished result) (returned .result) = refl
  completedRetainsStatus retained (stepped state reply rest) =
    completedRetainsStatus (advanceRetains reply retained) rest

```

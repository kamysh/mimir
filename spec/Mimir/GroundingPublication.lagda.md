# How weighted evidence changes a belief

An evidence link connects a document passage to a belief. The add
operation accepts a weight between zero and one. A positive weight
contributes evidence. A zero weight records the source while keeping
belief values unchanged. The MCP and CLI expose addition and use
weight one when the caller omits it. Removal is an internal store
operation.

Each successful add creates a contribution of its own. For example,
two successful adds of weight 0.5 for the same passage and belief
produce two links. Removing that pair removes both links.

[Why a published belief starts with a zero-weight link](BeliefEmbedding.lagda.md#why-the-source-link-has-zero-evidence-weight)

```agda
{-# OPTIONS --safe #-}
-- GROUNDS writes and their numerical consequences share the learning lock and
-- transaction. Adding the same pair again creates another contribution; explicit
-- removal deletes every matching edge. It does not rewrite immutable reviews.
module Mimir.GroundingPublication where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.List using (List; []; _∷_; _++_; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.LearningRecompute as Recompute
import Mimir.PosteriorComputation as Posterior
import Mimir.RetrievalRanking as Ranking
import Mimir.GraphNumerics as Numeric
import Mimir.LearningTransaction as Transaction

```

## Determine whether the evidence changed

The operation checks the supplied weight and requires both records
to exist before adding a link. Removing a pair with no matching links
leaves the store unchanged. Removing zero-weight links changes the
stored links without changing belief values.

```agda
data Request : Set where
  add : UUID → UUID → Float → Request -- chunk, belief, weight
  remove : UUID → UUID → Request

data Failure : Set where
  storageFailure : Text → Failure
  invalidWeight missingEndpoint invalidNumericInput invalidNumericWrite foreignTarget : Failure

admitted : Request → Bool
admitted (add chunk belief weight) = Numeric.probability weight
admitted (remove chunk belief) = true

matches : UUID → UUID → Store.Ground → Bool
matches chunk belief link =
  does (chunk ≟UUID Store.Ground.chunk link) ∧ does (belief ≟UUID Store.Ground.belief link)

unlink : UUID → UUID → Store.World → Store.World
unlink chunk belief before = record before
  { grounds = filterᵇ (λ link → not (matches chunk belief link)) (Store.World.grounds before) }

link : UUID → UUID → Float → Store.World → Store.World
link chunk belief weight before = record before
  { grounds = Store.World.grounds before ++ (Store.ground chunk belief weight ∷ []) }

```

## Recalculate and publish in one transaction

Adding or removing positive weight recalculates the target and the
beliefs that depend on it through inference links. The calculation
uses the remaining evidence and the original priors. The specification
limits its writes to the selected beliefs.

The transaction publishes the evidence edit and recalculated values
together. If calculation fails, the previous links and values survive.
If an attempt fails, the caller can correct the cause and submit it
again from the beginning. Two successful adds are two contributions.

[Rust adds evidence](../../crates/core/src/store.rs#L2059) · [Rust removes evidence](../../crates/core/src/store.rs#L2165)

```agda
module Operation (database : ℕ) (calculation : Posterior.Calculation) where
  module T = Transaction.Over Store.World ⊤ Failure database 671942183

  finish : Store.World → Recompute.Result → T.Decision
  finish proposed (Recompute.recomputed nodes warning) = T.replace (Store.setNodes nodes proposed) tt
  finish proposed Recompute.foreignTarget = T.reject foreignTarget
  finish proposed Recompute.invalidNumericInput = T.reject invalidNumericInput
  finish proposed Recompute.invalidNumericWrite = T.reject invalidNumericWrite

  recompute : UUID → Store.World → T.Decision
  recompute belief proposed = finish proposed (Recompute.runGlobal (Recompute.scopedCalculation calculation) (belief ∷ [])
    (Store.nodes proposed) (Publication.World.edges pub)
    (Recompute.activeReviewsScoped nothing (Learning.identities learn) (Publication.World.ledger pub))
    (Store.groundingMasses proposed))
    where learn = Store.World.learning proposed; pub = Learning.World.publication learn

  plan : Request → Store.World → T.Decision
  plan (remove chunk belief) before
    with filterᵇ (λ link → matches chunk belief link ∧ (0.0 <ᵇ Store.Ground.weight link)) (Store.World.grounds before)
  ... | [] = T.replace (unlink chunk belief before) tt
  ... | _ ∷ _ = recompute belief (unlink chunk belief before)
  plan (add chunk belief weight) before with Numeric.probability weight
  ... | false = T.reject invalidWeight
  ... | true with Store.chunk chunk (Store.World.chunks before) | Ranking.lookup belief (Store.beliefs before)
  ...   | nothing | _ = T.reject missingEndpoint
  ...   | just _ | nothing = T.reject missingEndpoint
  ...   | just _ | just _ with 0.0 <ᵇ weight
  ...     | true = recompute belief (link chunk belief weight before)
  ...     | false = T.replace (link chunk belief weight before) tt

```

## What admission and locking guarantee

A weight outside the accepted range is rejected before it can start a
transaction. A valid edit acquires the learning lock before touching
evidence or belief values. This keeps simultaneous edits consistent
with recalculation.

```agda
  module Run (request : Request) where
    module P = T.Plan (plan request)
    module Laws = T.Laws (plan request)

    -- Nothing is pre-transaction numeric rejection. It cannot acquire a lock,
    -- create an edge or trigger recomputation.
    start : Maybe (T.E.Script T.Outcome)
    start with admitted request
    ... | false = nothing
    ... | true = just P.start

    lockBeforeGrounding : T.Scoped T.outside P.start
    lockBeforeGrounding = Laws.startScoped
```

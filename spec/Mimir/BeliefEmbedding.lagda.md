# How Mimir publishes a supported belief

A direct `insert_belief` request gives Mimir a claim and the UUID of an
existing indexed passage that supports it. The caller selects the passage
after reading it. Similarity can help find a passage, but the caller must
decide whether the text supports the claim. The MCP tool also requires
independent provenance describing the user instruction or document behind
the claim.

For example, an agent can use `query_document` to find the passage that
states a project's release policy, then submit that passage's UUID with the
belief. If no passage supports the claim, the agent asks the user how to
proceed before resubmitting.

[MCP request handler](../../crates/mcp/src/main.rs#L665) · [Application protocol](ApplicationProtocol.agda)

```agda
{-# OPTIONS --safe #-}
-- A belief is published only after an embedding and a supporting indexed
-- document passage have been prepared. PostgreSQL creates the stored identity
-- as part of the publication and returns the resulting belief.
module Mimir.BeliefEmbedding where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID)
import Mimir.CandidateGraph as G
import Mimir.GraphNumerics as Numbers
import Mimir.LearningCandidates as Candidates
import Mimir.IndependentProvenance as Origin
import Mimir.DocumentStore as Documents
import Mimir.Effects as Effects

```

## Prepare the materials before saving

The draft holds the requested belief fields and the selected passage UUID.
Preparation supplies a nonempty embedding and an indexed passage, or a
reason and suggested action for the caller. Neither the draft nor the
prepared materials contain a new belief UUID.

Rust looks up the passage and checks its project before requesting an
embedding. An unavailable or incompatible passage produces correction
guidance. A missing or failing embedding provider calls for a user decision
or repair before the request can proceed.

[Preparation in Rust](../../crates/core/src/lib.rs#L284)

```agda
record Draft : Set where
  constructor draft
  field
    content : Text
    probability confidence : Float
    project : Maybe Text
    memory : Candidates.Memory
    origin : Maybe Origin.Provenance
    supportingPassageID : UUID

-- The preparation boundary supplies an embedding and a passage from an
-- indexed document. It does not create the belief or its database identity.
record Prepared : Set where
  constructor prepared
  field
    firstComponent : Float
    remainingComponents : List Float
    supportingPassage : Documents.Chunk

vector : Prepared → List Float
vector material = Prepared.firstComponent material ∷ Prepared.remainingComponents material

data Preparation : Set where
  ready : Prepared → Preparation
  askUser : Text → Text → Preparation -- explanation and suggested action

data Failure : Set where
  needsInput : Text → Text → Failure
  publicationFailed : Text → Failure

```

## Publish in one transaction

The operation checks embedding availability and the allowed range for
probability and confidence. It proceeds to publication only after
preparation returns both materials. A publication reply either returns
the saved belief or reports a failure.

In Rust, PostgreSQL generates the belief UUID inside the transaction that
writes the belief, its vector, and its source link. The store checks the
passage again before commit because it can change while the embedding is
being prepared.

[Publication transaction](../../crates/core/src/store.rs#L534) · [Publication requirements in Agda](ApplicationProtocol.agda#L145)

```agda
data Effect : Set where
  prepare : Draft → Effect
  publish : Draft → Prepared → Effect

Reply : Effect → Set
Reply (prepare _) = Preparation
Reply (publish _ _) = Text ⊎ G.BeliefValues

module E = Effects.Protocol Effect Reply
open E

Result = Failure ⊎ G.BeliefValues

admit : Bool → Draft → Maybe Failure
admit false input = just (needsInput
  (toList "An embedding is required before the belief can be saved.")
  (toList "Configure an embedding provider, then retry."))
admit true input with Numbers.probability (Draft.probability input) | Numbers.probability (Draft.confidence input)
... | false | _ = just (needsInput
  (toList "The belief probability must be between 0 and 1.")
  (toList "Choose a probability between 0 and 1, then retry."))
... | true | false = just (needsInput
  (toList "The belief confidence must be between 0 and 1.")
  (toList "Choose a confidence between 0 and 1, then retry."))
... | true | true = nothing

start : Bool → Draft → Script Result
start enabled input with admit enabled input
... | just failure = done (inj₁ failure)
... | nothing = ask (prepare input) λ where
  (askUser reason guidance) → done (inj₁ (needsInput reason guidance))
  (ready material) → ask (publish input material) λ where
    (inj₁ error) → done (inj₁ (publicationFailed error))
    (inj₂ belief) → done (inj₂ belief)

```

## Why the source link has zero evidence weight

A supporting passage makes a belief traceable. An agent can inspect the
passage later and see what the author relied on. The publication request
contains no separate judgment about how much the passage should change
the belief's probability. A similarity score helps rank passages for
inspection. It supplies no such judgment.

For example, if the caller submits a belief with probability 0.60 and
cites a retention policy, Mimir saves the belief at 0.60 with a link to
that policy. Recalculation reads the weights of source links. A nonzero
weight here could change the belief later, even though publication
returned 0.60. The zero weight makes the citation's contribution zero.
Other evidence can still change the belief.

Agda requires the saved probability to equal the submitted probability.
It also takes the complete list of links to the new belief immediately
after publication and requires exactly one entry, the selected passage
with weight zero. Checking only that a zero-weight link exists would
also allow a second link with positive weight, even a second link to
the same passage. That link could change the result of recalculation.
Rust saves the probability and inserts the single link in the same
transaction. This requirement applies at publication, so later explicit
evidence can still be added.

[Direct publication receipt](ApplicationProtocol.agda#L157) · [Weights read for recalculation](ApplicationStore.agda#L114) · [Rust source write](../../crates/core/src/store.rs#L610)

Review-created beliefs follow the same rule. Their Agda publication
proof requires the source row with zero weight and shows that attaching
the prepared materials preserves the proposed belief values. Adding
weighted evidence is a separate operation that takes an explicit weight
and recalculates the affected beliefs.

[Review publication proof](ReviewBeliefPreparation.lagda.md#commit-the-review-and-its-materials-together) · [Explicit evidence weight](GroundingPublication.agda#L59)

## What the proof says about asking for input

For every draft and every execution that returns `needsInput`, the
proof shows that the operation either stopped at admission or stopped
after preparation asked for input. In both cases, it issued no publication
request. If preparation succeeded but publication failed, the application
protocol specifies rollback separately. Once the prerequisite is fixed,
the caller can restart the request from the beginning.

[Publication failure and rollback](ApplicationProtocol.agda#L528)

```agda
-- A request for a user decision has not issued the publication operation.
data NoPublication : List Event → Set where
  noEffects : NoPublication []
  onlyPreparation : ∀ input reason guidance →
    NoPublication ((prepare input , askUser reason guidance) ∷ [])

needsInputDoesNotPublish : ∀ enabled input reason guidance events →
  Runs (start enabled input) events (inj₁ (needsInput reason guidance)) → NoPublication events
needsInputDoesNotPublish enabled input reason guidance events execution with admit enabled input
... | just failure with execution
...   | returned _ = noEffects
needsInputDoesNotPublish enabled input reason guidance events execution | nothing with execution
... | replied _ _ (askUser why next) (returned _) = onlyPreparation input why next
... | replied _ _ (ready material) (replied _ _ (inj₁ error) ())
... | replied _ _ (ready material) (replied _ _ (inj₂ belief) ())
```

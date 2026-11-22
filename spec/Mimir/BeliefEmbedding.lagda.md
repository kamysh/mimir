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
being prepared. Both the application contract and Rust require the source
link to have zero evidence weight. The link records the source while
preserving the supplied probability and adding no evidence mass for
later recalculation.

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

## What the proof says about asking for input

For every draft and every execution that returns `needsInput`, the
proof shows that the operation either stopped at admission or stopped
after preparation asked for input. In both cases, it issued no publication
request. If preparation succeeded but publication failed, the application
protocol specifies rollback separately. Once the prerequisite is fixed,
the caller can restart the request from the beginning.

[Publication failure and rollback](ApplicationProtocol.agda#L527)

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

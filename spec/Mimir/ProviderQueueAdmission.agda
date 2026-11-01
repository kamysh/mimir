{-# OPTIONS --safe #-}
-- Connect accepted provider envelopes to queue admission without silently
-- imposing chat-only name rules on the other provider formats.
module Mimir.ProviderQueueAdmission where

open import Data.List using ([])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Mimir.Text using (Text; Nonempty; nonempty?)
open import Mimir.Validation using (Fault; result; check; fault; emptyText; reported; noFalseRejection)
import Mimir.StructuredValue as V
import Mimir.ProviderResponse as Response
import Mimir.ProviderCollection as Collection
import Mimir.ProviderReplay as Replay

module Q = Response.Q

identityOnly : ∀ request → Response.IdentityValid request → Q.CallValidFor Q.deferred request
identityOnly request identity = identity , tt

deferredAdmission : (response : Response.Reply) →
  Q.BatchValidFor Q.deferred (Response.Reply.calls response)
deferredAdmission response with Response.Reply.valid response
... | identities , unique = All.map (λ {request} → identityOnly request) identities , unique

requiredCalls : ∀ {calls} → All Response.IdentityValid calls → All (λ request → Nonempty (Q.Call.name request)) calls →
  All (Q.CallValidFor Q.required) calls
requiredCalls [] [] = []
requiredCalls (identity ∷ rest) (name ∷ names) = (identity , name) ∷ requiredCalls rest names

requiredAdmission : (response : Response.Reply) →
  All (λ request → Nonempty (Q.Call.name request)) (Response.Reply.calls response) →
  Q.BatchValidFor Q.required (Response.Reply.calls response)
requiredAdmission response names with Response.Reply.valid response
... | identities , unique = requiredCalls identities names , unique

module Admission (arguments : Text → Fault ⊎ V.Value) where
  module D = Response.Decode arguments
  module C = Collection.Collection arguments
  module R = Replay.Replay arguments

  chatName : ∀ allowObject input request → D.chatItem allowObject input ≡ inj₂ (just request) → Nonempty (Q.Call.name request)
  chatName allowObject input request observed with Response.string "missing chat call ID" (Response.get "id" input)
  ... | inj₁ failure with observed
  ...   | ()
  chatName allowObject input request observed | inj₂ identity
    with Response.string "missing chat function name" (Response.get "name" (Response.get "function" input))
  ... | inj₁ failure with observed
  ...   | ()
  chatName allowObject input request observed | inj₂ identity | inj₂ name
    with Response.ensure (Response.isText "function" (Response.get "type" input)) "invalid chat function call"
  ... | inj₁ failure with observed
  ...   | ()
  chatName allowObject input request observed | inj₂ identity | inj₂ name | inj₂ tt
    with result (check (fault [] emptyText "invalid chat function call") (nonempty? name))
  ... | inj₁ failure with observed
  ...   | ()
  chatName allowObject input request observed | inj₂ identity | inj₂ name | inj₂ tt | inj₂ named
    with D.makeCallPreserves identity name (D.chatArguments allowObject (Response.get "arguments" (Response.get "function" input))) request observed
  ... | identityExact , nameExact , argumentsExact = subst Nonempty (sym nameExact) named

  chatAdmission : ∀ allowObject input response → D.chat allowObject input ≡ inj₂ response →
    Q.BatchValidFor Q.required (Response.Reply.calls response)
  chatAdmission allowObject input response observed with R.Chat.preserves allowObject input response observed
  ... | choice , rawCalls , selected , rawField , extracted , replay = requiredAdmission response
    (Calls.Extraction.everyOutput (chatName allowObject) (Calls.preservesExtraction extracted))
    where module Calls = C.For (D.chatItem allowObject)

  openaiQueueAccepts : ∀ input response → D.openai input ≡ inj₂ response →
    reported (Q.checkBatchFor Q.deferred (Response.Reply.calls response)) ≡ []
  openaiQueueAccepts input response observed = noFalseRejection
    (Q.checkBatchFor Q.deferred (Response.Reply.calls response)) (deferredAdmission response)

  anthropicQueueAccepts : ∀ input response → D.anthropic input ≡ inj₂ response →
    reported (Q.checkBatchFor Q.deferred (Response.Reply.calls response)) ≡ []
  anthropicQueueAccepts input response observed = noFalseRejection
    (Q.checkBatchFor Q.deferred (Response.Reply.calls response)) (deferredAdmission response)

  chatQueueAccepts : ∀ allowObject input response → D.chat allowObject input ≡ inj₂ response →
    reported (Q.checkBatchFor Q.required (Response.Reply.calls response)) ≡ []
  chatQueueAccepts allowObject input response observed = noFalseRejection
    (Q.checkBatchFor Q.required (Response.Reply.calls response)) (chatAdmission allowObject input response observed)

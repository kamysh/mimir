{-# OPTIONS --safe #-}
-- Successful response parsing preserves original replay values and the exact
-- ordered extraction of calls, including calls carrying argument failures.
module Mimir.ProviderReplay where

open import Data.List using (List; []; _∷_)
import Data.Bool
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault)
import Mimir.Validation as Validation
import Mimir.Collections as Collections
import Mimir.StructuredValue as V
import Mimir.ProviderResponse as Response
import Mimir.ProviderCollection as Collection

module Replay (arguments : Text → Fault ⊎ V.Value) where
  module D = Response.Decode arguments
  module C = Collection.Collection arguments
  module OpenAI = C.For D.openaiItem
  module Anthropic = C.For D.anthropicItem

  OpenAIContract : V.Value → Response.Reply → Set
  OpenAIContract input response = Σ (List V.Value) λ output →
    Response.array "invalid OpenAI output" (Response.get "output" input) ≡ inj₂ output ×
    (OpenAI.Collected [] output (Response.Reply.calls response) × Response.Reply.replay response ≡ output)

  openaiPreserves : ∀ input response → D.openai input ≡ inj₂ response →
    OpenAIContract input response
  openaiPreserves input response observed
    with Response.ensure (Response.isText "completed" (Response.get "status" input)) "OpenAI response is incomplete"
  ... | inj₁ failure with observed
  ...   | ()
  openaiPreserves input response observed | inj₂ tt
    with Response.array "invalid OpenAI output" (Response.get "output" input) in outputField
  ... | inj₁ failure with observed
  ...   | ()
  openaiPreserves input response observed | inj₂ tt | inj₂ output
    with D.collect D.openaiItem [] output in collected
  ... | inj₁ failure with observed
  ...   | ()
  openaiPreserves input response observed | inj₂ tt | inj₂ output | inj₂ calls
    with Response.finishPreserves output calls response observed
  ... | replayExact , callsExact = output , refl ,
    subst (OpenAI.Collected [] output) (sym callsExact) (OpenAI.sound [] output calls collected) , replayExact

  AnthropicContract : V.Value → Response.Reply → Set
  AnthropicContract input response = Σ (List V.Value) λ content →
    Response.array "invalid Anthropic content" (Response.get "content" input) ≡ inj₂ content ×
    (Anthropic.Collected [] content (Response.Reply.calls response) ×
      Response.Reply.replay response ≡ Response.anthropicReplay content)

  anthropicPreserves : ∀ input response → D.anthropic input ≡ inj₂ response →
    AnthropicContract input response
  anthropicPreserves input response observed
    with Response.array "invalid Anthropic content" (Response.get "content" input) in contentField
  ... | inj₁ failure with observed
  ...   | ()
  anthropicPreserves input response observed | inj₂ content
    with D.collect D.anthropicItem [] content in collected
  ... | inj₁ failure with observed
  ...   | ()
  anthropicPreserves input response observed | inj₂ content | inj₂ calls
    with D.stopReason "tool_use" "end_turn" "Anthropic response is incomplete" (Response.get "stop_reason" input) calls
  ... | inj₁ failure with observed
  ...   | ()
  anthropicPreserves input response observed | inj₂ content | inj₂ calls | inj₂ tt
    with Response.finishPreserves (Response.anthropicReplay content) calls response observed
  ... | replayExact , callsExact = content , refl ,
    subst (Anthropic.Collected [] content) (sym callsExact) (Anthropic.sound [] content calls collected) , replayExact

  module Chat (allowObject : Data.Bool.Bool) where
    module Calls = C.For (D.chatItem allowObject)

    Contract : V.Value → Response.Reply → Set
    Contract input response = Σ V.Value λ choice → Σ (List V.Value) λ rawCalls →
      D.chatChoice input ≡ inj₂ choice ×
      (D.rawChatCalls (Response.get "tool_calls" (Response.get "message" choice)) ≡ inj₂ rawCalls ×
      (Calls.Collected [] rawCalls (Response.Reply.calls response) ×
        Response.Reply.replay response ≡ Response.get "message" choice ∷ []))

    preserves : ∀ input response → D.chat allowObject input ≡ inj₂ response →
      Contract input response
    preserves input response observed with D.chatChoice input in selectedChoice
    ... | inj₁ failure with observed
    ...   | ()
    preserves input response observed | inj₂ choice
      with Response.ensure (Response.isText "assistant" (Response.get "role" (Response.get "message" choice))) "invalid chat assistant message"
    ... | inj₁ failure with observed
    ...   | ()
    preserves input response observed | inj₂ choice | inj₂ tt
      with Response.ensure (Response.isObject (Response.get "message" choice)) "invalid chat assistant message"
    ... | inj₁ failure with observed
    ...   | ()
    preserves input response observed | inj₂ choice | inj₂ tt | inj₂ tt
      with D.rawChatCalls (Response.get "tool_calls" (Response.get "message" choice)) in rawField
    ... | inj₁ failure with observed
    ...   | ()
    preserves input response observed | inj₂ choice | inj₂ tt | inj₂ tt | inj₂ rawCalls
      with D.stopReason "tool_calls" "stop" "chat response is incomplete" (Response.get "finish_reason" choice) rawCalls
    ... | inj₁ failure with observed
    ...   | ()
    preserves input response observed | inj₂ choice | inj₂ tt | inj₂ tt | inj₂ rawCalls | inj₂ tt
      with D.collect (D.chatItem allowObject) [] rawCalls in collected
    ... | inj₁ failure with observed
    ...   | ()
    preserves input response observed | inj₂ choice | inj₂ tt | inj₂ tt | inj₂ rawCalls | inj₂ tt | inj₂ calls
      with Response.finishPreserves (Response.get "message" choice ∷ []) calls response observed
    ... | replayExact , callsExact = choice , rawCalls , refl , rawField ,
      subst (Calls.Collected [] rawCalls) (sym callsExact) (Calls.sound [] rawCalls calls collected) , replayExact

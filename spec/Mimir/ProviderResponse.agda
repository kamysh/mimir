{-# OPTIONS --safe #-}
-- Structural response decoding for the three provider wire formats used by
-- the judge. Argument decoding is an explicit parameter here; malformed
-- arguments remain a request result, while malformed envelopes reject the batch.
module Mimir.ProviderResponse where

open import Data.Bool using (Bool; true; false; _∨_; not)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.Empty
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; Nonempty; Bounded; nonempty?; bounded?)
open import Mimir.Validation
open import Mimir.RecordDecoding using (_>>=_; mapResult)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.StructuredValue as V
import Mimir.ProviderQueue as Provider
import Mimir.Collections as Collections
import Mimir.Binary64 as Binary

module Q = Provider.Queue V.Value

get : String → V.Value → V.Value
get name (V.object fields) with V.Object.normalize fields (toList name)
... | nothing = V.null
... | just value = value
get name _ = V.null

isText : String → V.Value → Bool
isText expected (V.string actual) with actual ≟Text toList expected
... | yes same = true
... | no different = false
isText expected _ = false

isNull isObject isString : V.Value → Bool
isNull V.null = true
isNull _ = false
isObject (V.object fields) = true
isObject _ = false
isString (V.string text) = true
isString _ = false

ensure : Bool → String → Fault ⊎ ⊤
ensure true message = inj₂ tt
ensure false message = inj₁ (fault [] malformedInput message)

string : String → V.Value → Fault ⊎ Text
string message (V.string text) = inj₂ text
string message _ = inj₁ (fault [] malformedInput message)

array : String → V.Value → Fault ⊎ List V.Value
array message (V.array values) = inj₂ values
array message _ = inj₁ (fault [] malformedInput message)

nonempty : ∀ {A : Set} → List A → Bool
nonempty [] = false
nonempty (_ ∷ _) = true

IdentityValid : Q.Call → Set
IdentityValid request = Nonempty (Q.Call.identity request)

checkIdentity : ∀ request → Checked (IdentityValid request)
checkIdentity request = check (fault [] emptyText "provider call ID is empty") (nonempty? (Q.Call.identity request))

Valid : List Q.Call → Set
Valid calls = All IdentityValid calls × Provider.IDs.Unique (map Q.Call.identity calls)

checkCalls : ∀ calls → Checked (Valid calls)
checkCalls calls = combine (allChecked checkIdentity calls) (Provider.IDs.checkUnique (map Q.Call.identity calls))

record Reply : Set where
  constructor reply
  field
    replay : List V.Value
    calls : List Q.Call
    valid : Valid calls

anthropicReplay : List V.Value → List V.Value
anthropicReplay content =
  V.object ((toList "role" , V.string (toList "assistant")) ∷ (toList "content" , V.array content) ∷ []) ∷ []

finish : ∀ replay calls → Fault ⊎ Reply
finish replay calls = result (checkCalls calls) >>= λ valid → inj₂ (reply replay calls valid)

finishPreserves : ∀ replay calls response → finish replay calls ≡ inj₂ response →
  Reply.replay response ≡ replay × Reply.calls response ≡ calls
finishPreserves replay calls response observed with checkCalls calls
... | rejected failure invalid with observed
...   | ()
finishPreserves replay calls .(reply replay calls valid) refl | accepted valid = refl , refl

-- Envelope validation is atomic: history and pending calls are published
-- together only after every item and final stop condition has been checked.
record State : Set where
  constructor state
  field history : List V.Value; pending : List Q.Call

commit : State → Fault ⊎ Reply → Fault ⊎ State
commit before (inj₁ failure) = inj₁ failure
commit before (inj₂ response) = inj₂ (state (State.history before ++ Reply.replay response) (Reply.calls response))

failureCannotPublish : ∀ before failure → commit before (inj₁ failure) ≡ inj₁ failure
failureCannotPublish before failure = refl

module Decode (arguments : Text → Fault ⊎ V.Value) where
  encodedArguments : V.Value → Fault ⊎ V.Value
  encodedArguments (V.string text) = arguments text
  encodedArguments _ = inj₁ (fault [] malformedInput "function arguments must be JSON text")

  objectArguments : V.Value → Fault ⊎ V.Value
  objectArguments value@(V.object fields) = inj₂ value
  objectArguments _ = inj₁ (fault [] malformedInput "tool input must be a JSON object")

  chatArguments : Bool → V.Value → Fault ⊎ V.Value
  chatArguments allowObject (V.string text) = arguments text
  chatArguments true value@(V.object fields) = inj₂ value
  chatArguments allowObject _ = inj₁ (fault [] malformedInput "function arguments must be JSON text")

  makeCall : Text → Text → Fault ⊎ V.Value → Fault ⊎ (Maybe Q.Call)
  makeCall identity name parsed =
    result (checkIdentity (Q.call identity name parsed)) >>= λ valid → inj₂ (just (Q.call identity name parsed))

  makeCallPreserves : ∀ identity name parsed request → makeCall identity name parsed ≡ inj₂ (just request) →
    Q.Call.identity request ≡ identity × (Q.Call.name request ≡ name × Q.Call.arguments request ≡ parsed)
  makeCallPreserves identity name parsed request observed with checkIdentity (Q.call identity name parsed)
  ... | rejected failure invalid with observed
  ...   | ()
  makeCallPreserves identity name parsed .(Q.call identity name parsed) refl | accepted valid = refl , refl , refl

  malformedArgumentsRetainCall : ∀ identity name failure →
    IdentityValid (Q.call identity name (inj₁ failure)) →
    makeCall identity name (inj₁ failure) ≡ inj₂ (just (Q.call identity name (inj₁ failure)))
  malformedArgumentsRetainCall identity name failure valid with checkIdentity (Q.call identity name (inj₁ failure))
  ... | accepted proof = refl
  ... | rejected faultValue invalid = Data.Empty.⊥-elim (invalid valid)

  argumentFailureDeliveredExactly : ∀ identity name failure →
    Q.Call.arguments (Q.call identity name (inj₁ failure)) ≡ inj₁ failure
  argumentFailureDeliveredExactly identity name failure = refl

  openaiItem : V.Value → Fault ⊎ Maybe Q.Call
  openaiItem item = ensure (isNull (get "status" item) ∨ isText "completed" (get "status" item))
    "incomplete OpenAI output item" >>= λ _ → classify (get "type" item)
    where
    classify : V.Value → Fault ⊎ Maybe Q.Call
    classify kind with isText "function_call" kind
    ... | true = string "missing OpenAI call ID" (get "call_id" item) >>= λ identity →
      string "missing OpenAI function name" (get "name" item) >>= λ name →
      makeCall identity name (encodedArguments (get "arguments" item))
    ... | false with isText "reasoning" kind ∨ isText "message" kind
    ...   | true = inj₂ nothing
    ...   | false = inj₁ (fault [] malformedInput "unexpected OpenAI output item")

  anthropicItem : V.Value → Fault ⊎ Maybe Q.Call
  anthropicItem item with isText "tool_use" (get "type" item)
  ... | true = string "missing Anthropic tool ID" (get "id" item) >>= λ identity →
    string "missing Anthropic tool name" (get "name" item) >>= λ name →
    makeCall identity name (objectArguments (get "input" item))
  ... | false with isText "thinking" (get "type" item)
  ...   | true = ensure (isString (get "thinking" item)) "invalid Anthropic thinking block" >>= λ _ →
    ensure (isString (get "signature" item)) "invalid Anthropic thinking block" >>= λ _ → inj₂ nothing
  ...   | false with isText "redacted_thinking" (get "type" item)
  ...     | true = ensure (isString (get "data" item)) "invalid Anthropic reasoning block" >>= λ _ → inj₂ nothing
  ...     | false with isText "text" (get "type" item)
  ...       | true = inj₂ nothing
  ...       | false = inj₁ (fault [] malformedInput "unexpected Anthropic content block")

  chatItem : Bool → V.Value → Fault ⊎ Maybe Q.Call
  chatItem allowObject item = string "missing chat call ID" (get "id" item) >>= λ identity →
    string "missing chat function name" (get "name" (get "function" item)) >>= λ name →
    ensure (isText "function" (get "type" item)) "invalid chat function call" >>= λ _ →
    result (check (fault [] emptyText "invalid chat function call") (nonempty? name)) >>= λ _ →
    makeCall identity name (chatArguments allowObject (get "arguments" (get "function" item)))

  collect : (V.Value → Fault ⊎ Maybe Q.Call) → List Text → List V.Value → Fault ⊎ List Q.Call
  collect read seen [] = inj₂ []
  collect read seen (item ∷ rest) = read item >>= λ where
    nothing → collect read seen rest
    (just request) → result (check (fault [] duplicate "duplicate provider call ID")
      (Provider.IDs.absent? (Q.Call.identity request) seen)) >>= λ _ →
      mapResult (request ∷_) (collect read (Q.Call.identity request ∷ seen) rest)

  openai : V.Value → Fault ⊎ Reply
  openai input = ensure (isText "completed" (get "status" input)) "OpenAI response is incomplete" >>= λ _ →
    array "invalid OpenAI output" (get "output" input) >>= λ output →
    collect openaiItem [] output >>= λ calls → finish output calls

  stopReason : ∀ {A : Set} → String → String → String → V.Value → List A → Fault ⊎ ⊤
  stopReason toolStop finishedStop message reason calls with isText toolStop reason
  ... | true = ensure (nonempty calls) message
  ... | false with isText finishedStop reason
  ...   | true = ensure (not (nonempty calls)) message
  ...   | false = inj₁ (fault [] malformedInput message)

  anthropic : V.Value → Fault ⊎ Reply
  anthropic input =
    array "invalid Anthropic content" (get "content" input) >>= λ content →
    collect anthropicItem [] content >>= λ calls →
    stopReason "tool_use" "end_turn" "Anthropic response is incomplete" (get "stop_reason" input) calls >>= λ _ →
    finish (anthropicReplay content) calls

  rawChatCalls : V.Value → Fault ⊎ List V.Value
  rawChatCalls V.null = inj₂ []
  rawChatCalls (V.array calls) = inj₂ calls
  rawChatCalls _ = inj₁ (fault [] malformedInput "invalid chat tool calls")

  onlyChoice : List V.Value → Fault ⊎ V.Value
  onlyChoice (choice ∷ []) = inj₂ choice
  onlyChoice _ = inj₁ (fault [] malformedInput "invalid chat choice count")

  chatChoice : V.Value → Fault ⊎ V.Value
  chatChoice input = array "invalid chat choices" (get "choices" input) >>= onlyChoice

  chat : (allowObject : Bool) → V.Value → Fault ⊎ Reply
  chat allowObject input =
    chatChoice input >>= λ choice →
    let message = get "message" choice in
    ensure (isText "assistant" (get "role" message)) "invalid chat assistant message" >>= λ _ →
    ensure (isObject message) "invalid chat assistant message" >>= λ _ →
    rawChatCalls (get "tool_calls" message) >>= λ rawCalls →
    stopReason "tool_calls" "stop" "chat response is incomplete" (get "finish_reason" choice) rawCalls >>= λ _ →
    collect (chatItem allowObject) [] rawCalls >>= λ calls →
    finish (message ∷ []) calls

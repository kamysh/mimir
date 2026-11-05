{-# OPTIONS --safe #-}
-- Native provider transport and conversation state around the already checked
-- provider response/replay contracts. Pending calls are consumed before a new
-- HTTP request; every result is paired with the outstanding provider call ID.
module Mimir.JudgeAPIAdapter where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_; _++_; map; any; length; reverse; dropWhileᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤?_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.RecordDecoding using (_>>=_; readArray)
import Mimir.StructuredValue as V
import Mimir.PublicEncoding as Encoding
import Mimir.PublicInput as Input
import Mimir.Validation as Validation
import Mimir.StandardLibrary as Conversion
import Mimir.JudgeConfiguration as Config
import Mimir.JudgeHarnessAdapter as Harness
import Mimir.JudgeRevision as Revision
import Mimir.JudgeJSON as JSONDependency
import Mimir.JudgePrompt as Prompt
import Mimir.ProviderArguments as ArgumentsDependency
import Mimir.ProviderResponse as Response
import Mimir.ReviewObservation as Observation
import Mimir.ExperienceSchema as Experience
import Mimir.SourceFailure as Source
import Mimir.Binary64
import Mimir.CompleteBytes as Body
import Mimir.Effects as Effects
import Data.Char as Char

module Q = Response.Q

data Wire : Set where responses anthropic chat : Wire

data TransportFailure : Set where transportTimeout transportFailure : TransportFailure

record Endpoint : Set where
  constructor endpointValue
  field wire : Wire; base suffix : Text

preset : Config.Provider → Endpoint
preset Config.openai = endpointValue responses (toList "https://api.openai.com/v1") (toList "responses")
preset Config.anthropic = endpointValue anthropic (toList "https://api.anthropic.com/v1") (toList "messages")
preset Config.openrouter = endpointValue chat (toList "https://openrouter.ai/api/v1") (toList "chat/completions")
preset Config.deepseek = endpointValue chat (toList "https://api.deepseek.com") (toList "chat/completions")
preset Config.zai = endpointValue chat (toList "https://api.z.ai/api/paas/v4") (toList "chat/completions")
preset Config.gemini = endpointValue chat (toList "https://generativelanguage.googleapis.com/v1beta/openai") (toList "chat/completions")
preset Config.compatible = endpointValue chat [] (toList "chat/completions")

trimSlash : Text → Text
trimSlash text = reverse (dropWhileᵇ (λ c → does (c Char.≟ '/')) (reverse text))

url : Config.Llm → Config.Provider → Text
url config provider = trimSlash base ++ toList "/" ++ Endpoint.suffix (preset provider)
  where
  base : Text
  base with Config.Llm.baseURL config
  ... | nothing = Endpoint.base (preset provider)
  ... | just custom = custom

record Call : Set where
  constructor call
  field identity name : Text; arguments : Source.Failure ⊎ V.Value

callAction : Call → Revision.Action
callAction request with Call.arguments request
... | inj₁ source = Revision.malformedTool (Call.name request) source
... | inj₂ arguments = Revision.tool (Call.name request) arguments

record Adapter : Set where
  constructor adapter
  field selectedID : Maybe ℕ; history : List V.Value; pending : List Call
        awaiting : Maybe Text; results : List V.Value; nativeOutputMaximum : Maybe ℕ

initial : Adapter
initial = adapter nothing [] [] nothing [] nothing

willCallModel : Adapter → ℕ → Bool
willCallModel state identity with Harness.same (Adapter.selectedID state) identity | Adapter.pending state
... | false | _ = true
... | true | [] = true
... | true | _ ∷ _ = false

get : String → V.Value → V.Value
get name value with Input.view value (toList name)
... | nothing = V.null
... | just value = value

array : V.Value → List V.Value
array (V.array entries) = entries
array _ = []

find : String → Text → List V.Value → V.Value
find key id [] = V.null
find key id (value ∷ rest) with get key value
... | V.string name with does (name ≟Text id)
...   | true = value
...   | false = find key id rest
find key id (_ ∷ rest) | _ = find key id rest

argumentSource : Wire → Text → V.Value → V.Value
argumentSource responses id raw = get "arguments" (find "call_id" id (array (get "output" raw)))
argumentSource anthropic id raw = get "input" (find "id" id (array (get "content" raw)))
argumentSource chat id raw with array (get "choices" raw)
... | [] = V.null
... | choice ∷ _ = get "arguments" (get "function" (find "id" id (array (get "tool_calls" (get "message" choice)))))

argumentStage : Wire → Text
argumentStage responses = toList "invalid OpenAI function arguments"
argumentStage anthropic = toList "invalid Anthropic tool arguments"
argumentStage chat = toList "invalid chat function arguments"

module Run (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (libraries : Harness.Libraries) (config : Config.Llm) (provider : Config.Provider)
  (selected : Observation.Snapshot) (tools : List V.Value) where
  module Arguments = ArgumentsDependency conversion
  module JSON = JSONDependency conversion
  module Encode = Encoding.Encode format
  display = Harness.Libraries.display libraries
  json = Revision.Display.json display
  encode = Revision.Display.bytes display
  wire = Endpoint.wire (preset provider)
  source = Observation.Snapshot.experience selected
  identity = Experience.Experience.identity source

  instructions : Text
  instructions = toList "Review only this pinned experience. Use the supplied functions for evidence and review; never claim database completion in text. " ++
    Prompt.guidance json source ++ toList " The host enforces project " ++ Experience.Experience.project source ++
    toList ", experience " ++ Encoding.Formatting.uuidText format identity ++ toList ", source revision " ++
    Harness.Libraries.integer libraries (Observation.Snapshot.revision selected) ++ toList ", and review revision " ++
    Harness.Libraries.integer libraries (Observation.Snapshot.reviewRevision selected) ++ toList ". Stop after the review is submitted."

  initialHistory : Wire → List V.Value
  initialHistory responses = Encoding.object (("role" , V.string (toList "user")) ∷
    ("content" , V.string (json (Encode.snapshot selected))) ∷ []) ∷ []
  initialHistory anthropic = Encoding.object (("role" , V.string (toList "user")) ∷ ("content" , V.array
    (Encoding.object (("type" , V.string (toList "text")) ∷ ("text" , V.string (json (Encode.snapshot selected))) ∷ []) ∷ [])) ∷ []) ∷ []
  initialHistory chat = Encoding.object (("role" , V.string (toList "system")) ∷ ("content" , V.string instructions) ∷ []) ∷
    initialHistory responses

  reset : Adapter → Adapter
  reset state with Harness.same (Adapter.selectedID state) identity
  ... | true = state
  ... | false = adapter (just identity) (initialHistory wire) [] nothing [] (Adapter.nativeOutputMaximum state)

  resultMessage : Wire → Text → V.Value → V.Value
  resultMessage responses id result = Encoding.object (("type" , V.string (toList "function_call_output")) ∷
    ("call_id" , V.string id) ∷ ("output" , V.string (json result)) ∷ [])
  resultMessage anthropic id result = Encoding.object (("type" , V.string (toList "tool_result")) ∷
    ("tool_use_id" , V.string id) ∷ ("content" , V.string (json result)) ∷ [])
  resultMessage chat id result = Encoding.object (("role" , V.string (toList "tool")) ∷
    ("tool_call_id" , V.string id) ∷ ("content" , V.string (json result)) ∷ [])

  flush : Adapter → Wire → Adapter
  flush state wire with Adapter.results state
  ... | [] = state
  flush state anthropic | entries@(_ ∷ _) = record state
    { history = Adapter.history state ++ (Encoding.object (("role" , V.string (toList "user")) ∷
        ("content" , V.array entries) ∷ []) ∷ []) ; results = [] }
  flush state _ | entries@(_ ∷ _) = record state { history = Adapter.history state ++ entries ; results = [] }

  definition : Wire → V.Value → Validation.Fault ⊎ V.Value
  definition wire raw = Input.required "name" V.asString (Input.view raw) >>= λ name →
    Input.required "inputSchema" V.asObject (Input.view raw) >>= λ fields →
    inj₂ (build wire name (V.object fields) (Input.loose "description" [] V.asString (Input.view raw)))
    where
    build : Wire → Text → V.Value → Text → V.Value
    build responses name schema description = Encoding.object
      (("type" , V.string (toList "function")) ∷ ("name" , V.string name) ∷ ("description" , V.string description) ∷
       ("parameters" , schema) ∷ ("strict" , V.boolean false) ∷ [])
    build anthropic name schema description = Encoding.object
      (("name" , V.string name) ∷ ("description" , V.string description) ∷ ("input_schema" , schema) ∷ [])
    build chat name schema description = Encoding.object (("type" , V.string (toList "function")) ∷
      ("function" , Encoding.object (("name" , V.string name) ∷ ("description" , V.string description) ∷ ("parameters" , schema) ∷ [])) ∷ [])

  router : Config.Provider → List (String × V.Value)
  router Config.openrouter = ("provider" , Encoding.object
    (("allow_fallbacks" , V.boolean false) ∷ ("require_parameters" , V.boolean true) ∷ [])) ∷ []
  router _ = []

  body : Adapter → List V.Value → Wire → V.Value
  body state definitions responses = Encoding.object (("model" , V.string (Config.Llm.model config)) ∷
    ("instructions" , V.string instructions) ∷ ("input" , V.array (Adapter.history state)) ∷ ("tools" , V.array definitions) ∷
    ("parallel_tool_calls" , V.boolean true) ∷ ("store" , V.boolean false) ∷
    ("truncation" , V.string (toList "disabled")) ∷ [])
  body state definitions anthropic = Encoding.object ((("model" , V.string (Config.Llm.model config)) ∷
    ("system" , V.string instructions) ∷ ("messages" , V.array (Adapter.history state)) ∷ ("tools" , V.array definitions) ∷ []) ++
    nativeTokens (Adapter.nativeOutputMaximum state))
    where
    nativeTokens : Maybe ℕ → List (String × V.Value)
    nativeTokens nothing = []
    nativeTokens (just maximum) = ("max_tokens" , V.unsigned maximum) ∷ []
  body state definitions chat = Encoding.object ((("model" , V.string (Config.Llm.model config)) ∷
    ("messages" , V.array (Adapter.history state)) ∷ ("tools" , V.array definitions) ∷
    ("stream" , V.boolean false) ∷ []) ++ router provider)

  rawSource : Wire → V.Value → Validation.Fault → Source.Failure
  rawSource wire raw failure = Source.Current.input conversion (argumentStage wire) (encode raw) (Revision.Display.fault display failure)

  textSource : Wire → Text → Validation.Fault → Source.Failure
  textSource wire text failure with JSON.text (argumentStage wire) text
  ... | inj₁ error with Revision.Error.source error
  ...   | just captured = captured
  ...   | nothing = rawSource wire (V.string text) failure
  textSource wire text failure | inj₂ _ = rawSource wire (V.string text) failure

  argumentFailure : Wire → V.Value → Validation.Fault → Source.Failure
  argumentFailure anthropic raw failure = rawSource anthropic raw failure
  argumentFailure responses (V.string text) failure = textSource responses text failure
  argumentFailure chat (V.string text) failure = textSource chat text failure
  argumentFailure wire raw failure = rawSource wire raw failure

  materialize : V.Value → Q.Call → Call
  materialize raw request with Q.Call.arguments request
  ... | inj₂ value = call (Q.Call.identity request) (Q.Call.name request) (inj₂ value)
  ... | inj₁ failure = call (Q.Call.identity request) (Q.Call.name request)
      (inj₁ (argumentFailure wire (argumentSource wire (Q.Call.identity request) raw) failure))

  allowObject : Config.Provider → Bool
  allowObject Config.zai = true
  allowObject _ = false

  parse : Wire → V.Value → Validation.Fault ⊎ Response.Reply
  parse responses = Arguments.Providers.openai
  parse anthropic = Arguments.Providers.anthropic
  parse chat = Arguments.Providers.chat (allowObject provider)

  classify : ℕ → List Byte → Text
  classify status bytes = reason status code
    where
    code : Maybe Text
    code with JSON.read [] bytes
    ... | inj₁ _ = nothing
    ... | inj₂ value with get "code" (get "error" value)
    ...   | V.string code = just code
    ...   | _ = nothing
    contains : String → Maybe Text → Bool
    contains _ nothing = false
    contains part (just code) = Harness.Libraries.contains libraries code (toList part)
    rejected : Maybe Text → Text
    rejected code with contains "model" code
    ... | true = toList "provider model is unsupported"
    ... | false with contains "tool" code ∨ contains "function" code ∨ contains "unsupported_parameter" code
    ...   | true = toList "provider model or requested tools are unsupported"
    ...   | false = toList "provider rejected request"
    matches : ℕ → List ℕ → Bool
    matches status = any (λ candidate → does (status ≟ candidate))
    quota : Maybe Text → Bool
    quota nothing = false
    quota (just code) = does (code ≟Text toList "insufficient_quota")
    reason : ℕ → Maybe Text → Text
    reason status code with matches status (401 ∷ 403 ∷ [])
    ... | true = toList "provider authentication failed"
    ... | false with does (status ≟ 402) ∨ (does (status ≟ 429) ∧ quota code)
    ...   | true = toList "provider quota exhausted"
    ...   | false with does (status ≟ 429)
    ...     | true = toList "provider rate limit reached"
    ...     | false with matches status (400 ∷ 404 ∷ 422 ∷ [])
    ...       | true = rejected code
    ...       | false with matches status (408 ∷ 504 ∷ [])
    ...         | true = toList "provider request timed out"
    ...         | false with Config.between 500 599 status
    ...           | true = toList "provider service failed"
    ...           | false = toList "provider request failed"

  record Outcome : Set where
    constructor outcome
    field state : Adapter; answer : Revision.Error ⊎ Revision.Action

  data Effect : Set where
    headerValid : Text → Effect
    post : Text → List (Text × Text) → V.Value → Effect
    modelMetadata : Effect
    readChunk : ℕ → Effect
  Reply : Effect → Set
  Reply (headerValid _) = Bool
  Reply (post url headers body) = TransportFailure ⊎ (ℕ × ℕ)
  Reply modelMetadata = Revision.Error ⊎ V.Value
  Reply (readChunk handle) = Body.Input
  module P = Effects.Protocol Effect Reply
  open P using (Script; ask; done) renaming (_>>=_ to _then_)

  data State : Set where
    receiving : Adapter → ℕ → ℕ → Body.State → State
    executing : Adapter → Script State → State
    finished : Outcome → State

  failure : Adapter → Text → State
  failure state detail = finished (outcome state (inj₁ (Revision.error detail nothing)))

  yield : Adapter → State
  yield state with Adapter.pending state
  ... | [] = finished (outcome state (inj₂ Revision.modelDone))
  ... | current ∷ rest = finished (outcome (record state { pending = rest ; awaiting = just (Call.identity current) })
      (inj₂ (callAction current)))

  afterJSON : Adapter → V.Value → State
  afterJSON state raw with parse wire raw
  ... | inj₁ fault = failure state (Revision.Display.fault display fault)
  ... | inj₂ response = yield (record state
      { history = Adapter.history state ++ Response.Reply.replay response
      ; pending = map (materialize raw) (Response.Reply.calls response) })

  afterBody : Adapter → ℕ → List Byte → State
  afterBody state status bytes with Config.between 200 299 status
  ... | false = failure state (classify status bytes)
  ... | true with JSON.read (toList "invalid provider JSON") bytes
  ...   | inj₁ error = finished (outcome state (inj₁ error))
  ...   | inj₂ value = afterJSON state value

  headers : Wire → Text → List (Text × Text)
  headers responses key = (toList "Authorization" , (toList "Bearer " ++ key)) ∷ []
  headers chat key = headers responses key
  headers anthropic key = (toList "x-api-key" , key) ∷ (toList "anthropic-version" , toList "2023-06-01") ∷ []

  send : Adapter → V.Value → Text → Script State
  send state request key = ask (post (url config provider) (headers wire key) request) λ where
    (inj₁ transportTimeout) → done (failure state (toList "provider request timed out"))
    (inj₁ transportFailure) → done (failure state (toList "provider transport failed"))
    (inj₂ (handle , status)) → done (receiving state handle status Body.begin)

  withKey : Adapter → V.Value → Wire → Maybe Text → Script State
  withKey state request wire nothing = done (failure state (toList "missing API key"))
  withKey state request anthropic (just key) = ask (headerValid key) λ where
    false → done (failure state (toList "invalid API key header"))
    true → send state request key
  withKey state request _ (just key) = send state request key

  preparedRequest : Adapter → State
  preparedRequest state with readArray (definition wire) (V.array tools)
  ... | inj₁ fault = failure state (Revision.Display.fault display fault)
  ... | inj₂ definitions = executing state (withKey state (body state definitions wire) wire (Config.Llm.apiKey config))

  afterMetadata : Adapter → Revision.Error ⊎ V.Value → State
  afterMetadata state (inj₁ error) = finished (outcome state (inj₁ error))
  afterMetadata state (inj₂ raw) with Input.unsigned (Mimir.Binary64.powerMinusOne 64) (get "max_tokens" raw)
  ... | inj₁ _ = failure state (toList "Anthropic model metadata is missing max_tokens")
  ... | inj₂ maximum with does (1 ≤? maximum)
  ...   | false = failure state (toList "Anthropic model metadata has invalid max_tokens")
  ...   | true = preparedRequest (record state { nativeOutputMaximum = just maximum })

  request : Adapter → State
  request state with wire | Adapter.nativeOutputMaximum state
  ... | anthropic | nothing = executing state (ask modelMetadata (λ reply → done (afterMetadata state reply)))
  ... | _ | _ = preparedRequest state

  nextCall : Adapter → State
  nextCall state with Adapter.pending state
  ... | [] = request (flush state wire)
  ... | _ ∷ _ = yield state

  acceptFeedback : Adapter → Maybe Text → Maybe V.Value → State
  acceptFeedback state nothing nothing = nextCall state
  acceptFeedback state (just id) (just result) = nextCall (record state
    { results = Adapter.results state ++ (resultMessage wire id result ∷ []) })
  acceptFeedback state _ _ = failure state (toList "provider tool result sequence is invalid")

  start : Adapter → Maybe V.Value → State
  start state feedback = acceptFeedback (record current { awaiting = nothing }) (Adapter.awaiting current) feedback
    where current = reset state

  currentAdapter : State → Adapter
  currentAdapter (receiving state _ _ _) = state
  currentAdapter (executing state _) = state
  currentAdapter (finished result) = Outcome.state result

  data Step : Set where
    internal : State → Step
    external : (effect : Effect) → (Reply effect → State) → Step
    stopped : Outcome → Step
  next : State → Step
  next (receiving state handle status (Body.receiving buffer)) = external (readChunk handle)
    (λ input → receiving state handle status (Body.step (Body.receiving buffer) input))
  next (receiving state handle status (Body.complete buffer)) = internal (afterBody state status (Body.Buffer.bytes buffer))
  next (receiving state handle status (Body.failed Body.transport)) = internal (failure state (toList "provider body failed"))
  next (executing saved (done state)) = internal state
  next (executing saved (ask effect k)) = external effect (λ reply → executing saved (k reply))
  next (finished result) = stopped result

  data Transition : State → Maybe P.Event → State → Set where
    internalStep : ∀ {before after} → next before ≡ internal after → Transition before nothing after
    externalStep : ∀ {before effect k} → next before ≡ external effect k →
      (reply : Reply effect) → Transition before (just (effect , reply)) (k reply)
  data Trace : State → List (Maybe P.Event) → State → Set where
    empty : ∀ {state} → Trace state [] state
    step : ∀ {before middle after event events} → Transition before event middle →
      Trace middle events after → Trace before (event ∷ events) after

  yieldedIdentity : ∀ state current rest → Adapter.pending state ≡ current ∷ rest →
    yield state ≡ finished (outcome (record state { pending = rest ; awaiting = just (Call.identity current) })
      (inj₂ (callAction current)))
  yieldedIdentity state current rest pending rewrite pending = refl

module Construction (config : Config.Llm) where
  data Effect : Set where buildHTTPClient : Bool → Effect
  Reply : Effect → Set
  Reply _ = Text ⊎ ⊤
  module P = Effects.Protocol Effect Reply
  open P using (Script; done; ask)

  record Ready : Set where
    constructor ready
    field provider : Config.Provider; endpoint : Text; wire : Wire

  Result = Text ⊎ Maybe Ready

  build : Config.Provider → Script Result
  build provider = ask (buildHTTPClient false) λ where
    (inj₁ _) → done (inj₁ (toList "unable to initialize API transport"))
    (inj₂ tt) → done (inj₂ (just (ready provider (url config provider) (Endpoint.wire (preset provider)))))

  router : Config.Provider → Script Result
  router Config.openrouter with does (Config.Llm.model config ≟Text toList "auto") ∨
    does (Config.Llm.model config ≟Text toList "openrouter/auto")
  ... | true = done (inj₁ (toList "OpenRouter requires a specific model"))
  ... | false = build Config.openrouter
  router provider = build provider

  custom : Config.Provider → Script Result
  custom Config.compatible with Config.Llm.baseURL config
  ... | nothing = done (inj₁ (toList "llm.base_url is required for openai-compatible"))
  ... | just _ = router Config.compatible
  custom provider = router provider

  select : Maybe Config.Provider → Script Result
  select nothing = done (inj₂ nothing)
  select (just provider) = custom provider

  start : Script Result
  start with Config.Llm.backend config
  ... | Config.api = select (Config.Llm.provider config)
  ... | _ = done (inj₁ (toList "API backend requires llm.backend=api"))

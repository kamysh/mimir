{-# OPTIONS --safe #-}
-- Client extraction from normalized JSON. Missing and explicit null fields
-- remain distinct; application errors retain the original server value.
import Mimir.StandardLibrary
module Mimir.McpClientWire (library : Mimir.StandardLibrary.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault; fault; malformedInput; Checked; accepted; rejected)
import Mimir.StructuredValue as V
import Mimir.RpcReply as RPC
import Mimir.Binary64 as Binary
import Mimir.ProviderResponse as Fields
import Mimir.ProviderArguments as JSONDependency
private
  module JSON = JSONDependency library
import Mimir.Bits as Bits

module Replies = RPC.Replies V.Value V.Value

lookup : String → V.Value → Maybe V.Value
lookup name (V.object fields) = V.Object.normalize fields (toList name)
lookup name _ = nothing

text : Maybe V.Value → Maybe Text
text (just (V.string value)) = just value
text _ = nothing

numberID : V.Value → RPC.Identifier
numberID raw with V.uint (Binary.powerMinusOne 64) raw
... | accepted (n , representation) = RPC.integer n
... | rejected failure invalid = RPC.invalid

identifier : Maybe V.Value → RPC.Identifier
identifier nothing = RPC.absent
identifier (just V.null) = RPC.null
identifier (just (V.string value)) = RPC.string value
identifier (just raw) = numberID raw

extract : V.Value → Replies.Envelope
extract raw = Replies.envelope (text (lookup "jsonrpc" raw)) (text (lookup "method" raw))
  (identifier (lookup "id" raw)) (lookup "error" raw) (lookup "result" raw)

receive : ℕ → ℕ → V.Value → Replies.Outcome
receive expected notifications raw = Replies.receive expected notifications (extract raw)

missingIDIsNotificationCandidate : ∀ raw → lookup "id" raw ≡ nothing →
  Replies.Envelope.id (extract raw) ≡ RPC.absent
missingIDIsNotificationCandidate raw missing rewrite missing = refl

explicitNullIsResponseID : ∀ raw → lookup "id" raw ≡ just V.null →
  Replies.Envelope.id (extract raw) ≡ RPC.null
explicitNullIsResponseID raw explicit rewrite explicit = refl

unsignedIDPreserved : ∀ n → n ≤ Binary.powerMinusOne 64 → numberID (V.unsigned n) ≡ RPC.integer n
unsignedIDPreserved n bounded with n ≤? Binary.powerMinusOne 64
... | yes fits = refl
... | no outside = ⊥-elim (outside bounded)

errorFieldPreserved : ∀ raw → Replies.Envelope.error (extract raw) ≡ lookup "error" raw
errorFieldPreserved raw = refl

resultFieldPreserved : ∀ raw → Replies.Envelope.result (extract raw) ≡ lookup "result" raw
resultFieldPreserved raw = refl

presentErrorWins : ∀ raw failure → lookup "error" raw ≡ just failure →
  Replies.responseBody (Replies.Envelope.error (extract raw)) (Replies.Envelope.result (extract raw)) ≡
  Replies.rejected failure
presentErrorWins raw failure present rewrite present = refl

-- Tool content is a second JSON document. Keep application refusal,
-- malformed envelope and malformed embedded document distinguishable.
data ToolResult : Set where
  applicationFailure : V.Value → ToolResult
  invalidEnvelope : Fault → ToolResult
  invalidJSON : Text → Fault → ToolResult
  toolValue : Text → V.Value → ToolResult

parsedTool : Text → Fault ⊎ V.Value → ToolResult
parsedTool source (inj₁ failure) = invalidJSON source failure
parsedTool source (inj₂ value) = toolValue source value

parseTool : Text → ToolResult
parseTool source = parsedTool source (JSON.decode source)

readText : V.Value → ToolResult
readText (V.string source) = parseTool source
readText _ = invalidEnvelope (fault [] malformedInput "invalid MCP tool text")

readItem : V.Value → ToolResult
readItem raw with Fields.isText "text" (Fields.get "type" raw)
... | false = invalidEnvelope (fault [] malformedInput "invalid MCP tool content")
... | true = readText (Fields.get "text" raw)

readContent : V.Value → ToolResult
readContent (V.array (item ∷ [])) = readItem item
readContent (V.array _) = invalidEnvelope (fault [] malformedInput "invalid MCP tool content")
readContent _ = invalidEnvelope (fault [] malformedInput "invalid MCP tool result")

markedError : V.Value → Bool
markedError (V.boolean true) = true
markedError _ = false

tool : V.Value → ToolResult
tool raw with markedError (Fields.get "isError" raw)
... | true = applicationFailure raw
... | false = readContent (Fields.get "content" raw)

parseFailurePreserved : ∀ source failure → JSON.decode source ≡ inj₁ failure →
  parseTool source ≡ invalidJSON source failure
parseFailurePreserved source failure failed rewrite failed = refl

parseValuePreserved : ∀ source value → JSON.decode source ≡ inj₂ value →
  parseTool source ≡ toolValue source value
parseValuePreserved source value parsed rewrite parsed = refl

markedFailurePreserved : ∀ raw → markedError (Fields.get "isError" raw) ≡ true →
  tool raw ≡ applicationFailure raw
markedFailurePreserved raw marked rewrite marked = refl

record ContentEvidence (raw : V.Value) (source : Text) (value : V.Value) : Set where
  constructor contentEvidence
  field
    item : V.Value
    singleton : Fields.get "content" raw ≡ V.array (item ∷ [])
    textKind : Fields.isText "text" (Fields.get "type" item) ≡ true
    exactText : Fields.get "text" item ≡ V.string source
    parsed : JSON.decode source ≡ inj₂ value

record ToolEvidence (raw : V.Value) (source : Text) (value : V.Value) : Set where
  constructor toolEvidence
  field
    notMarked : markedError (Fields.get "isError" raw) ≡ false
    content : ContentEvidence raw source value

parsedSound : ∀ source result supplied value → parsedTool source result ≡ toolValue supplied value →
  source ≡ supplied × result ≡ inj₂ value
parsedSound source (inj₁ failure) supplied value ()
parsedSound source (inj₂ value) .source .value refl = refl , refl

textSound : ∀ raw source value → readText raw ≡ toolValue source value →
  raw ≡ V.string source × JSON.decode source ≡ inj₂ value
textSound (V.string supplied) source value observed with parsedSound supplied (JSON.decode supplied) source value observed
... | refl , parsed = refl , parsed
textSound V.null source value ()
textSound (V.boolean b) source value ()
textSound (V.signed n) source value ()
textSound (V.unsigned n) source value ()
textSound (V.floating n) source value ()
textSound (V.array xs) source value ()
textSound (V.object xs) source value ()

itemSound : ∀ raw source value → readItem raw ≡ toolValue source value →
  Fields.isText "text" (Fields.get "type" raw) ≡ true ×
  (Fields.get "text" raw ≡ V.string source × JSON.decode source ≡ inj₂ value)
itemSound raw source value observed with Fields.isText "text" (Fields.get "type" raw) in kind
... | false with observed
...   | ()
itemSound raw source value observed | true = refl , textSound (Fields.get "text" raw) source value observed

contentSound : ∀ raw source value → readContent raw ≡ toolValue source value →
  Σ V.Value (λ item → raw ≡ V.array (item ∷ []) ×
    (Fields.isText "text" (Fields.get "type" item) ≡ true ×
    (Fields.get "text" item ≡ V.string source × JSON.decode source ≡ inj₂ value)))
contentSound (V.array (item ∷ [])) source value observed = item , refl , itemSound item source value observed
contentSound (V.array []) source value ()
contentSound (V.array (a ∷ b ∷ rest)) source value ()
contentSound V.null source value ()
contentSound (V.boolean b) source value ()
contentSound (V.string s) source value ()
contentSound (V.signed n) source value ()
contentSound (V.unsigned n) source value ()
contentSound (V.floating n) source value ()
contentSound (V.object xs) source value ()

toolSound : ∀ raw source value → tool raw ≡ toolValue source value → ToolEvidence raw source value
toolSound raw source value observed with markedError (Fields.get "isError" raw) in marked
... | true with observed
...   | ()
toolSound raw source value observed | false with contentSound (Fields.get "content" raw) source value observed
... | item , singleton , kind , exact , parsed = toolEvidence marked (contentEvidence item singleton kind exact parsed)

toolComplete : ∀ raw source value → ToolEvidence raw source value → tool raw ≡ toolValue source value
toolComplete raw source value (toolEvidence notMarked (contentEvidence item singleton kind exact parsed))
  rewrite notMarked | singleton | kind | exact | parsed = refl

line : List Bits.Byte → Fault ⊎ V.Value
line bytes = JSON.convert (Mimir.StandardLibrary.Contract.jsonValue library bytes)

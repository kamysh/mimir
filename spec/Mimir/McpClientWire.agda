{-# OPTIONS --safe #-}
-- Client extraction from normalized JSON. Missing and explicit null fields
-- remain distinct; application errors retain the original server value.
import Mimir.StandardLibrary
module Mimir.McpClientWire (library : Mimir.StandardLibrary.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation using (Fault; fault; problem; malformedInput)
import Mimir.StructuredValue as V
import Mimir.RpcReply as RPC
import Mimir.Bits as Bits

-- JSON decoding is supplied by the standard-library boundary.
private module JSON where
  convert : Mimir.StandardLibrary.JSONResult → Fault ⊎ V.Value
  convert (Mimir.StandardLibrary.parsed value) = inj₂ value
  convert (Mimir.StandardLibrary.rejected error) =
    inj₁ (problem [] malformedInput (Mimir.StandardLibrary.JSONError.message error))
  convert (Mimir.StandardLibrary.panicked message) = inj₁ (problem [] malformedInput message)

  decode : Text → Fault ⊎ V.Value
  decode value = convert (Mimir.StandardLibrary.Contract.jsonValue library
    (Mimir.StandardLibrary.Contract.encodeUTF8 library value))

module Replies = RPC.Replies V.Value V.Value

lookup : String → V.Value → Maybe V.Value
lookup name (V.object fields) = V.Object.normalize fields (toList name)
lookup name _ = nothing

get : String → V.Value → V.Value
get name raw with lookup name raw
... | nothing = V.null
... | just value = value

isText : String → V.Value → Bool
isText expected (V.string actual) with actual ≟Text toList expected
... | yes _ = true
... | no _ = false
isText expected _ = false

text : Maybe V.Value → Maybe Text
text (just (V.string value)) = just value
text _ = nothing

identifier : Maybe V.Value → RPC.Identifier
identifier nothing = RPC.absent
identifier (just V.null) = RPC.null
identifier (just (V.string value)) = RPC.string value
identifier (just raw) = RPC.invalid

extract : V.Value → Replies.Envelope
extract raw = Replies.envelope (text (lookup "jsonrpc" raw)) (text (lookup "method" raw))
  (identifier (lookup "id" raw)) (lookup "error" raw) (lookup "result" raw)

receive : Text → ℕ → V.Value → Replies.Outcome
receive expected notifications raw = Replies.receive expected notifications (extract raw)

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
readItem raw with isText "text" (get "type" raw)
... | false = invalidEnvelope (fault [] malformedInput "invalid MCP tool content")
... | true = readText (get "text" raw)

readContent : V.Value → ToolResult
readContent (V.array (item ∷ [])) = readItem item
readContent (V.array _) = invalidEnvelope (fault [] malformedInput "invalid MCP tool content")
readContent _ = invalidEnvelope (fault [] malformedInput "invalid MCP tool result")

markedError : V.Value → Bool
markedError (V.boolean true) = true
markedError _ = false

tool : V.Value → ToolResult
tool raw with markedError (get "isError" raw)
... | true = applicationFailure raw
... | false = readContent (get "content" raw)

line : List Bits.Byte → Fault ⊎ V.Value
line bytes = JSON.convert (Mimir.StandardLibrary.Contract.jsonValue library bytes)

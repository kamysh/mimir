{-# OPTIONS --safe #-}
-- Actual server-side extraction from serde_json::Value. Missing IDs suppress
-- replies after dispatch; explicit null IDs still receive replies. The current
-- server does not reject requests based on a jsonrpc version field.
module Mimir.McpEnvelope where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Properties as List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.String using (String; toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.StructuredValue as JSON
open import Mimir.Text public using (Text)
open import Mimir.SourceReview using (_≟Text_)

literal : String → Text
literal = toList

get : Text → JSON.Value → Maybe JSON.Value
get name (JSON.object fields) = JSON.Object.normalize fields name
get name _ = nothing

orDefault : JSON.Value → Maybe JSON.Value → JSON.Value
orDefault fallback nothing = fallback
orDefault fallback (just value) = value

asText : Maybe JSON.Value → Text
asText (just (JSON.string values)) = values
asText _ = []

record Identity : Set where
  constructor identity
  field reply : Bool; value : JSON.Value

identify : Maybe JSON.Value → Identity
identify nothing = identity false JSON.null
identify (just value) = identity true value

record Request : Set where
  constructor request
  field identityValue : Identity; method : Text; params : JSON.Value

extractFields : JSON.Object.View → Request
extractFields fields = request (identify (fields (literal "id")))
  (asText (fields (literal "method"))) (orDefault (JSON.object []) (fields (literal "params")))

extract : JSON.Value → Request
extract (JSON.object fields) = extractFields (JSON.Object.normalize fields)
extract _ = extractFields (λ _ → nothing)

data Command : Set where
  initialize listTools : Command
  callTool : Text → JSON.Value → Command
  unknownMethod : Text → Command

route : Text → JSON.Value → Command
route method params with method ≟Text literal "initialize"
... | yes matched = initialize
... | no other with method ≟Text literal "tools/list"
...   | yes matched = listTools
...   | no otherList with method ≟Text literal "tools/call"
...     | yes matched = callTool (asText (get (literal "name") params))
        (orDefault (JSON.object []) (get (literal "arguments") params))
...     | no otherCall = unknownMethod method

dispatch : Request → Command
dispatch value = route (Request.method value) (Request.params value)

respond : ∀ {Response : Set} → Identity → Response → Maybe Response
respond (identity false id) response = nothing
respond (identity true id) response = just response

identityDoesNotChangeDispatch : ∀ first second method params →
  dispatch (request first method params) ≡ dispatch (request second method params)
identityDoesNotChangeDispatch first second method params = refl

missingIDSuppressesOnlyResponse : ∀ {Response : Set} (response : Response) →
  respond (identify nothing) response ≡ nothing
missingIDSuppressesOnlyResponse response = refl

presentIDRetained : ∀ id → Identity.value (identify (just id)) ≡ id
presentIDRetained id = refl

explicitNullReplies : ∀ {Response : Set} (response : Response) →
  respond (identify (just JSON.null)) response ≡ just response
explicitNullReplies response = refl

missingParamsDefault : ∀ fallback → orDefault fallback nothing ≡ fallback
missingParamsDefault fallback = refl

presentParamsPreserved : ∀ value → orDefault (JSON.object []) (just value) ≡ value
presentParamsPreserved value = refl

lastIDRetained : ∀ id fields →
  Identity.value (Request.identityValue (extract (JSON.object
    (fields ++ ((literal "id" , id) ∷ []))))) ≡ id
lastIDRetained id fields rewrite JSON.Object.lastOccurrenceWins fields (literal "id") id = refl

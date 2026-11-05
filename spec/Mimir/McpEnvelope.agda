{-# OPTIONS --safe #-}
-- Actual server-side extraction from serde_json::Value. Missing IDs suppress
-- replies after dispatch; explicit null IDs still receive replies. The current
-- server does not reject requests based on a jsonrpc version field.
module Mimir.McpEnvelope where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (toℕ)
open import Data.List using (List; []; _∷_; map)
import Data.List.Properties as List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_,_)
open import Data.String using (String; toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.JsonStoredValue as JSON
import Mimir.UTF8Packet as Packet

Text = List ℕ

literal : String → Text
literal text = map toℕ (toList text)

get : Text → JSON.Value → Maybe JSON.Value
get name (JSON.object fields) = JSON.Map.lookup name fields
get name _ = nothing

orDefault : JSON.Value → Maybe JSON.Value → JSON.Value
orDefault fallback nothing = fallback
orDefault fallback (just value) = value

asText : Maybe JSON.Value → Text
asText (just (JSON.string values)) = map (λ scalar → Packet.codePoint (Packet.Scalar.raw scalar)) values
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

extract : JSON.Value → Request
extract value = request (identify (get (literal "id") value))
  (asText (get (literal "method") value))
  (orDefault (JSON.object []) (get (literal "params") value))

data Command : Set where
  initialize listTools : Command
  callTool : Text → JSON.Value → Command
  unknownMethod : Text → Command

route : Text → JSON.Value → Command
route method params with List.≡-dec _≟_ method (literal "initialize")
... | yes matched = initialize
... | no other with List.≡-dec _≟_ method (literal "tools/list")
...   | yes matched = listTools
...   | no otherList with List.≡-dec _≟_ method (literal "tools/call")
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
    (JSON.Map.insert (literal "id") id fields)))) ≡ id
lastIDRetained id fields rewrite JSON.Map.insertedLookup (literal "id") id fields = refl

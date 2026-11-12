{-# OPTIONS --safe #-}
-- One server exchange. Response delivery is an external boundary: a
-- completed transaction's result reaches the client.
module Mimir.McpExchange where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _++_)
open import Data.Integer using (ℤ; -[1+_])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Data.String using (toList)
import Mimir.StructuredValue as JSON
import Mimir.McpEnvelope as Envelope
import Mimir.Effects as Effects

data Payload : Set where
  initialized tools : Payload
  content : JSON.Value → Payload

data Response : Set where
  ok : JSON.Value → Payload → Response
  error : JSON.Value → ℤ → Text → Response

data Effect : Set where
  handleTool : Envelope.Identity → Envelope.Text → JSON.Value → Effect
  deliver : Response → Effect

Reply : Effect → Set
Reply (handleTool identityValue name args) = Text ⊎ JSON.Value
Reply (deliver response) = ⊤

module E = Effects.Protocol Effect Reply
open E public

data Outcome : Set where nextLine : Outcome

emit : Response → Script Outcome
emit response = ask (deliver response) (λ _ → done nextLine)

respond : Envelope.Identity → Response → Script Outcome
respond identityValue response with Envelope.Identity.reply identityValue
... | false = done nextLine
... | true = emit response

afterTool : Envelope.Identity → Text ⊎ JSON.Value → Script Outcome
afterTool identityValue (inj₁ message) = respond identityValue (error (Envelope.Identity.value identityValue) -[1+ 31999 ] message)
afterTool identityValue (inj₂ value) = respond identityValue (ok (Envelope.Identity.value identityValue) (content value))

dispatch : Envelope.Identity → Envelope.Command → Script Outcome
dispatch identityValue Envelope.initialize = respond identityValue (ok (Envelope.Identity.value identityValue) initialized)
dispatch identityValue Envelope.listTools = respond identityValue (ok (Envelope.Identity.value identityValue) tools)
dispatch identityValue (Envelope.callTool name args) = ask (handleTool identityValue name args) (afterTool identityValue)
dispatch identityValue (Envelope.unknownMethod name) = respond identityValue
  (error (Envelope.Identity.value identityValue) -[1+ 32600 ]
    (toList "Method not found. Use a supported MCP method; ask the user if the intended method is unclear."))

toolRequestCarriesIdentity : ∀ identityValue name args →
  dispatch identityValue (Envelope.callTool name args) ≡
    ask (handleTool identityValue name args) (afterTool identityValue)
toolRequestCarriesIdentity identityValue name args = refl

exchange : Envelope.Request → Script Outcome
exchange invocation with Envelope.Request.identityValue invocation
... | Envelope.identity false id = dispatch (Envelope.identity false id) (Envelope.dispatch invocation)
... | Envelope.identity true (JSON.string id) = dispatch (Envelope.identity true (JSON.string id)) (Envelope.dispatch invocation)
... | Envelope.identity true _ = emit (error JSON.null -[1+ 32599 ]
    (toList "Request ID must be a string. Use a non-numeric ID and retry the request."))

numericRequestRejected : ∀ id method params →
  exchange (Envelope.request (Envelope.identity true (JSON.unsigned id)) method params) ≡
    emit (error JSON.null -[1+ 32599 ]
      (toList "Request ID must be a string. Use a non-numeric ID and retry the request."))
numericRequestRejected id method params = refl

parseError : Text → Script Outcome
parseError message = emit (error JSON.null -[1+ 32699 ]
  (toList "Invalid JSON: " ++ message ++ toList ". Correct the request and retry."))

notificationStillExecutes : ∀ id name args →
  dispatch (Envelope.identity false id) (Envelope.callTool name args) ≡
    ask (handleTool (Envelope.identity false id) name args) (afterTool (Envelope.identity false id))
notificationStillExecutes id name args = refl

notificationSuccessEmitsNothing : ∀ id value events result →
  Runs (afterTool (Envelope.identity false id) (inj₂ value)) events result →
  events ≡ [] × result ≡ nextLine
notificationSuccessEmitsNothing id value .[] .nextLine (returned _) = refl , refl

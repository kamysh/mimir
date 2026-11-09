{-# OPTIONS --safe #-}
-- Validate the MCP envelope before method execution. Response policy is
-- distinct from admission: valid notifications have no response or tool call.
module Mimir.McpEnvelope where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Integer using (ℤ; -[1+_])
open import Data.String using (String; toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.StructuredValue as JSON
open import Mimir.Text public using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.Validation as V
import Mimir.McpErrors as Errors
import Mimir.JsonObjects as Objects
open import Mimir.JsonObjects using (forbid)
module Correction = Errors.AgentCorrection

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

validID : JSON.Value → Bool
validID (JSON.string _) = true
validID (JSON.signed _) = true
validID (JSON.unsigned _) = true
validID (JSON.floating _) = true
validID _ = false

-- An invalid present ID is null in a diagnostic, never an admitted request.
identify : Maybe JSON.Value → Identity
identify nothing = identity false JSON.null
identify (just value) with validID value
... | true = identity true value
... | false = identity true JSON.null

record AdmittedIdentity : Set where
  constructor admittedID
  field
    response : Identity
    valid : Identity.reply response ≡ true → validID (Identity.value response) ≡ true

record Request : Set where
  constructor request
  field
    admittedIdentity : AdmittedIdentity
    method : Text
    params : List (Text × JSON.Value)

identityValue : Request → Identity
identityValue requestValue = AdmittedIdentity.response (Request.admittedIdentity requestValue)

record Problem : Set where
  constructor problem
  field response : Identity; code : ℤ; report : Correction.Claim

data Check (A : Set) : Set where
  accepted : A → Check A
  rejected : Correction.Item → List Correction.Item → Check A

both : ∀ {A B} → Check A → Check B → Check (A × B)
both (accepted a) (accepted b) = accepted (a , b)
both (rejected first rest) (accepted _) = rejected first rest
both (accepted _) (rejected first rest) = rejected first rest
both (rejected first rest) (rejected other more) = rejected first (rest ++ (other ∷ more))

issue : List V.Segment → V.Code → String → String → String → Correction.Item
issue path code message expected fix = Correction.item Correction.request
  (V.fault path code message) (literal expected) (literal fix)

version : JSON.Object.View → Check ⊤
version fields with fields (literal "jsonrpc")
... | nothing = rejected (issue (V.key "jsonrpc" ∷ []) V.missingField
  "The jsonrpc field must be the string \"2.0\"." "The string \"2.0\"."
  "Supply jsonrpc as \"2.0\"; this is the JSON-RPC version, not the MCP protocolVersion.") []
... | just value with asText (just value) ≟Text literal "2.0"
...   | yes _ = accepted tt
...   | no _ = rejected (issue (V.key "jsonrpc" ∷ []) V.malformedInput
  "The jsonrpc field must be the string \"2.0\"." "The string \"2.0\"."
  "Supply jsonrpc as \"2.0\"; this is the JSON-RPC version, not the MCP protocolVersion.") []

method : JSON.Object.View → Check Text
method fields with fields (literal "method")
... | just (JSON.string name) = accepted name
... | nothing = rejected (issue (V.key "method" ∷ []) V.missingField
  "The request needs a string method name." "A method name such as tools/list or tools/call."
  "Supply the method as a string. Keep the intended request; do not guess a different operation.") []
... | just _ = rejected (issue (V.key "method" ∷ []) V.wrongType
  "The request needs a string method name." "A method name such as tools/list or tools/call."
  "Supply the method as a string. Keep the intended request; do not guess a different operation.") []

identifier : JSON.Object.View → Check AdmittedIdentity
identifier fields with fields (literal "id")
... | nothing = accepted (admittedID (identity false JSON.null) (λ ()))
... | just value with validID value in valid
...   | true = accepted (admittedID (identity true value) (λ _ → valid))
...   | false = rejected (issue (V.key "id" ∷ []) V.wrongType
  "The MCP request ID is not a string or number." "A client-chosen string or JSON number; zero is a valid identifier."
  "Use the calling client's request identifier. Do not use null, a boolean, an array or an object.") []

parameters : JSON.Object.View → Check (List (Text × JSON.Value))
parameters fields with fields (literal "params")
... | nothing = accepted []
... | just (JSON.object values) = accepted values
... | just _ = rejected (issue (V.key "params" ∷ []) V.wrongType
  "MCP named parameters must be an object." "An object, or an omitted params member when the method permits it."
  "Supply named parameters as an object; do not replace an invalid supplied value with defaults.") []

responseIdentity : JSON.Object.View → Identity
responseIdentity fields with fields (literal "id")
... | just value = identify (just value)
... | nothing with version fields | method fields
...   | accepted _ | accepted _ = identity false JSON.null
...   | _ | _ = identity true JSON.null

problemCode : JSON.Object.View → ℤ
problemCode fields with version fields | method fields | identifier fields | parameters fields
... | accepted _ | accepted _ | accepted _ | rejected _ _ = -[1+ 32601 ]
... | _ | _ | _ | _ = -[1+ 32599 ]

extractFields : JSON.Object.View → Problem ⊎ Request
extractFields fields with both (version fields) (both (method fields) (both (identifier fields) (parameters fields)))
... | accepted (tt , name , who , params) = inj₂ (request who name params)
... | rejected first rest = inj₁ (problem (responseIdentity fields) (problemCode fields) (Correction.claim first rest))

extractUnique : JSON.Value → Problem ⊎ Request
extractUnique (JSON.object fields) = extractFields (JSON.Object.normalize fields)
extractUnique _ = inj₁ (problem (identity true JSON.null) -[1+ 32599 ] (Correction.claim
  (issue [] V.wrongType "The message is not a request object."
    "A JSON object containing jsonrpc, method and a client-chosen request ID."
    "Send one MCP request object per line; do not send a scalar or batch array.") []))

-- The standard decoder supplies fields before object normalization. Repeated
-- names at any depth block admission, even if both supplied values are equal.
Path = List V.Segment

mutual
  repeated : JSON.Value → Path → List Path
  repeated (JSON.object fields) path = repeatedFields fields [] path
  repeated (JSON.array values) path = repeatedElements values zero path
  repeated _ path = []

  repeatedFields : List (Text × JSON.Value) → List Text → Path → List Path
  repeatedFields [] seen path = []
  repeatedFields ((name , value) ∷ rest) seen path with Objects.Names.present? name seen
  ... | yes _ = (path ++ (V.fieldKey name ∷ [])) ∷
    (repeated value (path ++ (V.fieldKey name ∷ [])) ++ repeatedFields rest (name ∷ seen) path)
  ... | no _ = repeated value (path ++ (V.fieldKey name ∷ [])) ++ repeatedFields rest (name ∷ seen) path

  repeatedElements : List JSON.Value → ℕ → Path → List Path
  repeatedElements [] position path = []
  repeatedElements (value ∷ rest) position path = repeated value (path ++ (V.index position ∷ [])) ++
    repeatedElements rest (suc position) path

identifiers : List (Text × JSON.Value) → List JSON.Value
identifiers [] = []
identifiers ((name , value) ∷ rest) with name ≟Text literal "id"
... | yes _ = value ∷ identifiers rest
... | no _ = identifiers rest

uniqueIdentity : List JSON.Value → Identity
uniqueIdentity [] = identity false JSON.null
uniqueIdentity (value ∷ []) with validID value
... | true = identity true value
... | false = identity true JSON.null
uniqueIdentity (_ ∷ _ ∷ _) = identity true JSON.null

repeatedIdentity : JSON.Value → Identity
repeatedIdentity (JSON.object fields) = uniqueIdentity (identifiers fields)
repeatedIdentity _ = identity true JSON.null

repeatedIssue : Path → Correction.Item
repeatedIssue path = issue path V.duplicate
  "This field occurs more than once; no business operation was executed."
  "One intended value for each field."
  "Send this field exactly once. Decide which value was intended; do not rely on a first-value or last-value rule."

extract : JSON.Value → Problem ⊎ Request
extract value with repeated value []
... | [] = extractUnique value
... | first ∷ rest = inj₁ (problem (repeatedIdentity value) -[1+ 32599 ]
  (Correction.claim (repeatedIssue first) (map repeatedIssue rest)))

admittedHasNoRepeatedFields : ∀ value admitted → extract value ≡ inj₂ admitted → repeated value [] ≡ []
admittedHasNoRepeatedFields value admitted admission with repeated value []
... | [] = refl
... | first ∷ rest with admission
...   | ()

data Command : Set where
  initialize listTools : Command
  callTool : Text → JSON.Value → Command
  unknownMethod : Text → Command
  invalidParams : Correction.Claim → Command

toolName : JSON.Object.View → Check Text
toolName fields with fields (literal "name")
... | just (JSON.string name) = accepted name
... | nothing = rejected (issue (V.key "params" ∷ V.key "name" ∷ []) V.missingField
  "tools/call requires a string tool name." "The exact name of an advertised tool."
  "Supply the intended tool name from tool discovery; ask the user if the intended action is unknown.") []
... | just _ = rejected (issue (V.key "params" ∷ V.key "name" ∷ []) V.wrongType
  "tools/call requires a string tool name." "The exact name of an advertised tool."
  "Supply the intended tool name from tool discovery; ask the user if the intended action is unknown.") []

toolArguments : JSON.Object.View → Check JSON.Value
toolArguments fields with fields (literal "arguments")
... | nothing = accepted (JSON.object [])
... | just (JSON.object values) = accepted (JSON.object values)
... | just _ = rejected (issue (V.key "params" ∷ V.key "arguments" ∷ []) V.wrongType
  "Tool arguments must be an object." "An arguments object, or omission for a tool that needs no fields."
  "Supply the intended argument fields as an object; do not replace a malformed supplied value with defaults.") []

toolCommand : JSON.Value → Command
toolCommand (JSON.object fields) with JSON.Object.checkUnknowns forbid
  (literal "name" ∷ literal "arguments" ∷ literal "_meta" ∷ []) fields
... | V.rejected detail invalid = invalidParams (Correction.claim
  (Correction.item Correction.request (V.prependPath (V.key "params") detail)
    (literal "Use only name, arguments and optional protocol _meta.")
    (literal "Remove the unknown parameter. Preserve the intended action; do not execute a guessed correction.")) [])
... | V.accepted known with both (toolName (JSON.Object.normalize fields)) (toolArguments (JSON.Object.normalize fields))
...   | accepted (name , arguments) = callTool name arguments
...   | rejected first rest = invalidParams (Correction.claim first rest)
toolCommand _ = invalidParams (Correction.claim (issue (V.key "params" ∷ []) V.wrongType
  "MCP named parameters must be an object." "An object."
  "Supply named parameters as an object; do not replace an invalid supplied value with defaults.") [])

route : Text → JSON.Value → Command
route name params with name ≟Text literal "initialize"
... | yes _ = initialize
... | no _ with name ≟Text literal "tools/list"
...   | yes _ = listTools
...   | no _ with name ≟Text literal "tools/call"
...     | yes _ = toolCommand params
...     | no _ = unknownMethod name

dispatch : Request → Command
dispatch value = route (Request.method value) (JSON.object (Request.params value))

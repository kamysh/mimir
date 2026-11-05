{-# OPTIONS --safe #-}
-- JSON-RPC application error extraction. Typed fault data is retained beside
-- the legacy code/message pair; absent data never invents a typed refusal.
import Mimir.FloatConversion
module Mimir.McpErrorWire (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Integer using (ℤ; +_; -[1+_]; _≤_; _≤?_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Mimir.Text using (Text)
import Mimir.StructuredValue as V
import Mimir.McpErrors as Errors
import Mimir.McpClientWire as WireDependency
private
  module Wire = WireDependency floatConversion
import Mimir.ProviderResponse as Fields
import Mimir.SignedMachine as Machine

module BoundedCodes (minimum maximum : ℤ) where
  InRange : ℤ → Set
  InRange code = minimum ≤ code × code ≤ maximum

  boundedCode : ℤ → ℤ
  boundedCode code with minimum ≤? code
  ... | no below = -[1+ 0 ]
  ... | yes lower with code ≤? maximum
  ...   | no above = -[1+ 0 ]
  ...   | yes upper = code

  readCode : V.Value → ℤ
  readCode (V.signed code) = boundedCode code
  readCode (V.unsigned number) = boundedCode (+ number)
  readCode _ = -[1+ 0 ]

  readMessage : V.Value → Text
  readMessage (V.string message) = message
  readMessage _ = toList "unspecified MCP failure"

  decode : V.Value → Errors.Error
  decode raw = Errors.error (readCode (Fields.get "code" raw))
    (readMessage (Fields.get "message" raw)) (Wire.lookup "data" raw)

  encode : Errors.Error → V.Value
  encode (Errors.error code message nothing) = V.object
    ((toList "code" , V.signed code) ∷ (toList "message" , V.string message) ∷ [])
  encode (Errors.error code message (just dataValue)) = V.object
    ((toList "code" , V.signed code) ∷ (toList "message" , V.string message) ∷
     (toList "data" , dataValue) ∷ [])

  boundedExact : ∀ code → InRange code → boundedCode code ≡ code
  boundedExact code (lower , upper) with minimum ≤? code
  ... | no below = ⊥-elim (below lower)
  ... | yes aboveMinimum with code ≤? maximum
  ...   | no above = ⊥-elim (above upper)
  ...   | yes belowMaximum = refl

  roundTrip : ∀ error → InRange (Errors.Error.code error) → decode (encode error) ≡ error
  roundTrip (Errors.error code message nothing) bounded rewrite boundedExact code bounded = refl
  roundTrip (Errors.error code message (just dataValue)) bounded rewrite boundedExact code bounded = refl

  dataPreserved : ∀ raw → Errors.Error.details (decode raw) ≡ Wire.lookup "data" raw
  dataPreserved raw = refl

  structuredRefusalPreserved : ∀ code refusal → InRange code →
    Errors.classifyAt code (decode (encode (Errors.encodeAt code refusal))) ≡ Errors.rejected refusal
  structuredRefusalPreserved code report bounded =
    trans (cong (Errors.classifyAt code) (roundTrip (Errors.encodeAt code report) bounded))
      (Errors.roundTripAt code report)

  legacyRemainsUnclassified : ∀ expected code message → InRange code →
    Errors.classifyAt expected (decode (encode (Errors.error code message nothing))) ≡
    Errors.unclassified (Errors.error code message nothing)
  legacyRemainsUnclassified expected code message bounded =
    trans (cong (Errors.classifyAt expected) (roundTrip (Errors.error code message nothing) bounded))
      (Errors.legacyAt expected code message)

module I64 = Machine.Width 63
module Client = BoundedCodes I64.minimum I64.maximum

{-# OPTIONS --safe #-}
-- Server ingress composition: native line framing and UTF-8 admission precede
-- Unicode trimming, then complete JSON decoding and envelope extraction.
import Mimir.FloatConversion
module Mimir.McpInput (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.ReadLine as Lines
import Mimir.UTF8Text as UTF8
import Mimir.UTF8Packet as Packet
import Mimir.ScalarText as Text
import Mimir.JsonDecode as JSONDependency
private
  module JSON = JSONDependency floatConversion
import Mimir.JsonFlow as Flow
import Mimir.JsonCompletion as CompletionDependency
private
  module Completion = CompletionDependency floatConversion
import Mimir.McpEnvelope as Envelope
import Mimir.SignedMachine as Machine

module F = Flow.F

data BodyOutcome (input : List Byte) : Set where
  blank : input ≡ [] → BodyOutcome input
  accepted : JSON.Decoded → (position : F.Cursor input) →
    F.Cursor.remaining position ≡ [] → BodyOutcome input
  rejected : F.Rejected input → BodyOutcome input
  panicked : F.Cursor input → BodyOutcome input

fromJSON : ∀ {input} (result : Flow.Result JSON.Decoded input) →
  Completion.Complete result → BodyOutcome input
fromJSON (Flow.ordinary (F.success value position)) complete = accepted value position complete
fromJSON (Flow.ordinary (F.failure error)) complete = rejected error
fromJSON (Flow.panicked position) complete = panicked position

body : List Packet.Scalar → List Byte
body values = UTF8.encode (Text.trim values)

data Outcome (input : List Byte) : Set where
  eof : input ≡ [] → Outcome input
  invalidUTF8 : Lines.Line input → Packet.Error → Outcome input
  line : (framed : Lines.Line input) → (decoded : UTF8.Decoded (Lines.Line.bytes framed)) →
    BodyOutcome (body (UTF8.Decoded.values decoded)) → Outcome input

module Parser (checks : Machine.OverflowChecks) where
  module P = JSON.Parser checks

  trimmed : ∀ values → BodyOutcome (UTF8.encode values)
  trimmed [] = blank refl
  trimmed (first ∷ rest) = fromJSON (Flow.Productive.result (P.read (UTF8.encode (first ∷ rest))))
    (P.consumesCompleteDocument (UTF8.encode (first ∷ rest)))

  readBody : ∀ values → BodyOutcome (body values)
  readBody values = trimmed (Text.trim values)

  read : ∀ input → Outcome input
  read input with Lines.decode input
  ... | Lines.eof empty = eof empty
  ... | Lines.invalidUTF8 framed error = invalidUTF8 framed error
  ... | Lines.success framed textValue = line framed textValue (readBody (UTF8.Decoded.values textValue))

request : JSON.Decoded → Envelope.Request
request document = Envelope.extract (JSON.Decoded.value document)

command : JSON.Decoded → Envelope.Command
command document = Envelope.dispatch (request document)


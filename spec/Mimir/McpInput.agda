{-# OPTIONS --safe #-}
-- Mimir frames one line and trims its text before asking the standard JSON
-- parser. The supplied library owns UTF-8 admission and complete JSON syntax.
-- Its field-preserving visitor supplies object members before normalization;
-- Envelope.extract rejects repeated names before selecting any handler.
import Mimir.StandardLibrary
module Mimir.McpInput (library : Mimir.StandardLibrary.Contract) where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text; trim)
import Mimir.StandardLibrary as Library
import Mimir.ReadLine as Lines
import Mimir.StructuredValue as JSON
import Mimir.McpEnvelope as Envelope
import Data.Sum

data BodyOutcome (input : Text) : Set where
  blank : input ≡ [] → BodyOutcome input
  accepted : JSON.Value → BodyOutcome input
  rejected : Library.JSONError → BodyOutcome input
  panicked : Text → BodyOutcome input

fromJSON : ∀ {input} → Library.JSONResult → BodyOutcome input
fromJSON (Library.parsed value) = accepted value
fromJSON (Library.rejected error) = rejected error
fromJSON (Library.panicked message) = panicked message

body : Text → Text
body = trim

data Outcome (input : List Byte) : Set where
  eof : input ≡ [] → Outcome input
  invalidUTF8 : Lines.Line input → Text → Outcome input
  line : (framed : Lines.Line input) → (text : Text) → BodyOutcome (body text) → Outcome input

module Parser where
  trimmed : ∀ text → BodyOutcome text
  trimmed [] = blank refl
  trimmed text@(_ ∷ _) = fromJSON
    (Library.Contract.jsonMembers library (Library.Contract.encodeUTF8 library text))

  readBody : ∀ text → BodyOutcome (body text)
  readBody text = trimmed (trim text)

  read : ∀ input → Outcome input
  read input with Lines.decode library input
  ... | Lines.eof empty = eof empty
  ... | Lines.invalidUTF8 framed error = invalidUTF8 framed error
  ... | Lines.success framed text = line framed text (readBody text)

request : JSON.Value → Data.Sum._⊎_ Envelope.Problem Envelope.Request
request = Envelope.extract

command : JSON.Value → Data.Sum._⊎_ Envelope.Problem Envelope.Command
command value with request value
... | Data.Sum.inj₁ diagnostic = Data.Sum.inj₁ diagnostic
... | Data.Sum.inj₂ admitted = Data.Sum.inj₂ (Envelope.dispatch admitted)


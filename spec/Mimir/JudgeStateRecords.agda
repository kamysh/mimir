{-# OPTIONS --safe #-}
-- In-memory judge state records. Identity is a type parameter, not a claim
-- that UUID generation is injective. Clock/downcast results are explicit input.
module Mimir.JudgeStateRecords where

open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Integer using (ℤ)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; byteLength)
import Mimir.SourceFailure as Source

clock : Maybe ℕ → ℕ
clock nothing = 0
clock (just seconds) = seconds

module Over (Id : Set) where
  record Deferred : Set where
    constructor deferred
    field identity : Id; revision : ℤ

  record FailureDiagnostic : Set where
    constructor diagnosticValue
    field observedAt : ℕ; experience : Id; tool detail : Text

  newDiagnostic : Maybe ℕ → Id → Text → Text → FailureDiagnostic
  newDiagnostic observed identity tool detail = diagnosticValue (clock observed) identity
    tool detail

  diagnosticFieldsPreserved : ∀ observed identity tool detail →
    FailureDiagnostic.tool (newDiagnostic observed identity tool detail) ≡ tool ×
    FailureDiagnostic.detail (newDiagnostic observed identity tool detail) ≡ detail
  diagnosticFieldsPreserved observed identity tool detail = refl , refl

  record Report : Set where
    constructor reportValue
    field
      status : Text
      blockReason : Maybe Text
      diagnostic : Maybe FailureDiagnostic
      failureDetail : Maybe Text
      failureSource : Maybe Source.Failure
      diagnosticsId : Maybe Id
      selectedIds : List Id
      selected confirmed corrected pending unavailable : ℕ
      deferredReviews : List Deferred
      notification : Text
      recordedAt : ℕ

  stamp : Maybe ℕ → Report → Report
  stamp observed before = record before { recordedAt = clock observed }

  newReport : Maybe ℕ → Text → ℕ → ℕ → ℕ → ℕ → ℕ → Report
  newReport observed status selected confirmed corrected pending unavailable =
    reportValue status nothing nothing nothing nothing nothing [] selected confirmed corrected pending unavailable []
      (toList "disabled") (clock observed)

  captureSource : Maybe Source.Failure → Report → Report
  captureSource found before with Report.failureSource before
  ... | just existing = before
  ... | nothing = record before { failureSource = found }

  capturedSourceRetained : ∀ found before existing → Report.failureSource before ≡ just existing →
    captureSource found before ≡ before
  capturedSourceRetained found before existing same rewrite same = refl

  clearNotification : Report → Report
  clearNotification before = record before { notification = [] }

  record Confirmed : Set where
    constructor confirmedValue
    field identity : Id; recordedAt : ℕ

  record Incident : Set where
    constructor incident
    field first : Report; latest : Maybe Report; confirmedReviews : List Confirmed; recoveredAt : Maybe ℕ

  sanitize : Incident → Incident
  sanitize before = record before
    { first = clearNotification (Incident.first before)
    ; latest = map clearNotification (Incident.latest before) }

  sanitizeIdempotent : ∀ before → sanitize (sanitize before) ≡ sanitize before
  sanitizeIdempotent (incident first nothing confirmations recovered) = refl
  sanitizeIdempotent (incident first (just latest) confirmations recovered) = refl

  record Event : Set where
    constructor eventValue
    field
      at : ℕ
      experience : Id
      kind : Text
      modelRequests toolAttempts : Maybe ℕ
      tool detail : Maybe Text
      detailBytes : Maybe ℕ

  newEvent : Maybe ℕ → Id → Text → ℕ → ℕ → Maybe Text → Maybe Text → Event
  newEvent observed identity kind model toolBudget tool detail = eventValue (clock observed) identity
    kind (just model) (just toolBudget) tool detail (map byteLength detail)

  eventOriginalDetailSize : ∀ observed identity kind model toolBudget tool detail →
    Event.detailBytes (newEvent observed identity kind model toolBudget tool (just detail)) ≡ just (byteLength detail)
  eventOriginalDetailSize observed identity kind model toolBudget tool detail = refl

  eventFieldsPreserved : ∀ observed identity kind model toolBudget tool detail →
    Event.kind (newEvent observed identity kind model toolBudget tool detail) ≡ kind ×
    Event.tool (newEvent observed identity kind model toolBudget tool detail) ≡ tool ×
    Event.detail (newEvent observed identity kind model toolBudget tool detail) ≡ detail
  eventFieldsPreserved observed identity kind model toolBudget tool detail = refl , refl , refl

  record Trace : Set where
    constructor traceValue
    field
      identity : Id
      startedAt : ℕ
      finishedAt : Maybe ℕ
      status : Text
      blockReason : Maybe Text
      selectedIds : List Id
      modelRequests toolAttempts : Maybe ℕ
      events : List Event
      eventsOmitted : ℕ

  Diagnostics = List Trace

{-# OPTIONS --safe #-}
-- The actual server serialization receipt for a source snapshot. UUID/JSON
-- conversion belongs to the existing library/typed database boundary; this
-- module does not implement or prove an encoder. Failed conversion is a
-- diagnostic, never an authorization to capture different sources.
module Mimir.BackfillCaptureEncoding where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
import Mimir.ApplicationStore as Store
import Mimir.BackfillRecovery as Backfill
import Mimir.OperationControls as Controls
import Mimir.PublicEncoding as Public
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Registered
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Wire

module Encode (library : Library.Contract) (format : Public.Formatting) where
  module A = Backfill.Admission library
  module B = Backfill.Encode format
  module Plan = Controls.Plan

  shape : List Plan.Boundary
  shape = Plan.repeated "store.insert_belief_embedding" ∷ []

  typedPlan : List Backfill.Source → List Plan.CapturedSource → Plan.Saved
  typedPlan sources rows = Plan.saved (toList "reembed") shape
    (Plan.pendingSteps library rows) (just (B.snapshot sources))

  boundary : Plan.Boundary → Wire.Value
  boundary item = Public.object
    (("site" , Wire.string (Plan.Boundary.site item)) ∷
     ("may_repeat" , Wire.boolean (Plan.Boundary.repeated item)) ∷ [])

  statement : Plan.Step → Wire.Value
  statement item = Public.object
    (("site" , Wire.string (Plan.Step.site item)) ∷
     ("key" , Public.optional Wire.string (Plan.Step.key item)) ∷
     ("id" , Wire.string (Plan.Step.id item)) ∷ [])

  encodedPlan : List Backfill.Source → List Plan.CapturedSource → Wire.Value
  encodedPlan sources rows = Public.object
    (("operation" , Wire.string (toList "reembed")) ∷
     ("shape" , Wire.array (map boundary shape)) ∷
     ("steps" , Wire.array (map statement (Plan.pendingSteps library rows))) ∷
     ("capture" , B.snapshot sources) ∷ [])

  -- This is supplied by the successful observed conversion of the actual
  -- snapshot, not by an agent or an invocation expected answer. In
  -- particular it makes no assertion that every Agda Nat is a valid UUID.
  record Candidate (sources : List Backfill.Source) : Set where
    field
      rows : List Plan.CapturedSource
      represented : map A.semanticSource rows ≡ sources
      decodedCapture : Plan.readCapture library (B.snapshot sources) ≡ inj₂ rows
      decodedPlan : Plan.decode (encodedPlan sources rows) ≡ inj₂ (typedPlan sources rows)
      validPlan : Plan.valid library (typedPlan sources rows) ≡ true

  rawPlan : ∀ {sources} → Candidate sources → Wire.Value
  rawPlan {sources} candidate = encodedPlan sources (Candidate.rows candidate)

  alongObservation : ∀ {Observation Result : Set} (observed : Observation)
    (continue : (actual : Observation) → observed ≡ actual → Result)
    actual (same : observed ≡ actual) → continue observed refl ≡ continue actual same
  alongObservation observed continue .observed refl = refl

  originalAtBinding : ∀ token registration reserved binding raw →
    Registered.originalPlan (toList "reembed") token registration ≡ inj₂ (reserved , binding , raw) →
    Store.BindingRow.arguments binding ≡ Wire.object [] → A.provider (Store.BindingRow.settings binding) ≡ true →
    A.original token registration ≡ A.afterDecode token binding raw (Plan.decode raw) refl
  originalAtBinding token registration reserved binding raw resolved arguments configured
    rewrite resolved | arguments | configured = refl

  canonicalReadyGeneral : ∀ token registration reserved binding raw plan capture rows →
    Registered.originalPlan (toList "reembed") token registration ≡ inj₂ (reserved , binding , raw) →
    Store.BindingRow.arguments binding ≡ Wire.object [] →
    A.provider (Store.BindingRow.settings binding) ≡ true →
    Plan.decode raw ≡ inj₂ plan → Plan.valid library plan ≡ true →
    Plan.Saved.capture plan ≡ just capture → Plan.readCapture library capture ≡ inj₂ rows →
    Σ A.Context (λ context → A.original token registration ≡ inj₂ context × A.Context.rows context ≡ rows)
  canonicalReadyGeneral token registration reserved binding raw plan capture rows resolved arguments configured decoded valid captured sources =
    A.context token binding raw plan capture rows decoded valid captured sources ,
    trans (originalAtBinding token registration reserved binding raw resolved arguments configured)
      (trans (alongObservation (Plan.decode raw) (A.afterDecode token binding raw) (inj₂ plan) decoded)
        (trans (alongObservation (Plan.valid library plan) (A.afterValid token binding raw plan decoded) true valid)
          (trans (alongObservation (Plan.Saved.capture plan) (A.afterCapture token binding raw plan decoded valid) (just capture) captured)
            (alongObservation (Plan.readCapture library capture)
              (A.afterSources token binding raw plan capture decoded valid captured) (inj₂ rows) sources)))) , refl

  canonicalReady : ∀ sources (candidate : Candidate sources) token registration reserved binding →
    Registered.originalPlan (toList "reembed") token registration ≡ inj₂ (reserved , binding , rawPlan candidate) →
    Store.BindingRow.arguments binding ≡ Wire.object [] →
    A.provider (Store.BindingRow.settings binding) ≡ true →
    Σ A.Context (λ context → A.original token registration ≡ inj₂ context × A.selected context ≡ sources)
  canonicalReady sources candidate token registration reserved binding resolved arguments configured with
    canonicalReadyGeneral token registration reserved binding (rawPlan candidate)
      (typedPlan sources (Candidate.rows candidate)) (B.snapshot sources) (Candidate.rows candidate)
      resolved arguments configured (Candidate.decodedPlan candidate) (Candidate.validPlan candidate) refl (Candidate.decodedCapture candidate)
  ... | admittedContext , admitted , rows = admittedContext , admitted ,
    trans
      (cong (map A.semanticSource) rows) (Candidate.represented candidate)

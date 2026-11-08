{-# OPTIONS --safe #-}
-- Bind incident decisions and diagnostic lifecycle operations to the concrete
-- named-file codecs and filesystem receipts. Native UUIDs are projected into
-- the controller identity domain without assuming a fresh/injective generator.
module Mimir.JudgeStateOperations where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _,_; _×_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.StandardLibrary as Conversion
import Mimir.JudgePersistenceComposition as Persistence
import Mimir.JudgePersistence as Names
import Mimir.JudgeIncident as Incident
import Mimir.JudgeTraceStart as Start
import Mimir.JudgeTraceMutation as Mutation
import Mimir.JudgeStateRecords as Records
import Mimir.PublicInput as Input
import Mimir.UUIDGroups as UUID
import Mimir.UUIDV4 as Random
import Mimir.UnixPath as Path
import Mimir.Effects as Effects

module R = Records.Over ℕ
module I = Incident.Over ℕ _≟_
module Begin = Start.Over ℕ _≟_

data Effect : Set where
  readFailure : Effect
  writeFailure : R.Incident → Effect
Reply : Effect → Set
Reply readFailure = Text ⊎ Maybe R.Incident
Reply (writeFailure _) = Text ⊎ ⊤
module P = Effects.Protocol Effect Reply

writeDecision : Maybe R.Incident → P.Script (Text ⊎ ⊤)
writeDecision nothing = P.done (inj₂ tt)
writeDecision (just value) = P.ask (writeFailure value) P.done

recordIncident : R.Report → P.Script (Text ⊎ ⊤)
recordIncident report = P.ask readFailure λ where
  (inj₁ error) → P.done (inj₁ error)
  (inj₂ before) → writeDecision (proj₁ (I.decide report before))

module Bound (conversion : Conversion.Contract) (sizeMaximum : ℕ)
  (endian : Random.Endian) (path : Path.Path) where
  private
    module Store = Persistence.Storage conversion sizeMaximum endian
    module Failure = Store.Reading Names.failure
    module Diagnostics = Store.Reading Names.diagnostics
    module M = Mutation.Over ℕ _≟_

  ReadReceipt : (name : Names.Name) → Text ⊎ Maybe (Persistence.Logical name) → Set
  ReadReceipt name = Store.Reading.Receipt name path

  Written : (name : Names.Name) → Persistence.Logical name → Text ⊎ ⊤ → Set
  Written name = Store.Written path name

  IncidentReceipt : (effect : Effect) → Reply effect → Set
  IncidentReceipt readFailure reply = Failure.Receipt path reply
  IncidentReceipt (writeFailure value) reply = Store.Written path Names.failure value reply

  record IncidentExecution (report : R.Report) (reply : Text ⊎ ⊤) : Set where
    field events : List P.Event
          execution : P.Runs (recordIncident report) events reply
          receipts : All (λ { (effect , reply) → IncidentReceipt effect reply }) events

  diagnosticResult : Text ⊎ Maybe R.Diagnostics → Text ⊎ R.Diagnostics
  diagnosticResult (inj₁ error) = inj₁ error
  diagnosticResult (inj₂ nothing) = inj₂ []
  diagnosticResult (inj₂ (just values)) = inj₂ values

  record ReadDiagnostics (reply : Text ⊎ R.Diagnostics) : Set where
    field result : Text ⊎ Maybe R.Diagnostics
          read : Diagnostics.Receipt path result
          exact : diagnosticResult result ≡ reply

  BeginReceipt : (effect : Begin.Operation) → Begin.Reply effect → Set
  BeginReceipt Begin.readDiagnostics reply = ReadDiagnostics reply
  BeginReceipt Begin.clock reply = ⊤
  BeginReceipt Begin.newId reply = Σ UUID.UUID (λ value → Input.uuidNumber value ≡ reply)
  BeginReceipt (Begin.writeDiagnostics values) reply = Store.Written path Names.diagnostics values reply

  startedResult : Begin.Result → Text ⊎ ℕ
  startedResult (Begin.started id) = inj₂ id
  startedResult (Begin.failed error) = inj₁ error

  record Began (report : R.Report) (budget : ℕ) (reply : Text ⊎ ℕ) : Set where
    field events : List Begin.Event
          result : Begin.Result
          execution : Begin.Runs (Begin.begin report budget) events result
          receipts : All (λ { (effect , value) → BeginReceipt effect value }) events
          exact : startedResult result ≡ reply

  MutationReceipt : (effect : M.Operation) → M.Reply effect → Set
  MutationReceipt M.readDiagnostics reply = ReadDiagnostics reply
  MutationReceipt M.clock reply = ⊤
  MutationReceipt (M.writeDiagnostics values) reply = Store.Written path Names.diagnostics values reply

  data Acknowledges : M.Result → Text ⊎ ⊤ → Set where
    completed : Acknowledges M.completed (inj₂ tt)
    failed : ∀ error → Acknowledges (M.failed error) (inj₁ error)

  record Mutated (program : M.Script M.Result) (reply : Text ⊎ ⊤) : Set where
    field events : List M.Event
          result : M.Result
          execution : M.Runs program events result
          receipts : All (λ { (effect , value) → MutationReceipt effect value }) events
          normal : Acknowledges result reply

  Finished : ℕ → R.Report → Text ⊎ ⊤ → Set
  Finished id report = Mutated (M.finish id report)

  Recorded : ℕ → R.Event → Text ⊎ ⊤ → Set
  Recorded id event = Mutated (M.recordEvent id event)

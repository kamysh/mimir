{-# OPTIONS --safe #-}
-- Notification files use strict records; the incidents object is a BTreeMap
-- with last occurrence replacement, sorted iteration and unconstrained keys.
-- Loading does not rerun event validation on historical incidents.
module Mimir.NotificationWire where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; map; foldl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.StructuredValue
open import Mimir.RecordDecoding
open import Mimir.Validation using (Fault; fault; malformedInput)
open import Mimir.JsonObjects using (forbid; rejectKnownRepeated)
import Mimir.UnsignedWire as UInt
import Mimir.NotificationIncident as I
import Mimir.NotificationRuntime as N
import Mimir.DigestDelivery as Digest
import Mimir.SerdeSequence as Sequence
import Mimir.JudgeStatePrimitives as P

enum : ∀ {A : Set} → List (Text × A) → Value → Fault ⊎ A
enum [] raw = inj₁ (fault [] malformedInput "unknown notification enum variant")
enum ((name , value) ∷ rest) (string actual) with name ≟Text actual
... | yes _ = inj₂ value
... | no _ = enum rest (string actual)
enum ((name , value) ∷ rest) (object ((actual , null) ∷ [])) with name ≟Text actual
... | yes _ = inj₂ value
... | no _ = enum rest (object ((actual , null) ∷ []))
enum (_ ∷ _) _ = inj₁ (fault [] malformedInput "notification enum must be a string")

-- Serde-derived records accept positional sequences as well as maps. Keep
-- deny_unknown_fields on the map path; defaults apply only at exhausted input.
recordDecoder : ∀ {A : Set} fields → (Sequence.Values fields → A) →
  List Text → (Object.View → Fault ⊎ A) → Value → Fault ⊎ A
recordDecoder fields build names decode (array values) with Sequence.read fields 0 values
... | inj₁ error = inj₁ (fault [] malformedInput "invalid notification record")
... | inj₂ values = inj₂ (build values)
recordDecoder fields build names decode raw = readRecord forbid rejectKnownRepeated names decode raw

kind : Value → Fault ⊎ I.Kind
kind = enum ((toList "failure" , I.failure) ∷ (toList "recovery" , I.recovery) ∷ [])
delivery : Value → Fault ⊎ I.Delivery
delivery = enum ((toList "pending" , I.pending) ∷ (toList "exhausted" , I.exhausted) ∷ [])
lastError : Value → Fault ⊎ I.LastError
lastError = enum ((toList "auth_required" , I.authRequired) ∷ (toList "unavailable" , I.unavailable) ∷ [])

alertNames : List Text
alertNames = map toList ("id" ∷ "kind" ∷ "source" ∷ "code" ∷ "summary" ∷
  "details" ∷ "attempts" ∷ "next_due" ∷ "delivery" ∷ "last_error" ∷ [])

module Decode (sizeMaximum clockMaximum : ℕ) where
  alertFields : Object.View → Fault ⊎ I.Alert
  alertFields view = required (toList "id") asString view >>= λ id →
    required (toList "kind") kind view >>= λ k →
    required (toList "source") asString view >>= λ source →
    required (toList "code") asString view >>= λ code →
    required (toList "summary") asString view >>= λ summary →
    optional (toList "details") asString view >>= λ details →
    required (toList "attempts") (UInt.natural sizeMaximum) view >>= λ attempts →
    required (toList "next_due") (UInt.natural clockMaximum) view >>= λ due →
    required (toList "delivery") delivery view >>= λ d →
    optional (toList "last_error") lastError view >>= λ error →
    inj₂ (I.alert id k source code summary details attempts due d error)

  alert : Value → Fault ⊎ I.Alert
  alert = recordDecoder fields build alertNames alertFields
    where
    fields = P.required (toList "id") Text asString ∷
      P.required (toList "kind") I.Kind kind ∷
      P.required (toList "source") Text asString ∷ P.required (toList "code") Text asString ∷
      P.required (toList "summary") Text asString ∷ P.optional (toList "details") Text asString ∷
      P.required (toList "attempts") ℕ (UInt.natural sizeMaximum) ∷
      P.required (toList "next_due") ℕ (UInt.natural clockMaximum) ∷
      P.required (toList "delivery") I.Delivery delivery ∷ P.optional (toList "last_error") I.LastError lastError ∷ []
    build : Sequence.Values fields → I.Alert
    build (Sequence.more id (Sequence.more k (Sequence.more source (Sequence.more code
      (Sequence.more summary (Sequence.more details (Sequence.more attempts (Sequence.more due
      (Sequence.more d (Sequence.more error Sequence.empty)))))))))) =
      I.alert id k source code summary details attempts due d error

  incidentFields : Object.View → Fault ⊎ I.Incident
  incidentFields view = required (toList "source") asString view >>= λ source →
    required (toList "incident_key") asString view >>= λ key →
    optional (toList "active_code") asString view >>= λ active →
    optional (toList "delivered_code") asString view >>= λ delivered →
    optional (toList "outbox") alert view >>= λ pending →
    inj₂ (I.incident source key active delivered pending)

  incident : Value → Fault ⊎ I.Incident
  incident = recordDecoder fields build
    (map toList ("source" ∷ "incident_key" ∷ "active_code" ∷ "delivered_code" ∷ "outbox" ∷ [])) incidentFields
    where
    fields = P.required (toList "source") Text asString ∷ P.required (toList "incident_key") Text asString ∷
      P.optional (toList "active_code") Text asString ∷ P.optional (toList "delivered_code") Text asString ∷
      P.optional (toList "outbox") I.Alert alert ∷ []
    build : Sequence.Values fields → I.Incident
    build (Sequence.more source (Sequence.more key (Sequence.more active
      (Sequence.more delivered (Sequence.more pending Sequence.empty))))) = I.incident source key active delivered pending

  -- Fold in input order: all occurrences are decoded, including overwritten
  -- values. A malformed overwritten incident therefore still rejects the file.
  incidentMap : N.Entries → List (Text × Value) → Fault ⊎ N.Entries
  incidentMap before [] = inj₂ before
  incidentMap before ((key , raw) ∷ rest) = incident raw >>= λ item →
    incidentMap (N.insert key item (N.remove key before)) rest

  entries : Value → Fault ⊎ N.Entries
  entries raw = asObject raw >>= incidentMap []

  outboxFields : Object.View → Fault ⊎ N.Outbox
  outboxFields view = required (toList "schema_version") (UInt.natural 4294967295) view >>= λ version →
    required (toList "incidents") entries view >>= λ items → inj₂ (N.outbox version items)

  outbox : Value → Fault ⊎ N.Outbox
  outbox = recordDecoder fields build (map toList ("schema_version" ∷ "incidents" ∷ [])) outboxFields
    where
    fields = P.required (toList "schema_version") ℕ (UInt.natural 4294967295) ∷
      P.required (toList "incidents") N.Entries entries ∷ []
    build : Sequence.Values fields → N.Outbox
    build (Sequence.more version (Sequence.more items Sequence.empty)) = N.outbox version items

  cursorFields : Object.View → Fault ⊎ Digest.Cursor
  cursorFields view = optional (toList "through_day") asString view >>= λ through →
    required (toList "next_due") (UInt.natural clockMaximum) view >>= λ due →
    defaulted (toList "last_attempt_failed") false asBoolean view >>= λ failed →
    inj₂ (Digest.cursor through due failed)

  cursor : Value → Fault ⊎ Digest.Cursor
  cursor = recordDecoder fields build
    (map toList ("through_day" ∷ "next_due" ∷ "last_attempt_failed" ∷ [])) cursorFields
    where
    fields = P.optional (toList "through_day") Text asString ∷
      P.required (toList "next_due") ℕ (UInt.natural clockMaximum) ∷
      P.defaulted (toList "last_attempt_failed") Data.Bool.Bool asBoolean false ∷ []
    build : Sequence.Values fields → Digest.Cursor
    build (Sequence.more through (Sequence.more due (Sequence.more failed Sequence.empty))) = Digest.cursor through due failed

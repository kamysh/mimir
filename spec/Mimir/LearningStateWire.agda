{-# OPTIONS --safe #-}
-- ExperienceState response decoding. Serde permits unknown outer members;
-- the nested Experience retains its strict schema. Revision validity is a
-- separate observation/selection check, not silently added to deserialization.
module Mimir.LearningStateWire where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID)
open import Mimir.Validation using (Fault)
open import Mimir.RecordDecoding using (_>>=_; mapResult)
open import Mimir.PublicInput
import Mimir.StructuredValue as V
import Mimir.LearningWire as Wire
import Mimir.ReviewObservation as Observation
import Mimir.StandardLibrary as Conversion

ids : Conversion.Contract → List (Text × V.Value) → Fault ⊎ List (Text × UUID)
ids conversion [] = inj₂ []
ids conversion ((key , value) ∷ rest) with V.Object.normalize rest key
... | just _ = ids conversion rest
... | nothing = readUUID conversion value >>= λ id → mapResult ((key , id) ∷_) (ids conversion rest)

candidateIDs : Conversion.Contract → V.Value → Fault ⊎ List (Text × UUID)
candidateIDs conversion value = V.asObject value >>= ids conversion

module Decode (conversion : Conversion.Contract) (sizeMaximum : ℕ) where
  module W = Wire.Decode conversion sizeMaximum

  snapshot : V.Value → Fault ⊎ Observation.Snapshot
  snapshot raw = V.asObject raw >>= λ fields → decode (V.Object.normalize fields)
    where
    decode : V.Object.View → Fault ⊎ Observation.Snapshot
    decode fields = required "experience" W.experience fields >>= λ experience →
      required "revision" i64 fields >>= λ revision → required "review_revision" i64 fields >>= λ reviewRevision →
      required "reviewed_revision" i64 fields >>= λ reviewedRevision →
      defaulted "candidate_ids" [] (candidateIDs conversion) fields >>= λ ids →
      inj₂ (Observation.snapshot experience revision reviewRevision reviewedRevision ids)

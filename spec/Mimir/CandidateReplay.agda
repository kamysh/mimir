{-# OPTIONS --safe #-}
-- Read-only candidate-ID reconstruction on exact review retry. It rejects
-- missing, changed or retired reservations rather than returning guessed IDs.
module Mimir.CandidateReplay where

open import Data.List using (List; []; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)
open import Mimir.Text using (Text)
open import Mimir.LearningCandidates using (Candidate; candidateKey)
open import Mimir.OptionalTraversal using (nothingNotJust)
open import Mimir.Validation hiding (check)
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateBatch as Batch
import Mimir.ReviewResolution as Resolution

checkOne : ∀ experience registry declaration → Checked (Batch.Declared experience registry declaration)
checkOne experience registry declaration
  with Registry.lookup (experience , candidateKey declaration) registry in found
... | nothing = rejected (fault [] missingReference "candidate key is not reserved")
  (λ { (row , present , valid) → nothingNotJust present })
... | just row with Registry.checkExisting declaration row
...   | accepted valid = accepted (row , refl , valid)
...   | rejected failure invalid = rejected failure
  (λ { (other , present , valid)
         → invalid
           (subst (Registry.ExistingValid declaration)
            (sym (just-injective present)) valid)
     })

check : ∀ experience registry declarations → Checked (All (Batch.Declared experience registry) declarations)
check experience registry = allChecked (checkOne experience registry)

module Read (experience : UUID) (registry : Registry.Registry) where
  binding : (declaration : Candidate) → Batch.Declared experience registry declaration → Text × UUID
  binding declaration (row , present , valid) = candidateKey declaration , Registry.Entry.nodeID row

  bindings : (declarations : List Candidate) → All (Batch.Declared experience registry) declarations → Resolution.Registry
  bindings = Resolution.mapEvidence binding

  bindingSupported : ∀ declaration proof → Batch.Supported experience registry (binding declaration proof)
  bindingSupported declaration (row , present , same , live) = row , present , refl , live

  allSupported : ∀ declarations proofs → All (Batch.Supported experience registry) (bindings declarations proofs)
  allSupported = Resolution.mapEvidenceAll binding bindingSupported

  countExact : ∀ declarations proofs → length (bindings declarations proofs) ≡ length declarations
  countExact = Resolution.mapEvidenceLength binding

readIDs : UUID → Registry.Registry → List Candidate → Fault ⊎ Resolution.Registry
readIDs experience registry declarations with check experience registry declarations
... | rejected failure invalid = inj₁ failure
... | accepted proofs = inj₂ (Read.bindings experience registry declarations proofs)

returnedSupported : ∀ experience registry declarations ids →
  readIDs experience registry declarations ≡ inj₂ ids → All (Batch.Supported experience registry) ids
returnedSupported experience registry declarations ids observed
  with check experience registry declarations
... | rejected failure invalid with observed
...   | ()
returnedSupported experience registry declarations ids observed | accepted proofs with observed
... | refl = Read.allSupported experience registry declarations proofs

returnedCount : ∀ experience registry declarations ids →
  readIDs experience registry declarations ≡ inj₂ ids → length ids ≡ length declarations
returnedCount experience registry declarations ids observed
  with check experience registry declarations
... | rejected failure invalid with observed
...   | ()
returnedCount experience registry declarations ids observed | accepted proofs with observed
... | refl = Read.countExact experience registry declarations proofs

-- Immediately replaying a successful reservation batch cannot invent a
-- missing/changed/retired-declaration failure. Later retirement is different.
preparedReplayAccepted : ∀ {occupied experience before declarations after bindings} →
  Batch.Batch occupied experience before declarations after bindings →
  reported (check experience after declarations) ≡ []
preparedReplayAccepted {experience = experience} {declarations = declarations} {after = after} batch =
  noFalseRejection (check experience after declarations) (Batch.declarationsPreserved batch)

sameKeySameIdentity : ∀ experience registry name first second →
  Batch.Supported experience registry (name , first) →
  Batch.Supported experience registry (name , second) → first ≡ second
sameKeySameIdentity experience registry name first second
  (firstRow , firstFound , firstID , firstLive)
  (secondRow , secondFound , secondID , secondLive) = trans (sym firstID)
    (trans
     (cong Registry.Entry.nodeID
      (just-injective (trans (sym firstFound) secondFound)))
     secondID)

replayKeepsReservedIdentity : ∀ {occupied experience before declarations after bindings}
  (batch : Batch.Batch occupied experience before declarations after bindings) replayed name original actual →
  readIDs experience after declarations ≡ inj₂ replayed →
  Resolution.lookup name bindings ≡ just original →
  Resolution.lookup name replayed ≡ just actual → original ≡ actual
replayKeepsReservedIdentity {experience = experience} {declarations = declarations} {after = after}
  batch replayed name original actual readBack old new = sameKeySameIdentity experience after name original actual
    (Batch.resolvedReservation batch name original old)
    (Batch.lookupSupported experience after replayed name actual
     (returnedSupported experience after declarations replayed readBack)
     new)

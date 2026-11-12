{-# OPTIONS --safe #-}
-- Compose checked single-candidate reservations in request order. A failed
-- plan returns no publishable partial registry. Fresh IDs are untrusted inputs;
-- the existing registry checker rejects collisions rather than assuming UUID
-- uniqueness. The database adapter must publish registry and graph nodes in
-- the surrounding review transaction.
module Mimir.CandidateBatch where

open import Data.Bool using (false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym; cong)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID)
open import Mimir.LearningCandidates using (Candidate; candidateKey)
open import Mimir.Validation using (Fault)
open import Mimir.OptionalTraversal using (nothingNotJust)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.CandidateRegistry as Registry
import Mimir.ReviewResolution as Resolution

data Batch (occupied : List UUID) (experience : UUID) :
  Registry.Registry → List Candidate → Registry.Registry → Resolution.Registry → Set where
  done : ∀ before → Batch occupied experience before [] before []
  next : ∀ {before candidate rest after bindings} →
    (planned : Registry.Plan before occupied experience candidate) →
    Batch occupied experience (Registry.publish planned) rest after bindings →
    Batch occupied experience before (candidate ∷ rest) after
      ((candidateKey candidate , Registry.assigned planned) ∷ bindings)

Prepared : List UUID → UUID → Registry.Registry → List Candidate → Set
Prepared occupied experience before candidates = Σ Registry.Registry (λ after →
  Σ Resolution.Registry (λ bindings → Batch occupied experience before candidates after bindings))

prepare : ∀ occupied experience before candidates → (Candidate → UUID) →
  Fault ⊎ Prepared occupied experience before candidates
prepare occupied experience before [] fresh = inj₂ (before , [] , done before)
prepare occupied experience before (candidate ∷ rest) fresh
  with Registry.reserve before occupied experience candidate (fresh candidate)
... | inj₁ fault = inj₁ fault
... | inj₂ planned with prepare occupied experience (Registry.publish planned) rest fresh
...   | inj₁ fault = inj₁ fault
...   | inj₂ (after , bindings , remainder) = inj₂
  (after , (candidateKey candidate , Registry.assigned planned) ∷ bindings , next planned remainder)

-- Reusing or adding a fresh reservation cannot change an existing lookup.
lookupPreserved : ∀ {before occupied experience candidate}
  (planned : Registry.Plan before occupied experience candidate) name original →
  Registry.lookup name before ≡ just original → Registry.lookup name (Registry.publish planned) ≡ just original
lookupPreserved (Registry.reuse row found valid) name original present = present
lookupPreserved {before} {experience = experience} {candidate}
  (Registry.create fresh absent unused) name original present
  with Registry.keyEqual name (experience , candidateKey candidate)
... | yes same = ⊥-elim
  (nothingNotJust
   (trans (sym absent)
    (subst (λ name → Registry.lookup name before ≡ just original) same
     present)))
... | no different = present

batchPreserves : ∀ {occupied experience before candidates after bindings} →
  Batch occupied experience before candidates after bindings → ∀ name original →
  Registry.lookup name before ≡ just original → Registry.lookup name after ≡ just original
batchPreserves (done before) name original present = present
batchPreserves (next planned remainder) name original present = batchPreserves remainder name original
  (lookupPreserved planned name original present)

-- Every returned binding refers to a live reservation in the final
-- registry for this experience, after all later reservations have run.
Supported : UUID → Registry.Registry → Text × UUID → Set
Supported experience after (name , identity) = Σ Registry.Entry (λ entry →
  Registry.lookup (experience , name) after ≡ just entry ×
  Registry.Entry.nodeID entry ≡ identity × Registry.Entry.retired entry ≡ false)

singleSupported : ∀ {before occupied experience candidate}
  (planned : Registry.Plan before occupied experience candidate) →
  Supported experience (Registry.publish planned) (candidateKey candidate , Registry.assigned planned)
singleSupported (Registry.reuse row found (same , live)) = row , found , refl , live
singleSupported {before} {experience = experience} {candidate}
  (Registry.create fresh absent unused) = Registry.entry experience candidate fresh false ,
    Registry.lookupInserted experience candidate fresh before ,
    refl , refl

bindingsSupported : ∀ {occupied experience before candidates after bindings} →
  Batch occupied experience before candidates after bindings → All (Supported experience after) bindings
bindingsSupported (done before) = []
bindingsSupported (next planned remainder) = let row , present , same , live = singleSupported planned
  in (row , batchPreserves remainder _ row present , same , live) ∷
     bindingsSupported remainder

keysExact : ∀ {occupied experience before candidates after bindings} →
  Batch occupied experience before candidates after bindings →
  map proj₁ bindings ≡ map candidateKey candidates
keysExact (done before) = refl
keysExact (next planned remainder) = cong (_ ∷_) (keysExact remainder)

countExact : ∀ {occupied experience before candidates after bindings} →
  Batch occupied experience before candidates after bindings → length bindings ≡ length candidates
countExact (done before) = refl
countExact (next planned remainder) = cong suc (countExact remainder)

lookupSupported : ∀ experience after bindings name identity → All (Supported experience after) bindings →
  Resolution.lookup name bindings ≡ just identity → Supported experience after (name , identity)
lookupSupported experience after [] name identity [] ()
lookupSupported experience after ((other , assigned) ∷ rest) name identity (supported ∷ supports) found
  with name ≟Text other
... | no different = lookupSupported experience after rest name identity supports found
... | yes refl with found
...   | refl = supported

resolvedReservation : ∀ {occupied experience before candidates after bindings} →
  Batch occupied experience before candidates after bindings → ∀ name identity →
  Resolution.lookup name bindings ≡ just identity → Supported experience after (name , identity)
resolvedReservation {experience = experience} {after = after} {bindings = bindings} batch name identity =
  lookupSupported experience after bindings name identity (bindingsSupported batch)

Declared : UUID → Registry.Registry → Candidate → Set
Declared experience after declaration = Σ Registry.Entry (λ row →
  Registry.lookup (experience , candidateKey declaration) after ≡ just row × Registry.ExistingValid declaration row)

singleDeclared : ∀ {before occupied experience declaration}
  (planned : Registry.Plan before occupied experience declaration) →
  Declared experience (Registry.publish planned) declaration
singleDeclared (Registry.reuse row found valid) = row , found , valid
singleDeclared {before} {experience = experience} {declaration}
  (Registry.create fresh absent unused) = Registry.entry experience declaration fresh false ,
  Registry.lookupInserted experience declaration fresh before , refl , refl

declarationsPreserved : ∀ {occupied experience before candidates after bindings} →
  Batch occupied experience before candidates after bindings → All (Declared experience after) candidates
declarationsPreserved (done before) = []
declarationsPreserved (next planned remainder) = let row , present , valid = singleDeclared planned
  in (row , batchPreserves remainder _ row present , valid) ∷
     declarationsPreserved remainder

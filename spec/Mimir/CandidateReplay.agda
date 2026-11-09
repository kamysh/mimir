{-# OPTIONS --safe #-}
-- Read-only reconstruction of a completed review's original answer. Retirement
-- prevents new publication, but cannot erase an unchanged saved declaration/ID.
module Mimir.CandidateReplay where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; cong₂)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.LearningCandidates using (Candidate; candidateKey; candidateEqual)
open import Mimir.OptionalTraversal using (nothingNotJust)
open import Mimir.Validation hiding (check)
import Mimir.Validation as Validation
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateBatch as Batch
import Mimir.ReviewResolution as Resolution
import Mimir.ApplicationStore as Store

Declared : ℕ → Registry.Registry → Candidate → Set
Declared experience registry declaration = Σ Registry.Entry (λ row →
  Registry.lookup (experience , candidateKey declaration) registry ≡ just row ×
  declaration ≡ Registry.Entry.declaration row)

Supported : ℕ → Registry.Registry → Text × ℕ → Set
Supported experience registry (name , identity) = Σ Registry.Entry (λ row →
  Registry.lookup (experience , name) registry ≡ just row × Registry.Entry.nodeID row ≡ identity)

fromPublishedDeclaration : ∀ {experience registry declaration} →
  Batch.Declared experience registry declaration → Declared experience registry declaration
fromPublishedDeclaration (row , present , same , live) = row , present , same

fromPublishedSupport : ∀ {experience registry binding} →
  Batch.Supported experience registry binding → Supported experience registry binding
fromPublishedSupport (row , present , same , live) = row , present , same

checkOne : ∀ experience registry declaration → Checked (Declared experience registry declaration)
checkOne experience registry declaration
  with Registry.lookup (experience , candidateKey declaration) registry in found
... | nothing = rejected (fault [] missingReference "candidate key is not reserved")
  (λ { (row , present , valid) → nothingNotJust present })
... | just row with Validation.check (fault [] wrongIdentity "candidate key has a different declaration")
  (candidateEqual declaration (Registry.Entry.declaration row))
...   | accepted valid = accepted (row , refl , valid)
...   | rejected failure invalid = rejected failure
  (λ { (other , present , valid)
         → invalid
           (subst (λ row → declaration ≡ Registry.Entry.declaration row)
            (sym (just-injective present)) valid)
     })

check : ∀ experience registry declarations → Checked (All (Declared experience registry) declarations)
check experience registry = allChecked (checkOne experience registry)

module Read (experience : ℕ) (registry : Registry.Registry) where
  binding : (declaration : Candidate) → Declared experience registry declaration → Text × ℕ
  binding declaration (row , present , valid) = candidateKey declaration , Registry.Entry.nodeID row

  bindings : (declarations : List Candidate) → All (Declared experience registry) declarations → Resolution.Registry
  bindings = Resolution.mapEvidence binding

  bindingSupported : ∀ declaration proof → Supported experience registry (binding declaration proof)
  bindingSupported declaration (row , present , same) = row , present , refl

  allSupported : ∀ declarations proofs → All (Supported experience registry) (bindings declarations proofs)
  allSupported = Resolution.mapEvidenceAll binding bindingSupported

  countExact : ∀ declarations proofs → length (bindings declarations proofs) ≡ length declarations
  countExact = Resolution.mapEvidenceLength binding

  bindingUnique : ∀ declaration first second → binding declaration first ≡ binding declaration second
  bindingUnique declaration (first , foundFirst , sameFirst) (second , foundSecond , sameSecond) =
    cong (λ row → candidateKey declaration , Registry.Entry.nodeID row)
      (just-injective (trans (sym foundFirst) foundSecond))

  bindingsUnique : ∀ declarations first second → bindings declarations first ≡ bindings declarations second
  bindingsUnique [] [] [] = refl
  bindingsUnique (declaration ∷ rest) (first ∷ firstRest) (second ∷ secondRest) =
    cong₂ _∷_ (bindingUnique declaration first second) (bindingsUnique rest firstRest secondRest)

readIDs : ℕ → Registry.Registry → List Candidate → Fault ⊎ Resolution.Registry
readIDs experience registry declarations with check experience registry declarations
... | rejected failure invalid = inj₁ failure
... | accepted proofs = inj₂ (Read.bindings experience registry declarations proofs)

returnedSupported : ∀ experience registry declarations ids →
  readIDs experience registry declarations ≡ inj₂ ids → All (Supported experience registry) ids
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
-- missing/changed-declaration failure. Its saved answer also survives retirement.
preparedReplayAccepted : ∀ {occupied experience before declarations after bindings} →
  Batch.Batch occupied experience before declarations after bindings →
  reported (check experience after declarations) ≡ []
preparedReplayAccepted {experience = experience} {declarations = declarations} {after = after} batch =
  noFalseRejection (check experience after declarations)
    (All.map (fromPublishedDeclaration {experience = experience} {registry = after}) (Batch.declarationsPreserved batch))

sameKeySameIdentity : ∀ experience registry name first second →
  Supported experience registry (name , first) →
  Supported experience registry (name , second) → first ≡ second
sameKeySameIdentity experience registry name first second
  (firstRow , firstFound , firstID)
  (secondRow , secondFound , secondID) = trans (sym firstID)
    (trans
     (cong Registry.Entry.nodeID
      (just-injective (trans (sym firstFound) secondFound)))
     secondID)

lookupSupported : ∀ experience registry bindings name identity → All (Supported experience registry) bindings →
  Resolution.lookup name bindings ≡ just identity → Supported experience registry (name , identity)
lookupSupported experience registry [] name identity [] ()
lookupSupported experience registry ((other , assigned) ∷ rest) name identity (supported ∷ supports) found
  with name ≟Text other
... | no different = lookupSupported experience registry rest name identity supports found
... | yes refl with found
...   | refl = supported

replayKeepsReservedIdentity : ∀ {occupied experience before declarations after bindings}
  (batch : Batch.Batch occupied experience before declarations after bindings) replayed name original actual →
  readIDs experience after declarations ≡ inj₂ replayed →
  Resolution.lookup name bindings ≡ just original →
  Resolution.lookup name replayed ≡ just actual → original ≡ actual
replayKeepsReservedIdentity {experience = experience} {declarations = declarations} {after = after}
  batch replayed name original actual readBack old new = sameKeySameIdentity experience after name original actual
    (fromPublishedSupport {experience = experience} {registry = after} {binding = name , original}
      (Batch.resolvedReservation batch name original old))
    (lookupSupported experience after replayed name actual
     (returnedSupported experience after declarations replayed readBack)
     new)

retiredLookup : ∀ ids name registry → Registry.lookup name (Store.retire ids registry) ≡
  Maybe.map (Store.retireEntry ids) (Registry.lookup name registry)
retiredLookup ids name [] = refl
retiredLookup ids name (row ∷ rest) with Registry.keyEqual name (Registry.entryKey row)
... | yes _ = refl
... | no _ = retiredLookup ids name rest

retiredDeclaration : ∀ ids experience registry declaration → Declared experience registry declaration →
  Declared experience (Store.retire ids registry) declaration
retiredDeclaration ids experience registry declaration (row , found , same) = Store.retireEntry ids row ,
  trans (retiredLookup ids (experience , candidateKey declaration) registry)
    (cong (Maybe.map (Store.retireEntry ids)) found) , same

retiredBindings : ∀ ids experience registry declarations proofs →
  Read.bindings experience (Store.retire ids registry) declarations
    (All.map (retiredDeclaration ids experience registry _) proofs) ≡ Read.bindings experience registry declarations proofs
retiredBindings ids experience registry [] [] = refl
retiredBindings ids experience registry (declaration ∷ rest) (proof ∷ proofs) =
  cong (_ ∷_) (retiredBindings ids experience registry rest proofs)

readFromEvidence : ∀ experience registry declarations proofs →
  readIDs experience registry declarations ≡ inj₂ (Read.bindings experience registry declarations proofs)
readFromEvidence experience registry declarations proofs with check experience registry declarations
... | rejected failure invalid = ⊥-elim (invalid proofs)
... | accepted actual = cong inj₂ (Read.bindingsUnique experience registry declarations actual proofs)

retirementPreservesCompletedAnswer : ∀ ids experience registry declarations answer →
  readIDs experience registry declarations ≡ inj₂ answer →
  readIDs experience (Store.retire ids registry) declarations ≡ inj₂ answer
retirementPreservesCompletedAnswer ids experience registry declarations answer observed
  with check experience registry declarations
... | rejected failure invalid with observed
...   | ()
retirementPreservesCompletedAnswer ids experience registry declarations answer observed | accepted proofs with observed
... | refl = trans
  (readFromEvidence experience (Store.retire ids registry) declarations
    (All.map (retiredDeclaration ids experience registry _) proofs))
  (cong inj₂ (retiredBindings ids experience registry declarations proofs))

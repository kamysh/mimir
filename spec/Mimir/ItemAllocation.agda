{-# OPTIONS --safe #-}
-- Persistent item identity is allocated by PostgreSQL, before the canonical
-- LearningSchema/SourceReview/ItemOwnerBatch validators. The SQL result is an
-- explicit input, not a claim that random UUIDs can never collide. The unique
-- database constraint may refuse allocation. Caller IDs can only reuse rows.
module Mimir.ItemAllocation where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation using (Fault; fault; key; index; Segment; wrongIdentity; missingReference;
  accepted; rejected; prependPath)
import Mimir.ItemOwners as Owners
import Mimir.LearningContracts as Contracts
import Mimir.LearningCandidates as LocalKeys

Keys = ℕ → Text → Maybe ℕ

writeKey : ℕ → Text → ℕ → Keys → Keys
writeKey experience name identity before other key with other ≟ experience
... | no _ = before other key
... | yes _ with key ≟Text name
...   | no _ = before other key
...   | yes _ = just identity

writeOwn : ∀ experience name identity before →
  writeKey experience name identity before experience name ≡ just identity
writeOwn experience name identity before with experience ≟ experience
... | no impossible = ⊥-elim (impossible refl)
... | yes _ with name ≟Text name
...   | no impossible = ⊥-elim (impossible refl)
...   | yes _ = refl

writeOtherExperience : ∀ experience name identity before other key →
  other ≢ experience → writeKey experience name identity before other key ≡ before other key
writeOtherExperience experience name identity before other key different
  with other ≟ experience
... | yes same = ⊥-elim (different same)
... | no _ = refl

module OwnerStore = Contracts.Ownership (Maybe Owners.Owner)

data Outcome : Set where
  refused : Fault → Outcome
  ready : ℕ → Keys → Owners.Registry → Outcome

ownerConflictField : Owners.Owner → Owners.Owner → Segment
ownerConflictField (experience , source , actor) (oldExperience , oldSource , oldActor)
  with source ≟Text oldSource
... | no _ = key "source_ref"
... | yes _ = key "actor"

-- A supplied UUID is never used to create a row. Existing UUID-only clients
-- can still correct a recorded item when its reserved provenance agrees.
reuse : Keys → Owners.Registry → ℕ → Owners.Owner → Outcome
reuse keys owners identity owner with owners identity
... | nothing = refused (fault (key "id" ∷ []) missingReference "new items require a local key; PostgreSQL allocates UUIDs")
... | just old@(oldExperience , oldSource , oldActor) with owner
...   | experience , source , actor with experience ≟ oldExperience
...     | no _ = refused (fault (key "id" ∷ []) missingReference "the item ID is not owned by this experience")
...     | yes _ with Owners.ownerEqual (experience , source , actor) old
...       | no _ = refused (fault (ownerConflictField (experience , source , actor) old ∷ []) wrongIdentity "item provenance is immutable")
...       | yes _ = ready identity keys owners

-- sqlIdentity is returned by INSERT ... DEFAULT ... RETURNING item_id. It is
-- consulted only for an unreserved (experience, key); retries use the ledger.
allocate : Keys → Owners.Registry → ℕ → Text → Text → Text → ℕ → Outcome
allocate keys owners experience name source actor sqlIdentity with keys experience name
... | just identity = reuse keys owners identity (experience , source , actor)
... | nothing with owners sqlIdentity
...   | just _ = refused (fault [] wrongIdentity "PostgreSQL item identity is occupied")
...   | nothing = ready sqlIdentity (writeKey experience name sqlIdentity keys)
    (OwnerStore.write sqlIdentity (just (experience , source , actor)) owners)

-- Optional id+key readback must agree with the reservation. Supplying a new
-- UUID together with a key cannot turn it into an allocation instruction.
reuseKey : Keys → Owners.Registry → ℕ → Text → ℕ → Text → Text → Outcome
reuseKey keys owners experience name identity source actor with keys experience name
... | nothing = refused (fault (key "id" ∷ []) missingReference "new items must omit id")
... | just assigned with identity ≟ assigned
...   | no _ = refused (fault (key "id" ∷ []) wrongIdentity "item key and UUID disagree")
...   | yes _ = reuse keys owners identity (experience , source , actor)

newIdentityComesFromPostgreSQL : ∀ keys owners experience name source actor sqlIdentity →
  keys experience name ≡ nothing → owners sqlIdentity ≡ nothing →
  allocate keys owners experience name source actor sqlIdentity ≡
    ready sqlIdentity (writeKey experience name sqlIdentity keys)
      (OwnerStore.write sqlIdentity (just (experience , source , actor)) owners)
newIdentityComesFromPostgreSQL keys owners experience name source actor sqlIdentity absent unused
  rewrite absent | unused = refl

reservedKeyIgnoresNewSQLIdentity : ∀ keys owners experience name source actor identity first second →
  keys experience name ≡ just identity →
  allocate keys owners experience name source actor first ≡
    allocate keys owners experience name source actor second
reservedKeyIgnoresNewSQLIdentity keys owners experience name source actor identity first second found
  rewrite found = refl

sameKeyRetryStable : ∀ keys owners experience name source actor identity →
  keys experience name ≡ just identity →
  owners identity ≡ just (experience , source , actor) →
  ∀ sqlIdentity → allocate keys owners experience name source actor sqlIdentity ≡
    ready identity keys owners
sameKeyRetryStable keys owners experience name source actor identity found owned sqlIdentity
  rewrite found | owned with experience ≟ experience
... | no impossible = ⊥-elim (impossible refl)
... | yes _ with Owners.ownerEqual (experience , source , actor) (experience , source , actor)
...   | no impossible = ⊥-elim (impossible refl)
...   | yes _ = refl

unreservedUUIDCannotAllocate : ∀ keys owners identity owner → owners identity ≡ nothing →
  reuse keys owners identity owner ≡
    refused (fault (key "id" ∷ []) missingReference "new items require a local key; PostgreSQL allocates UUIDs")
unreservedUUIDCannotAllocate keys owners identity owner unused rewrite unused = refl

-- Assessment-local references use precisely the enclosing experience's key
-- ledger. A missing reference refuses the whole plan; no partial list escapes.
data References (keys : Keys) (experience : ℕ) : List Text → List ℕ → Set where
  none : References keys experience [] []
  more : ∀ {name names identity identities} → LocalKeys.Trimmed name → keys experience name ≡ just identity →
    References keys experience names identities →
    References keys experience (name ∷ names) (identity ∷ identities)

resolveReferencesFrom : ∀ offset keys experience names → Fault ⊎ Σ (List ℕ) (References keys experience names)
resolveReferencesFrom offset keys experience [] = inj₂ ([] , none)
resolveReferencesFrom offset keys experience (name ∷ names) with LocalKeys.checkTrimmed name
... | rejected failure invalid = inj₁ (prependPath (index offset) failure)
... | accepted named with keys experience name in found
...   | nothing = inj₁ (fault (index offset ∷ []) missingReference "unknown learning item key")
...   | just identity with resolveReferencesFrom (suc offset) keys experience names
...     | inj₁ failure = inj₁ failure
...     | inj₂ (identities , supported) = inj₂ (identity ∷ identities , more named found supported)

resolveReferences : ∀ keys experience names → Fault ⊎ Σ (List ℕ) (References keys experience names)
resolveReferences keys experience names with LocalKeys.Keys.checkUnique names
... | rejected failure invalid = inj₁ failure
... | accepted unique = resolveReferencesFrom 0 keys experience names

referenceCountExact : ∀ {keys experience names identities} → References keys experience names identities →
  length names ≡ length identities
referenceCountExact none = refl
referenceCountExact (more named found remaining) rewrite referenceCountExact remaining = refl

allocationCollisionRefused : ∀ keys owners experience name source actor sqlIdentity old →
  keys experience name ≡ nothing → owners sqlIdentity ≡ just old →
  allocate keys owners experience name source actor sqlIdentity ≡
    refused (fault [] wrongIdentity "PostgreSQL item identity is occupied")
allocationCollisionRefused keys owners experience name source actor sqlIdentity old absent occupied
  rewrite absent | occupied = refl

-- Publication occurs only with the enclosing experience/review commit. Later
-- validation failure rolls back both the reservation and all review effects.
data Commit : Set where aborted committed : Commit

finishKeys : Keys → Outcome → Commit → Keys
finishKeys before result aborted = before
finishKeys before (refused _) committed = before
finishKeys before (ready identity proposed owners) committed = proposed

finishOwners : Owners.Registry → Outcome → Commit → Owners.Registry
finishOwners before result aborted = before
finishOwners before (refused _) committed = before
finishOwners before (ready identity keys proposed) committed = proposed

abortPreservesKeys : ∀ before result → finishKeys before result aborted ≡ before
abortPreservesKeys before result = refl

abortPreservesOwners : ∀ before result → finishOwners before result aborted ≡ before
abortPreservesOwners before result = refl

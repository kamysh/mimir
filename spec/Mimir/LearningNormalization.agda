{-# OPTIONS --safe #-}
-- Allocate on the locked transaction's PostgreSQL connection, then validate
-- the canonical payload. Reservations are staged in the same proposed world
-- as source/review writes; a failed plan never returns a partial new world.
module Mimir.LearningNormalization where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault; fault; missingReference; accepted; rejected)
import Mimir.SourceSchema as Source
import Mimir.LearningInput as Input
import Mimir.LearningSchema as L
import Mimir.ExperienceSchema as X
import Mimir.ReviewSchema as R
import Mimir.ItemAllocation as Allocation
import Mimir.ItemOwners as Owners
import Mimir.LearningStore as Store
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewObservation as Observation
import Mimir.LearningTransaction as Transaction
import Mimir.DatabaseTransaction as Database

install : Allocation.Keys → Owners.Registry → Store.World → Store.World
install keys owners before = record before
  { itemKeys = keys
  ; publication = record (Store.World.publication before) { owners = owners } }

installKeepsSources : ∀ keys owners before →
  Store.World.sources (install keys owners before) ≡ Store.World.sources before
installKeepsSources keys owners before = refl

installKeepsCurrent : ∀ keys owners before →
  Store.World.current (install keys owners before) ≡ Store.World.current before
installKeepsCurrent keys owners before = refl

abortedPlanKeepsKeys : ∀ before proposed actual → Database.Atomic before proposed Database.aborted actual →
  Store.World.itemKeys actual ≡ Store.World.itemKeys before
abortedPlanKeepsKeys before proposed actual Database.abortedNone = refl

abortedPlanKeepsOwners : ∀ before proposed actual → Database.Atomic before proposed Database.aborted actual →
  Publication.World.owners (Store.World.publication actual) ≡
    Publication.World.owners (Store.World.publication before)
abortedPlanKeepsOwners before proposed actual Database.abortedNone = refl

module For (Failure : Set) (invalid : Fault → Failure) (database : ℕ) where
  module T = Transaction.Over Store.World Observation.Snapshot Failure database 671942183

  bind : ∀ {A B} → T.Allocation (Failure ⊎ A) →
    (A → T.Allocation (Failure ⊎ B)) → T.Allocation (Failure ⊎ B)
  bind program next = T.bindAllocation program λ where
    (inj₁ failure) → T.resolved (inj₁ failure)
    (inj₂ value) → next value

  finishItem : Input.Item → Store.World → Allocation.Outcome →
    T.Allocation (Failure ⊎ (Store.World × L.LearningItem))
  finishItem input before (Allocation.refused failure) = T.resolved (inj₁ (invalid failure))
  finishItem input before (Allocation.ready identity keys owners) =
    T.resolved (inj₂ (install keys owners before , Input.canonicalItem identity input))

  owner : ℕ → Input.Item → Owners.Owner
  owner experience input = experience , Input.Item.reference input , Input.Item.actor input

  afterPostgres : ℕ → Text → Input.Item → Store.World → Failure ⊎ ℕ →
    T.Allocation (Failure ⊎ (Store.World × L.LearningItem))
  afterPostgres experience name input before (inj₁ failure) = T.resolved (inj₁ failure)
  afterPostgres experience name input before (inj₂ identity) = finishItem input before
    (Allocation.allocate (Store.World.itemKeys before)
      (Publication.World.owners (Store.World.publication before)) experience name
      (Input.Item.reference input) (Input.Item.actor input) identity)

  -- Every successful new reservation carries the actual returned database ID
  -- into both the key ledger and canonical item. This assumes only the two
  -- observed absences, not any property of a UUID generator.
  allocatedItemUsesPostgres : ∀ experience name input before identity →
    Store.World.itemKeys before experience name ≡ nothing →
    Publication.World.owners (Store.World.publication before) identity ≡ nothing →
    afterPostgres experience name input before (inj₂ identity) ≡ T.resolved (inj₂
      (install (Allocation.writeKey experience name identity (Store.World.itemKeys before))
        (Allocation.OwnerStore.write identity (just (owner experience input))
          (Publication.World.owners (Store.World.publication before))) before ,
       Input.canonicalItem identity input))
  allocatedItemUsesPostgres experience name input before identity absent unused = cong (finishItem input before)
    (Allocation.newIdentityComesFromPostgreSQL (Store.World.itemKeys before)
      (Publication.World.owners (Store.World.publication before)) experience name
      (Input.Item.reference input) (Input.Item.actor input) identity absent unused)

  byKey : ℕ → Text → Input.Item → Store.World →
    T.Allocation (Failure ⊎ (Store.World × L.LearningItem))
  byKey experience name input before with Store.World.itemKeys before experience name
  ... | just identity = finishItem input before
    (Allocation.reuse (Store.World.itemKeys before)
      (Publication.World.owners (Store.World.publication before)) identity (owner experience input))
  ... | nothing = T.reserve experience name (Input.Item.reference input) (Input.Item.actor input)
    (afterPostgres experience name input before)

  identified : ℕ → Input.Item → Store.World →
    T.Allocation (Failure ⊎ (Store.World × L.LearningItem))
  identified experience input before with Input.Item.identity input | Input.Item.localKey input
  ... | nothing | nothing = T.resolved (inj₁ (invalid
    (fault [] missingReference "new learning items require a local key")))
  ... | nothing | just name = byKey experience name input before
  ... | just identity | nothing = finishItem input before
    (Allocation.reuse (Store.World.itemKeys before)
      (Publication.World.owners (Store.World.publication before)) identity (owner experience input))
  ... | just identity | just name = finishItem input before
    (Allocation.reuseKey (Store.World.itemKeys before)
      (Publication.World.owners (Store.World.publication before)) experience name identity
      (Input.Item.reference input) (Input.Item.actor input))

  item : ℕ → Input.Item → Store.World →
    T.Allocation (Failure ⊎ (Store.World × L.LearningItem))
  item experience input before with Input.Item.localKey input
  ... | nothing = identified experience input before
  ... | just name with Source.checkNamed name
  ...   | rejected failure proof = T.resolved (inj₁ (invalid failure))
  ...   | accepted proof = identified experience input before

  itemAlreadyReserved : ∀ experience input before name identity →
    Input.Item.identity input ≡ nothing → Input.Item.localKey input ≡ just name →
    Source.NamedText name → Store.World.itemKeys before experience name ≡ just identity →
    Publication.World.owners (Store.World.publication before) identity ≡ just (owner experience input) →
    item experience input before ≡ T.resolved (inj₂ (before , Input.canonicalItem identity input))
  itemAlreadyReserved experience input before name identity omitted keyed named reserved owned
    rewrite keyed with Source.checkNamed name
  ... | rejected failure invalidName = ⊥-elim (invalidName named)
  ... | accepted valid rewrite omitted | keyed | reserved | owned
    with Owners.ownerEqual (owner experience input) (owner experience input)
  ...   | no impossible = ⊥-elim (impossible refl)
  ...   | yes same = cong
    (λ key → T.resolved (inj₂ (before , record (Input.canonicalItem identity input) { localKey = key }))) keyed

  unreservedItemRequestsPostgres : ∀ experience input before name →
    Input.Item.identity input ≡ nothing → Input.Item.localKey input ≡ just name →
    Source.NamedText name → Store.World.itemKeys before experience name ≡ nothing →
    item experience input before ≡ T.reserve experience name (Input.Item.reference input) (Input.Item.actor input)
      (afterPostgres experience name input before)
  unreservedItemRequestsPostgres experience input before name omitted keyed named absent
    rewrite keyed with Source.checkNamed name
  ... | rejected failure invalidName = ⊥-elim (invalidName named)
  ... | accepted valid rewrite omitted | keyed | absent = refl

  unreservedUUIDRefused : ∀ experience input before identity →
    Input.Item.identity input ≡ just identity → Input.Item.localKey input ≡ nothing →
    Publication.World.owners (Store.World.publication before) identity ≡ nothing →
    item experience input before ≡ T.resolved (inj₁ (invalid
      (fault [] missingReference "new items require a local key; PostgreSQL allocates UUIDs")))
  unreservedUUIDRefused experience input before identity supplied unnamed absent
    rewrite unnamed | supplied | unnamed | absent = refl

  items : ℕ → List Input.Item → Store.World →
    T.Allocation (Failure ⊎ (Store.World × List L.LearningItem))
  items experience [] before = T.resolved (inj₂ (before , []))
  items experience (input ∷ rest) before = bind (item experience input before) λ where
    (after , canonical) → bind (items experience rest after) λ where
      (final , remaining) → T.resolved (inj₂ (final , canonical ∷ remaining))

  -- The premise is discharged by itemAlreadyReserved for named retries and
  -- by the actual item reader for recorded UUID-only corrections. It retains
  -- every item, rather than checking a selected example or a chosen UUID.
  data RecordedItems (experience : ℕ) (before : Store.World) :
    List Input.Item → List L.LearningItem → Set where
    none : RecordedItems experience before [] []
    more : ∀ input rest assigned remaining →
      item experience input before ≡ T.resolved (inj₂ (before , assigned)) →
      RecordedItems experience before rest remaining →
      RecordedItems experience before (input ∷ rest) (assigned ∷ remaining)

  recordedItemsNeedNoAllocation : ∀ experience before raw assigned → RecordedItems experience before raw assigned →
    items experience raw before ≡ T.resolved (inj₂ (before , assigned))
  recordedItemsNeedNoAllocation experience before [] [] none = refl
  recordedItemsNeedNoAllocation experience before (input ∷ rest) (assigned ∷ remaining)
    (more .input .rest .assigned .remaining found restFound)
    rewrite found | recordedItemsNeedNoAllocation experience before rest remaining restFound = refl

  -- Named retries are justified by saved rows, not by assuming a successful
  -- result from the normalizer. Every item retains its actual saved identity.
  data NamedItems (experience : ℕ) (before : Store.World) :
    List Input.Item → List L.LearningItem → Set where
    noNamedItems : NamedItems experience before [] []
    namedItem : ∀ input rest name identity remaining →
      Input.Item.identity input ≡ nothing → Input.Item.localKey input ≡ just name →
      Source.NamedText name → Store.World.itemKeys before experience name ≡ just identity →
      Publication.World.owners (Store.World.publication before) identity ≡ just (owner experience input) →
      NamedItems experience before rest remaining →
      NamedItems experience before (input ∷ rest) (Input.canonicalItem identity input ∷ remaining)

  namedItemsRecorded : ∀ experience before raw assigned → NamedItems experience before raw assigned →
    RecordedItems experience before raw assigned
  namedItemsRecorded experience before raw assigned noNamedItems = none
  namedItemsRecorded experience before raw assigned
    (namedItem input rest name identity remaining omitted keyed valid saved owned others) =
    more input rest (Input.canonicalItem identity input) remaining
      (itemAlreadyReserved experience input before name identity omitted keyed valid saved owned)
      (namedItemsRecorded experience before rest remaining others)

  data ResolvedAssessments (keys : Allocation.Keys) (experience : ℕ) :
    List Input.Assessment → List L.Assessment → Set where
    noAssessments : ResolvedAssessments keys experience [] []
    moreAssessments : ∀ input rest identities remaining →
      Allocation.References keys experience (Input.Assessment.itemKeys input) identities →
      ResolvedAssessments keys experience rest remaining →
      ResolvedAssessments keys experience (input ∷ rest) (Input.canonicalAssessment input identities ∷ remaining)

  assessments : ∀ keys experience raw → Fault ⊎ Σ (List L.Assessment) (ResolvedAssessments keys experience raw)
  assessments keys experience [] = inj₂ ([] , noAssessments)
  assessments keys experience (input ∷ rest)
    with Allocation.resolveReferences keys experience (Input.Assessment.itemKeys input)
  ... | inj₁ failure = inj₁ failure
  ... | inj₂ (identities , evidence) with assessments keys experience rest
  ...   | inj₁ failure = inj₁ failure
  ...   | inj₂ (remaining , supported) = inj₂
    (Input.canonicalAssessment input identities ∷ remaining , moreAssessments input rest identities remaining evidence supported)

  experience : Input.Experience → Store.World →
    T.Allocation (Failure ⊎ (Store.World × X.Experience))
  experience input before = bind (items (Input.Experience.identity input) (Input.Experience.items input) before) λ where
    (after , assigned) → T.resolved (inj₂ (after , Input.canonicalExperience input assigned))

  recordedExperienceNeedsNoAllocation : ∀ input before assigned →
    RecordedItems (Input.Experience.identity input) before (Input.Experience.items input) assigned →
    experience input before ≡ T.resolved (inj₂ (before , Input.canonicalExperience input assigned))
  recordedExperienceNeedsNoAllocation input before assigned recorded
    rewrite recordedItemsNeedNoAllocation (Input.Experience.identity input) before
      (Input.Experience.items input) assigned recorded = refl

  finishReview : Input.Review → Store.World → List L.LearningItem → T.Allocation (Failure ⊎ (Store.World × R.Review))
  finishReview input after assigned with assessments (Store.World.itemKeys after) (Input.Review.experienceID input)
    (Input.Review.assessments input)
  ... | inj₁ failure = T.resolved (inj₁ (invalid failure))
  ... | inj₂ (resolved , supported) = T.resolved (inj₂ (after , Input.canonicalReview input assigned resolved))

  review : Input.Review → Store.World → T.Allocation (Failure ⊎ (Store.World × R.Review))
  review input before = bind (items (Input.Review.experienceID input) (Input.Review.extracted input) before) λ where
    (after , assigned) → finishReview input after assigned

  recordedReviewNeedsNoAllocation : ∀ input before assigned resolved supported →
    RecordedItems (Input.Review.experienceID input) before (Input.Review.extracted input) assigned →
    assessments (Store.World.itemKeys before) (Input.Review.experienceID input) (Input.Review.assessments input)
      ≡ inj₂ (resolved , supported) →
    review input before ≡ T.resolved (inj₂ (before , Input.canonicalReview input assigned resolved))
  recordedReviewNeedsNoAllocation input before assigned resolved supported recorded references
    rewrite recordedItemsNeedNoAllocation (Input.Review.experienceID input) before
      (Input.Review.extracted input) assigned recorded | references = refl

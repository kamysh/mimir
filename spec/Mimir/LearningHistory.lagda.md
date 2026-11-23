# How Mimir returns experience history

`experience_history` takes one experience UUID. It returns two arrays,
`experiences` and `reviews`. Each array lists its own saved revisions in
ascending order. An entry includes the revision number, the stored payload,
and the time that version was created. Previously saved review versions stay
in history when a later experience correction makes them inactive.

Both arrays describe one PostgreSQL statement snapshot. For example, if a
correction and its review commit while a history request is in progress, that
request cannot show the new review with only the earlier experience versions.
The database's foreign key supplies the corresponding experience version for
every review. The checked read requires that relationship within its rows.
An unknown UUID returns two empty arrays. A failed database read produces an
operation error.

Historical payloads are returned as stored JSON data, including fields from
an older schema. Reading them does not apply today's validation rules or
reconstruct an old payload from the current experience. The
[MCP reply encoder](ApplicationOutput.agda) adds the revision and timestamp,
and [the Rust store](../../crates/core/src/store/learning.rs) obtains both sets
of rows in one query.

```agda
{-# OPTIONS --safe #-}
module Mimir.LearningHistory where

open import Data.List using (List; []; _∷_; map; filterᵇ)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer using (ℤ; +_; ∣_∣)
open import Data.Product using (_×_)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Mimir.ReviewSchema using (Review)
import Mimir.LearningStore as Store
import Mimir.ExperienceRead as Read
import Mimir.ReviewObservation as Observation
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewPreparationPublication as Publication
import Mimir.AssessmentRead as Assessment
import Mimir.LearningHistoryWire as Wire
import Mimir.StructuredValue as V

record Entry : Set where
  constructor entry
  field revision : ℤ; payload : V.Value; createdAt : ℤ

references : Wire.Row → Wire.Row → Set
references review source =
  (Wire.Row.experience review ≡ Wire.Row.experience source) ×
  (Wire.Row.sourceRevision review ≡ Wire.Row.revision source)

record Rows : Set where
  constructor rows
  field
    sources reviews : List Wire.Row
    referenced : All (λ review → Any (references review) sources) reviews

record Result : Set where
  constructor history
  field sources reviews : List Entry

insert : Entry → List Entry → List Entry
insert item [] = item ∷ []
insert item (next ∷ rest) with Entry.revision item Integer.≤? Entry.revision next
... | yes _ = item ∷ next ∷ rest
... | no _ = next ∷ insert item rest

sort : List Entry → List Entry
sort [] = []
sort (item ∷ rest) = insert item (sort rest)

select : UUID → List Wire.Row → List Entry
select id entries = sort (map (λ item → entry
  (Wire.Row.revision item) (Wire.Row.payload item) (Wire.Row.createdAt item))
  (filterᵇ (λ item → does (id ≟UUID Wire.Row.experience item)) entries))

getHistory : UUID → Rows → Result
getHistory id observed = history (select id (Rows.sources observed)) (select id (Rows.reviews observed))
```

## Current review

The separate current-review projection returns a review only when it refers
to the current source revision. History also includes earlier reviews.

```agda
record CurrentReview : Set where
  constructor currentReview
  field state : Observation.Snapshot; applied : Maybe Review

matchingReview : Observation.Snapshot → Maybe Ledger.Version → Maybe Review
matchingReview current nothing = nothing
matchingReview current (just v) with (+ Ledger.Version.source v) Integer.≟ Observation.Snapshot.revision current
... | yes same = just (Ledger.Version.applied v)
... | no stale = nothing

learningReview : UUID → Store.World → Maybe CurrentReview
learningReview id w with Read.get id (Store.World.current w)
... | nothing = nothing
... | just current = just (currentReview current
  (matchingReview current (Assessment.version ∣ Observation.Snapshot.reviewRevision current ∣
    (Ledger.World.histories (Publication.World.ledger (Store.World.publication w)) id))))

```

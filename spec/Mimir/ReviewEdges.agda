{-# OPTIONS --safe #-}
-- Belief-to-belief edges owned by a review. Independent edges have no owner.
-- GROUNDS and other non-belief overlays are outside this collection and must
-- be preserved by the native MATCH predicate. Corrections replace exactly the
-- selected experience's edges; CONTRADICTS creates both directed endpoints.
module Mimir.ReviewEdges where

open import Data.List using (List; []; _∷_; _++_; filter)
import Data.List.Properties as Lists
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional.Properties as Membership
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllProperties
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as MaybeProperties
open import Data.Nat using (ℕ; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Mimir.Binary64 using (Number)
open import Mimir.ReviewSchema using (Link; link; Relation; supports; defeats; causes; contradicts)

record Edge : Set where
  constructor edge
  field
    owner : Maybe ℕ
    from to : ℕ
    relation : Relation
    weight : Number

Foreign : ℕ → Edge → Set
Foreign experience e = Edge.owner e ≢ just experience

foreign? : ∀ experience e → Dec (Foreign experience e)
foreign? experience e with MaybeProperties.≡-dec _≟_ (Edge.owner e) (just experience)
... | yes same = no (λ different → different same)
... | no different = yes different

retained : ℕ → List Edge → List Edge
retained experience = filter (foreign? experience)

expand : ℕ → Link → List Edge
expand experience (link from to supports weight) = edge (just experience) from to supports weight ∷ []
expand experience (link from to defeats weight) = edge (just experience) from to defeats weight ∷ []
expand experience (link from to causes weight) = edge (just experience) from to causes weight ∷ []
expand experience (link from to contradicts weight) = edge (just experience) from to contradicts weight ∷
  edge (just experience) to from contradicts weight ∷ []

creations : ℕ → List Link → List Edge
creations experience [] = []
creations experience (declaration ∷ rest) = expand experience declaration ++ creations experience rest

replace : ℕ → List Link → List Edge → List Edge
replace experience links before = creations experience links ++ retained experience before

expandOwned : ∀ experience declaration → All (λ e → Edge.owner e ≡ just experience) (expand experience declaration)
expandOwned experience (link from to supports weight) = refl ∷ []
expandOwned experience (link from to defeats weight) = refl ∷ []
expandOwned experience (link from to causes weight) = refl ∷ []
expandOwned experience (link from to contradicts weight) = refl ∷ refl ∷ []

creationsOwned : ∀ experience links → All (λ e → Edge.owner e ≡ just experience) (creations experience links)
creationsOwned experience [] = []
creationsOwned experience (declaration ∷ rest) = AllProperties.++⁺ (expandOwned experience declaration)
  (creationsOwned experience rest)

retainedForeign : ∀ experience before → All (Foreign experience) (retained experience before)
retainedForeign experience before = AllProperties.all-filter (foreign? experience) before

foreignPreserved : ∀ experience before e → e ∈ before → Foreign experience e → e ∈ retained experience before
foreignPreserved experience before e member foreign = Membership.∈-filter⁺ (foreign? experience) member foreign

creationsRemoved : ∀ experience links → retained experience (creations experience links) ≡ []
creationsRemoved experience links = Lists.filter-none (foreign? experience)
  (All.map (λ owned foreign → foreign owned)
   (creationsOwned experience links))

retentionIdempotent : ∀ experience before → retained experience (retained experience before) ≡ retained experience before
retentionIdempotent experience before = Lists.filter-idem (foreign? experience) before

replacementForgetsOld : ∀ experience newer older before →
  replace experience newer (replace experience older before) ≡ replace experience newer before
replacementForgetsOld experience newer older before = cong (creations experience newer ++_)
  (Relation.Binary.PropositionalEquality.trans
   (Lists.filter-++ (foreign? experience) (creations experience older)
    (retained experience before))
   (Relation.Binary.PropositionalEquality.cong₂ _++_
    (creationsRemoved experience older)
    (retentionIdempotent experience before)))

forward : ℕ → Link → Edge
forward experience declaration = edge (just experience) (Link.from declaration) (Link.to declaration)
  (Link.relation declaration) (Link.weight declaration)

reverse : ℕ → Link → Edge
reverse experience declaration = edge (just experience) (Link.to declaration) (Link.from declaration)
  contradicts (Link.weight declaration)

data Generated (experience : ℕ) (declaration : Link) : Edge → Set where
  direct : Generated experience declaration (forward experience declaration)
  mirrored : Link.relation declaration ≡ contradicts → Generated experience declaration (reverse experience declaration)

expandGenerated : ∀ experience declaration → All (Generated experience declaration) (expand experience declaration)
expandGenerated experience (link from to supports weight) = direct ∷ []
expandGenerated experience (link from to defeats weight) = direct ∷ []
expandGenerated experience (link from to causes weight) = direct ∷ []
expandGenerated experience (link from to contradicts weight) = direct ∷ mirrored refl ∷ []

creationsGenerated : ∀ experience links →
  All (λ e → Any (λ declaration → Generated experience declaration e) links) (creations experience links)
creationsGenerated experience [] = []
creationsGenerated experience (declaration ∷ rest) = AllProperties.++⁺
  (All.map here (expandGenerated experience declaration))
  (All.map there (creationsGenerated experience rest))

forwardPresent : ∀ experience declaration → forward experience declaration ∈ expand experience declaration
forwardPresent experience (link from to supports weight) = here refl
forwardPresent experience (link from to defeats weight) = here refl
forwardPresent experience (link from to causes weight) = here refl
forwardPresent experience (link from to contradicts weight) = here refl

everyDeclaredLink : ∀ experience links declaration → declaration ∈ links →
  forward experience declaration ∈ creations experience links
everyDeclaredLink experience (declaration ∷ rest) .declaration (here refl) = Membership.∈-++⁺ˡ (forwardPresent experience declaration)
everyDeclaredLink experience (other ∷ rest) declaration (there member) = Membership.∈-++⁺ʳ (expand experience other)
  (everyDeclaredLink experience rest declaration member)

reversePresent : ∀ experience declaration → Link.relation declaration ≡ contradicts →
  reverse experience declaration ∈ expand experience declaration
reversePresent experience (link from to contradicts weight) refl = there (here refl)

everyContradictionReversed : ∀ experience links declaration → declaration ∈ links →
  Link.relation declaration ≡ contradicts → reverse experience declaration ∈ creations experience links
everyContradictionReversed experience (declaration ∷ rest) .declaration (here refl) relation = Membership.∈-++⁺ˡ (reversePresent experience declaration relation)
everyContradictionReversed experience (other ∷ rest) declaration (there member) relation = Membership.∈-++⁺ʳ (expand experience other)
  (everyContradictionReversed experience rest declaration member
   relation)

-- Every result edge is justified by a new declaration or belongs to someone
-- else. No obsolete edge owned by the corrected experience can survive alone.
replacementProvenance : ∀ experience links before →
  All (λ e → Any (λ declaration → Generated experience declaration e) links ⊎ Foreign experience e)
    (replace experience links before)
replacementProvenance experience links before = AllProperties.++⁺
  (All.map inj₁ (creationsGenerated experience links))
  (All.map inj₂ (retainedForeign experience before))

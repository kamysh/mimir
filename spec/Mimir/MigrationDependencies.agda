{-# OPTIONS --safe #-}
-- Dangling-reference admission before scheduling. HashMap iteration order
-- can affect which diagnostic is reported; it cannot affect admission.
module Mimir.MigrationDependencies where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as Perm
open import Mimir.Collections using (module Equality)

module Validate (Name Item : Set) (equal : DecidableEquality Name)
  (name : Item → Name) (requires : Item → List Name) where
  module Names = Equality Name equal

  Resolved : List Name → Item → Set
  Resolved known item = All (λ dependency → Names.Present dependency known) (requires item)

  data Missing (known : List Name) : List Name → Set where
    here : ∀ {dependency rest} → ¬ Names.Present dependency known → Missing known (dependency ∷ rest)
    later : ∀ {dependency rest} → Names.Present dependency known → Missing known rest →
      Missing known (dependency ∷ rest)

  missingName : ∀ {known requirements} → Missing known requirements → Name
  missingName (here {dependency} _) = dependency
  missingName (later _ remaining) = missingName remaining

  inspect : ∀ known requirements → Missing known requirements ⊎ All (λ dependency → Names.Present dependency known) requirements
  inspect known [] = inj₂ []
  inspect known (dependency ∷ rest) with Names.present? dependency known
  ... | no absent = inj₁ (here absent)
  ... | yes found with inspect known rest
  ...   | inj₁ absent = inj₁ (later found absent)
  ...   | inj₂ remaining = inj₂ (found ∷ remaining)

  resolvedNotMissing : ∀ {known requirements} →
    All (λ dependency → Names.Present dependency known) requirements → Missing known requirements → ⊥
  resolvedNotMissing (found ∷ _) (here absent) = absent found
  resolvedNotMissing (_ ∷ remaining) (later _ missing) = resolvedNotMissing remaining missing

  data Dangling (known : List Name) : List Item → Set where
    here : ∀ {item rest} → Missing known (requires item) → Dangling known (item ∷ rest)
    later : ∀ {item rest} → Resolved known item → Dangling known rest → Dangling known (item ∷ rest)

  diagnostic : ∀ {known items} → Dangling known items → Name × Name
  diagnostic (here {item} missing) = name item , missingName missing
  diagnostic (later _ remaining) = diagnostic remaining

  inspectAll : ∀ known items → Dangling known items ⊎ All (Resolved known) items
  inspectAll known [] = inj₂ []
  inspectAll known (item ∷ rest) with inspect known (requires item)
  ... | inj₁ missing = inj₁ (here missing)
  ... | inj₂ resolved with inspectAll known rest
  ...   | inj₁ missing = inj₁ (later resolved missing)
  ...   | inj₂ remaining = inj₂ (resolved ∷ remaining)

  resolvedNotDangling : ∀ {known items} → All (Resolved known) items → Dangling known items → ⊥
  resolvedNotDangling (resolved ∷ _) (here missing) = resolvedNotMissing resolved missing
  resolvedNotDangling (_ ∷ remaining) (later _ missing) = resolvedNotDangling remaining missing

  check : List Name → List Item → (Name × Name) ⊎ ⊤
  check known items with inspectAll known items
  ... | inj₁ missing = inj₁ (diagnostic missing)
  ... | inj₂ resolved = inj₂ tt

  sound : ∀ known items → check known items ≡ inj₂ tt → All (Resolved known) items
  sound known items with inspectAll known items
  ... | inj₁ missing = λ ()
  ... | inj₂ resolved = λ _ → resolved

  complete : ∀ known items → All (Resolved known) items → check known items ≡ inj₂ tt
  complete known items resolved with inspectAll known items
  ... | inj₁ missing = ⊥-elim (resolvedNotDangling resolved missing)
  ... | inj₂ admitted = refl

  iterationOrderDoesNotChangeAdmission : ∀ known original iteration → original Perm.↭ iteration →
    check known original ≡ inj₂ tt → check known iteration ≡ inj₂ tt
  iterationOrderDoesNotChangeAdmission known original iteration permutation accepted =
    complete known iteration (Perm.All-resp-↭ permutation (sound known original accepted))

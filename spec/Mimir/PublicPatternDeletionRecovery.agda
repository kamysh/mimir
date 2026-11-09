{-# OPTIONS --safe #-}
-- The public pattern deletion uses the registered original request. Its goal
-- is the existing whole-world deletion intent and the original saved answer.
module Mimir.PublicPatternDeletionRecovery where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.GraphDeletion as Delete
import Mimir.PublicRequest as Public
import Mimir.StandardLibrary as Library
import Mimir.ToolCatalog as Tools
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.RecoverableStoreStep as Step

module Registered (library : Library.Contract) where
  module Decode = Public.Decode library
  module Intent = Delete.PatternRecovery

  descriptor = Admission.descriptor (toList "delete_pattern") (toList "store.delete_pattern")
    (toList "[\"store.delete_pattern\",null]")
  key : ℕ → Text
  key _ = Admission.Descriptor.key descriptor
  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token ()

  invalid : Validation.Fault
  invalid = Validation.fault [] Validation.wrongIdentity
    "Read this token's original delete_pattern arguments and outcome. Ask the user before cancelling unfinished work and reserving a corrected request; do not rewrite the binding."

  original : ℕ → Step.Registration → Validation.Fault ⊎ ℕ
  original token registration with Admission.resolve descriptor token registration
  ... | inj₁ diagnostic = inj₁ diagnostic
  ... | inj₂ (_ , binding) with Store.BindingRow.settings binding
  ... | Wire.object [] with Decode.readBoundTool Tools.deletePattern (Store.BindingRow.arguments binding)
  ... | inj₁ diagnostic = inj₁ diagnostic
  ... | inj₂ (Public.delete Delete.patternNode identity) = inj₂ identity
  ... | inj₂ _ = inj₁ invalid
  original token registration | inj₂ (_ , binding) | _ = inj₁ invalid

  admit : ℕ → Step.Registration → Maybe Validation.Fault
  admit token registration with original token registration
  ... | inj₁ diagnostic = just diagnostic
  ... | inj₂ _ = nothing

  requested : ℕ → ℕ → Intent.Input
  requested = Intent.input

  decide : ℕ → Store.World → Validation.Fault ⊎ (Store.World × Wire.Value)
  decide token before with original token (Step.registration before)
  ... | inj₁ diagnostic = inj₁ diagnostic
  ... | inj₂ identity = inj₂ (Intent.apply (requested token identity) before)

  keepsJournal : ∀ token before changed reply → decide token before ≡ inj₂ (changed , reply) →
    Store.World.operations changed ≡ Store.World.operations before
  keepsJournal token before changed reply accepted with original token (Step.registration before)
  ... | inj₁ diagnostic with accepted
  ... | ()
  keepsJournal token before ._ ._ refl | inj₂ identity = Intent.preservesJournal (requested token identity) before

  module Saved = Step.Admitted ℕ Validation.Fault (λ token → token) key distinct decide keepsJournal admit

  FreshGoal : ℕ → ℕ → Store.World → Store.World → Saved.Reply → Set
  FreshGoal token identity before after reply =
    after ≡ Saved.Kernel.publication token (Intent.desired (requested token identity) before)
      (Intent.answer (requested token identity) before) ×
    reply ≡ Step.done (Intent.answer (requested token identity) before)

  decidesOriginal : ∀ token identity before → original token (Step.registration before) ≡ inj₂ identity →
    decide token before ≡ inj₂ (Intent.apply (requested token identity) before)
  decidesOriginal token identity before bound rewrite bound = refl

  freshMeaning : ∀ token identity before → original token (Step.registration before) ≡ inj₂ identity →
    FreshGoal token identity before (proj₁ (Saved.Kernel.fresh token before)) (proj₂ (Saved.Kernel.fresh token before))
  freshMeaning token identity before bound rewrite decidesOriginal token identity before bound = refl , refl

  Goal : ℕ → Store.World → Store.World → Saved.Reply → Set
  Goal token before after reply with original token (Step.registration before)
  ... | inj₁ diagnostic = after ≡ before × reply ≡ Step.needsInput diagnostic
  ... | inj₂ identity with Store.lookupCancellation before token
  ... | just cancellation = after ≡ before × reply ≡ Step.cancelled cancellation
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing = FreshGoal token identity before after reply

  meaning : ∀ token before → Goal token before (proj₁ (Saved.execute token before)) (proj₂ (Saved.execute token before))
  meaning token before with original token (Step.registration before) in bound
  ... | inj₁ diagnostic = refl , refl
  ... | inj₂ identity with Store.lookupCancellation before token
  ... | just cancellation = refl , refl
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = refl , refl
  ... | just _ | nothing = refl , refl
  ... | nothing | just _ = refl , refl
  ... | nothing | nothing = freshMeaning token identity before bound

  module Certified = Saved.Certified Goal meaning
  operation = Certified.operation

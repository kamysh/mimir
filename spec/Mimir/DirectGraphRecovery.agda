{-# OPTIONS --safe #-}
-- Direct relationships add their requested edges and retain every other table.
-- Repeating a token returns its saved answer, rather than adding more edges.
module Mimir.DirectGraphRecovery where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text)
open import Mimir.Binary64 using (Number)
open import Mimir.RecordDecoding using (_>>=_)
import Mimir.ApplicationStore as Store
import Mimir.ApplicationFloat as Numeric
import Mimir.GraphNumerics as Numbers
import Mimir.GraphWrites as Writes
import Mimir.RetrievalRanking as Ranking
import Mimir.ReviewSchema as R
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.StructuredValue as Wire
import Mimir.StandardLibrary as Conversion
import Mimir.RecordDecoding as Decode
import Mimir.PublicInput as Public
import Mimir.JsonObjects as Objects
import Mimir.Validation as Validation

data Kind : Set where
  support cause contradiction : Kind

relation : Kind → R.Relation
relation support = R.supports
relation cause = R.causes
relation contradiction = R.contradicts

name : Kind → Text
name support = toList "record_support"
name cause = toList "record_cause"
name contradiction = toList "record_contradiction"

descriptor : Kind → Admission.Descriptor
descriptor support = Admission.descriptor (name support) (toList "store.insert_edge") (toList "[\"store.insert_edge\",null]")
descriptor cause = Admission.descriptor (name cause) (toList "store.insert_edge") (toList "[\"store.insert_edge\",null]")
descriptor contradiction = Admission.descriptor (name contradiction) (toList "store.insert_contradicts") (toList "[\"store.insert_contradicts\",null]")

record Request : Set where
  constructor request
  field from to : ℕ; weight : Number

answer : Wire.Value
answer = Wire.object ((toList "ok" , Wire.boolean true) ∷ [])

invalid : Validation.Fault
invalid = Validation.fault (Validation.key "weight" ∷ []) Validation.invalidNumber
  "Supply a finite weight between 0 and 1 inclusive. Correct the request or ask the user; no relationship was saved."

endpointField : Kind → Bool → String
endpointField support true = "from_id"
endpointField support false = "to_id"
endpointField cause true = "from_id"
endpointField cause false = "to_id"
endpointField contradiction true = "id_a"
endpointField contradiction false = "id_b"

-- Identity spelling is an existing standard-library boundary. Mimir chooses
-- the actual missing endpoint and its public field, including the distinct
-- contradiction field names; it does not blame an unspecified pair of IDs.
missing : (ℕ → Text) → Kind → Bool → ℕ → Validation.Fault
missing uuidText kind first identity = Validation.problem
  (Validation.key (endpointField kind first) ∷ []) Validation.missingReference
  (toList "The requested belief " ++ uuidText identity ++ toList " was not found in Mimir.")

module Business (kind : Kind) (uuidText : ℕ → Text) where
  open Request
  Outcome = Validation.Fault ⊎ (Store.World × Wire.Value)

  -- This is the complete observable outcome, independently of transaction and
  -- journal steps. CONTRADICTS requests add both directions atomically.
  Goal : Request → Store.World → Outcome → Set
  Goal input before outcome with Numeric.number (weight input)
  ... | nothing = outcome ≡ inj₁ invalid
  ... | just value with Numbers.probability value
  ... | false = outcome ≡ inj₁ invalid
  ... | true with Ranking.lookup (from input) (Store.beliefs before) | Ranking.lookup (to input) (Store.beliefs before)
  ... | nothing | _ = outcome ≡ inj₁ (missing uuidText kind true (from input))
  ... | just _ | nothing = outcome ≡ inj₁ (missing uuidText kind false (to input))
  ... | just _ | just _ = outcome ≡ inj₂
    (Writes.addEdges (Writes.directEdges (from input) (to input) (relation kind) (weight input)) before , answer)

  checked : ∀ input before → Σ Outcome (Goal input before)
  checked input before with Numeric.number (weight input)
  ... | nothing = inj₁ invalid , refl
  ... | just value with Numbers.probability value
  ... | false = inj₁ invalid , refl
  ... | true with Ranking.lookup (from input) (Store.beliefs before) | Ranking.lookup (to input) (Store.beliefs before)
  ... | nothing | _ = inj₁ (missing uuidText kind true (from input)) , refl
  ... | just _ | nothing = inj₁ (missing uuidText kind false (to input)) , refl
  ... | just _ | just _ = inj₂
    (Writes.addEdges (Writes.directEdges (from input) (to input) (relation kind) (weight input)) before , answer) , refl

  journalUnchanged : ∀ input before after reply → proj₁ (checked input before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  journalUnchanged input before after reply accepted with Numeric.number (weight input)
  ... | nothing with accepted
  ... | ()
  journalUnchanged input before after reply accepted | just value with Numbers.probability value
  ... | false with accepted
  ... | ()
  journalUnchanged input before after reply accepted | just value | true
    with Ranking.lookup (from input) (Store.beliefs before) | Ranking.lookup (to input) (Store.beliefs before)
  ... | nothing | _ with accepted
  ... | ()
  journalUnchanged input before after reply accepted | just value | true | just _ | nothing with accepted
  ... | ()
  journalUnchanged input before after reply refl | just value | true | just _ | just _ = refl

module Registered (conversion : Conversion.Contract) (uuidText : ℕ → Text) (kind : Kind) where
  module B = Business kind uuidText
  module N = Public.Numbers conversion
  key : ℕ → Text
  key _ = Admission.Descriptor.key (descriptor kind)
  distinctKey : ∀ selected → Admission.Descriptor.key (descriptor selected) ≡ Step.resultKey → ⊥
  distinctKey support ()
  distinctKey cause ()
  distinctKey contradiction ()
  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token = distinctKey kind

  decodeFor : Kind → Wire.Value → Validation.Fault ⊎ Request
  decodeFor support raw = directed raw
    where
    directed = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
      (toList "from_id" ∷ toList "to_id" ∷ toList "weight" ∷ []) (λ view →
      Public.required "from_id" (Public.readUUID conversion) view >>= λ from →
      Public.required "to_id" (Public.readUUID conversion) view >>= λ to →
      Public.required "weight" N.number view >>= λ weight → inj₂ (request from to weight))
  decodeFor cause raw = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
      (toList "from_id" ∷ toList "to_id" ∷ toList "weight" ∷ []) (λ view →
      Public.required "from_id" (Public.readUUID conversion) view >>= λ from →
      Public.required "to_id" (Public.readUUID conversion) view >>= λ to →
      Public.required "weight" N.number view >>= λ weight → inj₂ (request from to weight)) raw
  decodeFor contradiction raw = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
      (toList "id_a" ∷ toList "id_b" ∷ toList "weight" ∷ []) (λ view →
      Public.required "id_a" (Public.readUUID conversion) view >>= λ from →
      Public.required "id_b" (Public.readUUID conversion) view >>= λ to →
      N.castNatural 1 >>= λ one → Public.defaulted "weight" one N.number view >>= λ weight →
      inj₂ (request from to weight)) raw

  original : ℕ → Step.Registration → Validation.Fault ⊎ Request
  original token registration with Admission.resolve (descriptor kind) token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (_ , binding) with Store.BindingRow.settings binding
  ... | Wire.object [] = decodeFor kind (Store.BindingRow.arguments binding)
  ... | _ = inj₁ (Validation.fault (Validation.key "settings" ∷ []) Validation.unknownField
    "Direct relationships have no per-request settings. Read the original binding and outcome; ask the user to resolve this token before changing its request.")

  admit : ℕ → Step.Registration → Maybe Validation.Fault
  admit token registration with original token registration
  ... | inj₁ fault = just fault
  ... | inj₂ _ = nothing

  decide : ℕ → Store.World → B.Outcome
  decide token before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ input = proj₁ (B.checked input before)

  keepsJournal : ∀ token before after reply → decide token before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  keepsJournal token before after reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  keepsJournal token before after reply accepted | inj₂ input = B.journalUnchanged input before after reply accepted

  module Saved = Step.Admitted ℕ Validation.Fault (λ token → token) key distinct decide keepsJournal admit

  FreshGoal : ℕ → Request → Store.World → Store.World → Saved.Reply → Set
  FreshGoal token input before after (Step.done reply) = Σ Store.World (λ changed →
    B.Goal input before (inj₂ (changed , reply)) × after ≡ Saved.Kernel.publication token changed reply)
  FreshGoal token input before after (Step.needsInput fault) = after ≡ before × B.Goal input before (inj₁ fault)
  FreshGoal token input before after _ = ⊥

  originalDecides : ∀ token before input → original token (Step.registration before) ≡ inj₂ input →
    decide token before ≡ proj₁ (B.checked input before)
  originalDecides token before input bound rewrite bound = refl

  freshMeaning : ∀ token input before → original token (Step.registration before) ≡ inj₂ input →
    FreshGoal token input before (proj₁ (Saved.Kernel.fresh token before)) (proj₂ (Saved.Kernel.fresh token before))
  freshMeaning token input before bound rewrite originalDecides token before input bound with B.checked input before
  ... | inj₁ fault , correct = refl , correct
  ... | inj₂ (changed , reply) , correct = changed , correct , refl

  Goal : ℕ → Store.World → Store.World → Saved.Reply → Set
  Goal token before after reply with original token (Step.registration before)
  ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput fault
  ... | inj₂ input with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing = FreshGoal token input before after reply

  meaning : ∀ token before → Goal token before (proj₁ (Saved.execute token before)) (proj₂ (Saved.execute token before))
  meaning token before with original token (Step.registration before) in bound
  ... | inj₁ fault = refl , refl
  ... | inj₂ input with Store.lookupCancellation before token
  ... | just cancelled = refl , refl
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = refl , refl
  ... | just _ | nothing = refl , refl
  ... | nothing | just _ = refl , refl
  ... | nothing | nothing = freshMeaning token input before bound

  module Certified = Saved.Certified Goal meaning
  operation = Certified.operation
  cachedReplay = Saved.cachedReplay

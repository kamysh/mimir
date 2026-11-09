{-# OPTIONS --safe #-}
-- Upgrade edits operational metadata and removes retired application limits; unrelated payload and
-- comments are preserved by the TOML document editor. No fallback on malformed
-- input and no downgrade of a future format. Publication uses the existing
-- owned-temporary-file, fsync, rename protocol; no backup is produced.
module Mimir.ConfigurationUpgrade where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.StructuredValue as V
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Validation using (Fault)
import Mimir.OperationalConfiguration as O
import Mimir.PublicInput as Input

-- Only these obsolete application budgets are removed. Other settings retain
-- their values and order, including model/provider credentials.
llmKeys judgeKeys emailKeys embeddingKeys : List String
llmKeys = "timeout_seconds" ∷ "max_calls" ∷ "max_output_tokens" ∷ "max_budget_usd" ∷ []
judgeKeys = "batch_size" ∷ []
emailKeys = "timeout_seconds" ∷ "retry_seconds" ∷ "max_attempts" ∷ []
embeddingKeys = "batch_size" ∷ []

named : List String → Text → Bool
named [] key = false
named (name ∷ rest) key = does (key ≟Text toList name) ∨ named rest key

retired : Text → Bool
retired = named llmKeys

-- The checker and upgrader share the same retired key sets. Values, including
-- an old wrong type, never become a replacement policy or enter the message.
checkOptional : String → List String → Maybe V.Value → Text ⊎ ⊤
checkOptional section keys nothing = inj₂ tt
checkOptional section [] (just raw) = inj₂ tt
checkOptional section (name ∷ names) (just raw) with Input.view raw (toList name)
... | nothing = checkOptional section names (just raw)
... | just value = inj₁ (toList section ++ toList "." ++ toList name ++
  toList " is obsolete: run `mimir config upgrade` to remove retired application limits, then `mimir config check`. Other settings and comments are preserved")

Fields = List (Text × V.Value)

module Filter (isRetired : Text → Bool) where
  removeRetired : Fields → Fields
  removeRetired [] = []
  removeRetired ((key , value) ∷ rest) with isRetired key
  ... | true = removeRetired rest
  ... | false = (key , value) ∷ removeRetired rest

  -- A receipt accounts for every input setting; only a retired key can disappear.
  data Migration : Fields → Fields → Set where
    empty : Migration [] []
    removed : ∀ key value before after → isRetired key ≡ true → Migration before after →
      Migration ((key , value) ∷ before) after
    preserved : ∀ key value before after → isRetired key ≡ false → Migration before after →
      Migration ((key , value) ∷ before) ((key , value) ∷ after)

  migrationComplete : ∀ fields → Migration fields (removeRetired fields)
  migrationComplete [] = empty
  migrationComplete ((key , value) ∷ rest) with isRetired key in eq
  ... | true = removed key value rest (removeRetired rest) eq (migrationComplete rest)
  ... | false = preserved key value rest (removeRetired rest) eq (migrationComplete rest)

  migrationIdempotent : ∀ fields → removeRetired (removeRetired fields) ≡ removeRetired fields
  migrationIdempotent [] = refl
  migrationIdempotent ((key , value) ∷ rest) with isRetired key in eq
  ... | true = migrationIdempotent rest
  ... | false rewrite eq = cong ((key , value) ∷_) (migrationIdempotent rest)

module Llm = Filter retired
open Llm public

loggingRetired : Text → Bool
loggingRetired name = does (name ≟Text toList "max_file_bytes") ∨ does (name ≟Text toList "retained_files")

module Logging = Filter loggingRetired

judgeRetired : Text → Bool
judgeRetired = named judgeKeys

module Judge = Filter judgeRetired

emailRetired : Text → Bool
emailRetired = named emailKeys

module Email = Filter emailRetired

module Embeddings = Filter (named embeddingKeys)

upgradeEmbeddings : Maybe Fields → Maybe Fields
upgradeEmbeddings nothing = nothing
upgradeEmbeddings (just fields) = just (Embeddings.removeRetired fields)

upgradeEmail : Maybe Fields → Maybe Fields
upgradeEmail nothing = nothing
upgradeEmail (just fields) = just (Email.removeRetired fields)

upgradeJudge : Maybe Fields → Maybe Fields
upgradeJudge nothing = nothing
upgradeJudge (just fields) = just (Judge.removeRetired fields)

upgradeLlm : Maybe Fields → Maybe Fields
upgradeLlm nothing = nothing
upgradeLlm (just fields) = just (removeRetired fields)

module Document (Payload : Set) where
  record Before : Set where
    constructor before
    field version : Maybe ℕ; logging : Fields; llm judge email embeddings : Maybe Fields; payload : Payload
  record After : Set where
    constructor after
    field operations : O.Admitted; logging : Fields; llm judge email embeddings : Maybe Fields; payload : Payload
  data Failure : Set where futureVersion : Failure; invalid : Fault → Failure

  validate : Before → Failure ⊎ After
  validate old with O.decodeLogging (V.object (Logging.removeRetired (Before.logging old)))
  ... | inj₁ fault = inj₁ (invalid fault)
  ... | inj₂ logs with O.admit (O.settings O.formatVersion logs)
  ...   | inj₁ fault = inj₁ (invalid fault)
  ...   | inj₂ accepted = inj₂ (after accepted (Logging.removeRetired (Before.logging old))
    (upgradeLlm (Before.llm old)) (upgradeJudge (Before.judge old))
    (upgradeEmail (Before.email old)) (upgradeEmbeddings (Before.embeddings old)) (Before.payload old))

  upgrade : Before → Failure ⊎ After
  upgrade old with Before.version old
  ... | nothing = validate old
  ... | just version with version ≟ O.formatVersion
  ...   | yes _ = validate old
  ...   | no _ = inj₁ futureVersion

  payloadPreserved : ∀ old new → validate old ≡ inj₂ new → After.payload new ≡ Before.payload old
  payloadPreserved old new proof with O.decodeLogging (V.object (Logging.removeRetired (Before.logging old)))
  ... | inj₁ fault with proof
  ...   | ()
  payloadPreserved old new proof | inj₂ logs with O.admit (O.settings O.formatVersion logs)
  ... | inj₁ fault with proof
  ...   | ()
  payloadPreserved old .(after accepted (Logging.removeRetired (Before.logging old))
    (upgradeLlm (Before.llm old)) (upgradeJudge (Before.judge old))
    (upgradeEmail (Before.email old)) (upgradeEmbeddings (Before.embeddings old)) (Before.payload old)) refl | inj₂ logs | inj₂ accepted = refl

  -- Startup requires the admitted value, so the new package cannot execute
  -- application I/O using absent or incompatible operational settings.
  data Started : After → Set where start : ∀ ready → Started ready
  startedCompatible : ∀ ready → Started ready →
    O.Settings.version (O.Admitted.value (After.operations ready)) ≡ O.formatVersion
  startedCompatible ready _ = O.acceptedVersion (After.operations ready)

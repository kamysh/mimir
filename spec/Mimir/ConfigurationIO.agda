{-# OPTIONS --safe #-}
-- Configuration publication is an atomic external operation. A failure leaves
-- the target unchanged and confirms cleanup of private files and handles.
-- The specification does not implement temporary-file or OS write algorithms.
module Mimir.ConfigurationIO where

open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.Recovery as Recovery

data Platform : Set where unix other : Platform
data Failure : Set where
  alreadyExists directoryFailure permissionFailure createFailure : Failure
  missingFile unreadable invalidTOML : Failure

record Settings : Set where
  constructor settings
  field platform : Platform; hasParent : Bool

data Effect : Set where
  createExclusive0600 createExclusive readUTF8 decodeTOML : Effect

data Input : Set where
  begin exists absent ok error : Input

data Result : Set where success : Result; failed : Failure → Result

-- Exclusive publication installs the complete content without replacing an
-- existing target. Rejection includes rollback/cleanup, not a partial file.
data Publication {Content : Set} (content : Content) : Maybe Content → Result → Maybe Content → Set where
  installed : Publication content nothing success (just content)
  refused : ∀ before failure → Publication content before (failed failure) before

createEffect : Platform → Effect
createEffect unix = createExclusive0600
createEffect other = createExclusive

resultOf : Input → Result
resultOf ok = success
resultOf exists = failed alreadyExists
resultOf _ = failed createFailure

module Certified (Content : Set) (content : Content) where
  Successful : Result → Set
  Successful success = ⊤
  Successful (failed _) = ⊥

  Atomic : Maybe Content → ⊤ → Result → Maybe Content → Set
  Atomic before tt result after = Publication content before result after

  module R = Recovery (Maybe Content) ⊤ Result (λ _ → ⊤) (λ _ → Result)
    Atomic (λ before after → after ≡ before) (λ _ _ → Maybe Content)
    (λ _ _ after → after) (λ _ after → after) Successful (λ _ → ⊤)

  successPublishesComplete : ∀ before reply after → Atomic before tt reply after →
    Successful reply → after ≡ just content
  successPublishesComplete .nothing .success .(just content) installed confirmed = refl
  successPublishesComplete before .(failed failure) .before (refused .before failure) ()

  failureLeavesUnchanged : ∀ before reply after → Atomic before tt reply after →
    ¬ Successful reply → after ≡ before
  failureLeavesUnchanged .nothing .success .(just content) installed impossible = ⊥-elim (impossible tt)
  failureLeavesUnchanged before .(failed failure) .before (refused .before failure) _ = refl

  call : R.FinalCall ⊤
  call = record
    { effect = λ _ → tt
    ; answer = λ _ result → result
    ; expected = λ _ _ _ → just content
    ; success = λ _ before reply after receipt confirmed _ →
        successPublishesComplete before reply after receipt confirmed
    ; failureUnchanged = λ _ → failureLeavesUnchanged
    ; crashUnchanged = λ _ _ unchanged → unchanged
    }
  module Proof = R.FinalPublication call
  recovery : R.Recoverable ⊤
  recovery = Proof.finalPublication

renderFailure : Failure → String
renderFailure alreadyExists = "Configuration already exists. Open the existing file; do not overwrite it."
renderFailure directoryFailure = "Cannot prepare the configuration directory. Correct the directory problem and retry."
renderFailure permissionFailure = "Cannot establish private configuration permissions. Correct access and retry."
renderFailure createFailure = "Configuration publication failed; the target is unchanged and private files are cleaned up. Correct the filesystem problem and retry."
renderFailure missingFile = "No configuration file found. Run mimir init."
renderFailure unreadable = "Cannot read the configuration. Check its path and access permissions, then retry."
renderFailure invalidTOML = "Invalid configuration syntax. Correct the TOML and run mimir config check."

renderReadFailure : String → Failure → String
renderReadFailure contents failure = renderFailure failure

diagnosticIndependentOfSecrets : ∀ first second failure →
  renderReadFailure first failure ≡ renderReadFailure second failure
diagnosticIndependentOfSecrets first second failure = refl

-- Updating an existing configuration has the same transaction boundary as
-- creation. The complete replacement is prepared first. Failure retains the
-- original file and releases private resources; retry starts with a fresh read.
module Replacement (Content : Set) (content : Content) where
  data Receipt : Maybe Content → Result → Maybe Content → Set where
    replaced : ∀ original → Receipt (just original) success (just content)
    refused : ∀ before failure → Receipt before (failed failure) before

  module R = Recovery (Maybe Content) ⊤ Result (λ _ → ⊤) (λ _ → Result)
    (λ before _ result after → Receipt before result after)
    (λ before after → after ≡ before) (λ _ _ → Maybe Content)
    (λ _ _ after → after) (λ _ after → after) (Certified.Successful Content content) (λ _ → ⊤)

  complete : ∀ before result after → Receipt before result after →
    Certified.Successful Content content result → after ≡ just content
  complete .(just original) .success .(just content) (replaced original) _ = refl
  complete before .(failed failure) .before (refused .before failure) ()

  unchanged : ∀ before result after → Receipt before result after →
    ¬ Certified.Successful Content content result → after ≡ before
  unchanged .(just original) .success .(just content) (replaced original) impossible = ⊥-elim (impossible tt)
  unchanged before .(failed failure) .before (refused .before failure) _ = refl

  call : R.FinalCall ⊤
  call = record
    { effect = λ _ → tt ; answer = λ _ result → result
    ; expected = λ _ _ _ → just content
    ; success = λ _ before reply after receipt confirmed _ → complete before reply after receipt confirmed
    ; failureUnchanged = λ _ → unchanged
    ; crashUnchanged = λ _ _ unchanged → unchanged
    }
  module Proof = R.FinalPublication call
  recovery : R.Recoverable ⊤
  recovery = Proof.finalPublication

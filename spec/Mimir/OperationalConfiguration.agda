{-# OPTIONS --safe #-}
-- Configuration format compatibility is independent of the package release.
-- Every file-based startup validates these settings before database/model I/O.
module Mimir.OperationalConfiguration where

open import Data.Char using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≤_; _≤?_) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceSchema using (NamedText; checkNamed)
open import Mimir.Validation
open import Mimir.RecordDecoding using (_>>=_; mapResult)
open import Mimir.PublicInput using (required; defaulted; unsigned)
import Mimir.StructuredValue as V

formatVersion : ℕ
formatVersion = 1

record Logging : Set where
  constructor logging
  field directory : Text; maxFileBytes retainedFiles : ℕ

record Settings : Set where
  constructor settings
  field version : ℕ; logs : Logging

Absolute : Text → Set
Absolute path = Σ[ rest ∈ Text ] path ≡ '/' ∷ rest

absolute? : ∀ path → Dec (Absolute path)
absolute? [] = no (λ { (rest , ()) })
absolute? (first ∷ rest) with first ≟ '/'
... | yes refl = yes (rest , refl)
... | no different = no (λ { (tail , refl) → different refl })

LoggingValid : Logging → Set
LoggingValid l = NamedText 4096 (Logging.directory l) ×
  (Absolute (Logging.directory l) ×
  ((4096 ≤ Logging.maxFileBytes l × Logging.maxFileBytes l ≤ 16777216) ×
   (1 ≤ Logging.retainedFiles l × Logging.retainedFiles l ≤ 16)))

Valid : Settings → Set
Valid s = Settings.version s ≡ formatVersion × LoggingValid (Settings.logs s)

validateLogging : (l : Logging) → Checked (LoggingValid l)
validateLogging l = combine
  (at (key "directory") (checkNamed 4096 (Logging.directory l)))
  (combine (at (key "directory") (check
    (fault [] malformedInput "logging.directory must be an absolute path")
    (absolute? (Logging.directory l))))
  (combine
    (combine (check (fault [] invalidNumber "max_file_bytes must be at least 4096") (4096 ≤? Logging.maxFileBytes l))
      (check (fault [] invalidNumber "max_file_bytes must not exceed 16777216") (Logging.maxFileBytes l ≤? 16777216)))
    (combine (check (fault [] invalidNumber "retained_files must be at least 1") (1 ≤? Logging.retainedFiles l))
      (check (fault [] invalidNumber "retained_files must not exceed 16") (Logging.retainedFiles l ≤? 16)))))

validate : (s : Settings) → Checked (Valid s)
validate s = combine
  (at (key "config_version") (check
    (fault [] unsupportedCombination "configuration format is unsupported; run mimir config check")
    (Settings.version s ≟ℕ formatVersion)))
  (at (key "logging") (validateLogging (Settings.logs s)))

record Admitted : Set where
  constructor admitted
  field value : Settings; valid : Valid value

admit : Settings → Fault ⊎ Admitted
admit s = mapResult (admitted s) (result (validate s))

decodeLogging : V.Value → Fault ⊎ Logging
decodeLogging raw = V.asObject raw >>= λ entries → fields (V.Object.normalize entries)
  where
  fields : V.Object.View → Fault ⊎ Logging
  fields view = required "directory" V.asString view >>= λ directory →
    defaulted "max_file_bytes" 1048576 (unsigned 16777216) view >>= λ bytes →
    defaulted "retained_files" 4 (unsigned 16) view >>= λ retained →
    inj₂ (logging directory bytes retained)

decode : V.Value → Fault ⊎ Admitted
decode raw = V.asObject raw >>= λ entries → fields (V.Object.normalize entries)
  where
  fields : V.Object.View → Fault ⊎ Admitted
  fields view = required "config_version" (unsigned 4294967295) view >>= λ version →
    required "logging" decodeLogging view >>= λ logs → admit (settings version logs)

-- The proof accompanies every accepted configuration; no caller can treat
-- a future version, missing directory or unbounded retention as compatible.
acceptedVersion : ∀ c → Settings.version (Admitted.value c) ≡ formatVersion
acceptedVersion c = proj₁ (Admitted.valid c)

acceptedDirectory : ∀ c → Absolute (Logging.directory (Settings.logs (Admitted.value c)))
acceptedDirectory c = proj₁ (proj₂ (proj₂ (Admitted.valid c)))

acceptedFileBounds : ∀ c → 4096 ≤ Logging.maxFileBytes (Settings.logs (Admitted.value c)) ×
  Logging.maxFileBytes (Settings.logs (Admitted.value c)) ≤ 16777216
acceptedFileBounds c = proj₁ (proj₂ (proj₂ (proj₂ (Admitted.valid c))))

acceptedRetentionBounds : ∀ c → 1 ≤ Logging.retainedFiles (Settings.logs (Admitted.value c)) ×
  Logging.retainedFiles (Settings.logs (Admitted.value c)) ≤ 16
acceptedRetentionBounds c = proj₂ (proj₂ (proj₂ (proj₂ (Admitted.valid c))))

validConfigurationNotRejected : ∀ s → Valid s → reported (validate s) ≡ []
validConfigurationNotRejected s = noFalseRejection (validate s)

{-# OPTIONS --safe #-}
-- Configuration format compatibility is independent of the package release.
-- Every file-based startup validates these settings before database/model I/O.
module Mimir.OperationalConfiguration where

open import Data.Char using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Maybe using (just; nothing)
open import Data.String using (toList)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceSchema using (NamedText; checkNamed)
open import Mimir.Validation
open import Mimir.RecordDecoding using (_>>=_; mapResult)
open import Mimir.PublicInput using (required; unsigned)
import Mimir.StructuredValue as V

formatVersion : ℕ
formatVersion = 1

record Logging : Set where
  constructor logging
  field directory : Text

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
LoggingValid l = NamedText (Logging.directory l) ×
  Absolute (Logging.directory l)

Valid : Settings → Set
Valid s = Settings.version s ≡ formatVersion × LoggingValid (Settings.logs s)

validateLogging : (l : Logging) → Checked (LoggingValid l)
validateLogging l = combine
  (at (key "directory") (checkNamed (Logging.directory l)))
  (at (key "directory") (check
    (fault [] malformedInput "logging.directory must be an absolute path")
    (absolute? (Logging.directory l))))

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
  fields view with view (toList "max_file_bytes") | view (toList "retained_files")
  ... | just _ | _ = inj₁ (fault (fieldKey (toList "max_file_bytes") ∷ []) unsupportedCombination
    "Remove logging.max_file_bytes: complete log entries are appended without a file-size ceiling.")
  ... | nothing | just _ = inj₁ (fault (fieldKey (toList "retained_files") ∷ []) unsupportedCombination
    "Remove logging.retained_files: Mimir no longer rotates or deletes log files.")
  ... | nothing | nothing = required "directory" V.asString view >>= λ directory → inj₂ (logging directory)

decode : V.Value → Fault ⊎ Admitted
decode raw = V.asObject raw >>= λ entries → fields (V.Object.normalize entries)
  where
  fields : V.Object.View → Fault ⊎ Admitted
  fields view = required "config_version" (unsigned 4294967295) view >>= λ version →
    required "logging" decodeLogging view >>= λ logs → admit (settings version logs)

-- The proof accompanies every accepted configuration; no caller can treat
-- a future version or missing directory as compatible. No retention or size
-- policy is invented by accepting a logging directory.
acceptedVersion : ∀ c → Settings.version (Admitted.value c) ≡ formatVersion
acceptedVersion c = proj₁ (Admitted.valid c)

acceptedDirectory : ∀ c → Absolute (Logging.directory (Settings.logs (Admitted.value c)))
acceptedDirectory c = proj₂ (proj₂ (Admitted.valid c))

validConfigurationNotRejected : ∀ s → Valid s → reported (validate s) ≡ []
validConfigurationNotRejected s = noFalseRejection (validate s)

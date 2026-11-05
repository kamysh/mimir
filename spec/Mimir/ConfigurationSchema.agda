{-# OPTIONS --safe #-}
-- Application TOML schema after the standard parser. Core configuration keeps
-- judge-owned tables opaque until the judge's stricter validators consume them.
-- Their presence cannot make graph-only startup require a judge backend.
module Mimir.ConfigurationSchema where

open import Data.List using (List; []; _∷_; map; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList; fromList)
open import Relation.Nullary using (yes; no)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault)
open import Mimir.RecordDecoding using (_>>=_; mapResult)
open import Mimir.PublicInput using (bad; enum; unsigned; required; optional; defaulted)
import Mimir.StructuredValue as V
import Mimir.OperationalConfiguration as Operations
import Mimir.ConfigurationValues as C
import Mimir.ConfigurationInput as Input
import Mimir.SourceReview as TextEquality

record Config : Set where
  constructor config
  field operations : Operations.Admitted; core : C.Config; llm judge email : Maybe V.Value

sslMode : V.Value → Fault ⊎ C.Mode
sslMode = enum (("disable" , C.disable) ∷ ("prefer" , C.prefer) ∷ ("require" , C.require) ∷
  ("verify-ca" , C.verifyCa) ∷ ("verify-full" , C.verifyFull) ∷ [])

backend : V.Value → Fault ⊎ C.Backend
backend = enum (("local" , C.local) ∷ ("voyage" , C.voyage) ∷ ("openai" , C.openai) ∷ [])

table : V.Value → Fault ⊎ V.Value
table raw@(V.object fields) = inj₂ raw
table _ = bad "expected a TOML table"

database : V.Value → Fault ⊎ C.Database
database raw = V.asObject raw >>= λ entries → fields (V.Object.normalize entries)
  where
  fields : V.Object.View → Fault ⊎ C.Database
  fields values = required "host" V.asString values >>= λ host → required "port" (unsigned 65535) values >>= λ port →
    required "dbname" V.asString values >>= λ dbname → required "user" V.asString values >>= λ user →
    optional "password" V.asString values >>= λ password → optional "pgpassfile" V.asString values >>= λ passfile →
    defaulted "ssl_mode" C.prefer sslMode values >>= λ mode → optional "ssl_root_cert" V.asString values >>= λ root →
    optional "ssl_client_cert" V.asString values >>= λ cert → optional "ssl_client_key" V.asString values >>= λ key →
    inj₂ (C.database host dbname user port password passfile mode root cert key)

module Decode (sizeMaximum : ℕ) where
  embeddings : V.Value → Fault ⊎ C.Embeddings
  embeddings raw = V.asObject raw >>= λ entries → fields (V.Object.normalize entries)
    where
    fields : V.Object.View → Fault ⊎ C.Embeddings
    fields values = required "backend" backend values >>= λ backend → defaulted "model" [] V.asString values >>= λ model →
      optional "api_key" V.asString values >>= λ key → defaulted "batch_size" 0 (unsigned sizeMaximum) values >>= λ batch →
      optional "cache_dir" V.asString values >>= λ cache → inj₂ (C.embeddings backend model key batch cache)

  decode : V.Value → Fault ⊎ Config
  decode raw = Operations.decode raw >>= λ operations →
    V.asObject raw >>= λ entries → fields operations (V.Object.normalize entries)
    where
    fields : Operations.Admitted → V.Object.View → Fault ⊎ Config
    fields operations values = required "database" database values >>= λ db → optional "embeddings" embeddings values >>= λ embed →
      optional "llm" table values >>= λ llm → optional "judge" table values >>= λ judge → optional "email" table values >>= λ email →
      inj₂ (config operations (C.config db embed) llm judge email)

-- CLI parsing splits only at the first '='; values can contain more equals
-- signs, whitespace or an empty string. Keys are not trimmed or case-folded.
splitPair : Text → Text → Maybe (Text × Text)
splitPair key [] = nothing
splitPair key (c ∷ rest) with TextEquality._≟Text_ (c ∷ []) (toList "=")
... | no _ = splitPair (c ∷ key) rest
... | yes _ with key
...   | [] = nothing
...   | _ ∷ _ = just (reverse key , rest)

pair : Text → Fault ⊎ (String × Text)
pair raw with splitPair [] raw
... | nothing = bad "expected KEY=VALUE"
... | just (key , value) = inj₂ (fromList key , value)

pairs : List Text → Fault ⊎ List (String × Text)
pairs [] = inj₂ []
pairs (raw ∷ rest) = pair raw >>= λ first → mapResult (first ∷_) (pairs rest)

{-# OPTIONS --safe #-}
-- A saved original preparation fixes the file, PostgreSQL identities and old
-- document view. Provider work cannot replace that capture on a later retry.
module Mimir.DocumentLoadingRecovery where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map; length; zip; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.DocumentReplacementRecovery as Replacement
import Mimir.DocumentQuery as Query
import Mimir.Markdown as Markdown
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Library
import Mimir.PublicInput as Input
import Mimir.RecordDecoding as Record
import Mimir.StructuredValue as Wire
import Mimir.JsonObjects as Objects
import Mimir.Validation as Validation
import Mimir.RetrievalRanking as Ranking
import Mimir.Binary64 as Binary
open import Mimir.RecordDecoding using (_>>=_)

record Draft : Set where
  constructor draft
  field requestedPath path source : Text; project : Maybe Text

-- These are temporary section links, not persistent identities. All saved
-- chunk and parent identities below are replaced by actual PostgreSQL replies.
outline : Draft → List Documents.Chunk
outline input = Parser.parse (Draft.source input)
  where module Parser = Markdown.Parse (Draft.path input) (Draft.project input) (λ ordinal → ordinal)

record Allocation : Set where
  constructor allocated
  field owner : ℕ; reservedAt : ℤ; declaredDimensions : Maybe ℕ; chunkIDs : List ℕ

record Prepared : Set where
  constructor prepared
  field owner : ℕ; reservedAt : ℤ; declaredDimensions : Maybe ℕ
        project : Maybe Text; path source : Text
        chunks previous : List Documents.Chunk

shapeFault : Validation.Fault
shapeFault = Validation.fault [] Validation.malformedInput
  "The original complete document preparation could not retain its allocated chunk identities and parent links. Read its saved preparation and outcome; no replacement was published."

lookupIdentity : ℕ → List (ℕ × ℕ) → Maybe ℕ
lookupIdentity identity [] = nothing
lookupIdentity identity ((key , assigned) ∷ rest) with identity ≟ key
... | yes _ = just assigned
... | no _ = lookupIdentity identity rest

remapParent : List (ℕ × ℕ) → Maybe ℕ → Validation.Fault ⊎ Maybe ℕ
remapParent mapping nothing = inj₂ nothing
remapParent mapping (just temporary) with lookupIdentity temporary mapping
... | nothing = inj₁ shapeFault
... | just assigned = inj₂ (just assigned)

remap : List (ℕ × ℕ) → List Documents.Chunk → Validation.Fault ⊎ List Documents.Chunk
remap mapping [] = inj₂ []
remap mapping (chunk ∷ rest) with lookupIdentity (Documents.Chunk.identity chunk) mapping
... | nothing = inj₁ shapeFault
... | just assigned = remapParent mapping (Documents.Chunk.parent chunk) >>= λ parent →
  remap mapping rest >>= λ later → inj₂ (record chunk { identity = assigned; parent = parent } ∷ later)

allocatedChunks : Draft → Allocation → Validation.Fault ⊎ List Documents.Chunk
allocatedChunks input metadata with length (outline input) ≟ length (Allocation.chunkIDs metadata)
... | no _ = inj₁ shapeFault
... | yes _ = remap (zip (map Documents.Chunk.identity (outline input)) (Allocation.chunkIDs metadata)) (outline input)

documentRows : Text → Store.World → List Documents.Chunk
documentRows path before = Ranking.sort
  (λ first second → does (Documents.Chunk.identity first Data.Nat.≤? Documents.Chunk.identity second))
  (filterᵇ (λ chunk → does (Documents.Chunk.document chunk ≟Text path)) (Store.World.chunks before))

capture : Draft → Allocation → Store.World → Validation.Fault ⊎ Prepared
capture input metadata snapshot = allocatedChunks input metadata >>= λ chunks → inj₂
  (prepared (Allocation.owner metadata) (Allocation.reservedAt metadata) (Allocation.declaredDimensions metadata)
    (Draft.project input) (Draft.path input) (Draft.source input) chunks (documentRows (Draft.path input) snapshot))

module Codec (library : Library.Contract) (format : Encoding.Formatting)
  (utcTimestamp : Text → Validation.Fault ⊎ ℤ) where
  module Encode = Encoding.Encode format
  module Scalar = Input.Numbers library

  optionalField : ∀ {A : Set} → String → (A → Wire.Value) → Maybe A → List (String × Wire.Value)
  optionalField name encode nothing = []
  optionalField name encode (just value) = (name , encode value) ∷ []

  chunk : Documents.Chunk → Wire.Value
  chunk value = Encoding.object
    (("id" , Encode.uuid (Documents.Chunk.identity value)) ∷
     ("document_path" , Wire.string (Documents.Chunk.document value)) ∷
     ("section_path" , Wire.array (map Wire.string (Documents.Chunk.section value))) ∷
     ("content" , Wire.string (Documents.Chunk.content value)) ∷
     (optionalField "parent_id" Encode.uuid (Documents.Chunk.parent value)
      Data.List.++ optionalField "project" Wire.string (Documents.Chunk.project value)))

  encode : Prepared → Wire.Value
  encode value = Encoding.object
    (("owner_token" , Encode.uuid (Prepared.owner value)) ∷
     ("reserved_at" , Encode.timestamp (Prepared.reservedAt value)) ∷
     ("declared_dimensions" , Encoding.optional Wire.unsigned (Prepared.declaredDimensions value)) ∷
     ("project" , Encoding.optional Wire.string (Prepared.project value)) ∷
     ("path" , Wire.string (Prepared.path value)) ∷
     ("source" , Wire.string (Prepared.source value)) ∷
     ("chunks" , Wire.array (map chunk (Prepared.chunks value))) ∷
     ("previous" , Wire.array (map chunk (Prepared.previous value))) ∷ [])

  readChunk : Wire.Value → Validation.Fault ⊎ Documents.Chunk
  readChunk = Record.readRecord Objects.forbid Objects.rejectKnownRepeated
    (map toList ("id" ∷ "document_path" ∷ "section_path" ∷ "content" ∷ "parent_id" ∷ "project" ∷ [])) λ fields →
      Input.required "id" Scalar.uuid fields >>= λ identity →
      Input.required "document_path" Wire.asString fields >>= λ path →
      Input.required "section_path" (Record.readArray Wire.asString) fields >>= λ section →
      Input.required "content" Wire.asString fields >>= λ content →
      Input.optional "parent_id" Scalar.uuid fields >>= λ parent →
      Input.optional "project" Wire.asString fields >>= λ project →
      inj₂ (Documents.mkChunk identity path section content parent project)

  decode : Wire.Value → Validation.Fault ⊎ Prepared
  decode = Record.readRecord Objects.forbid Objects.rejectKnownRepeated
    (map toList ("owner_token" ∷ "reserved_at" ∷ "declared_dimensions" ∷ "project" ∷ "path" ∷ "source" ∷ "chunks" ∷ "previous" ∷ [])) λ fields →
      Input.required "owner_token" Scalar.uuid fields >>= λ owner →
      Input.required "reserved_at" (λ raw → Wire.asString raw >>= utcTimestamp) fields >>= λ reserved →
      -- The existing installed target's usize representation, not a quota.
      Input.optional "declared_dimensions" (Input.unsigned (Binary.powerMinusOne 64)) fields >>= λ dimension →
      Input.optional "project" Wire.asString fields >>= λ project →
      Input.required "path" Wire.asString fields >>= λ path →
      Input.required "source" Wire.asString fields >>= λ source →
      Input.required "chunks" (Record.readArray readChunk) fields >>= λ chunks →
      Input.required "previous" (Record.readArray readChunk) fields >>= λ previous →
      inj₂ (prepared owner reserved dimension project path source chunks previous)

  -- An actual successful standard serialization/deserialization receipt for
  -- these concrete fields. No universal UUID/date formatter law is assumed.
  record Candidate (value : Prepared) : Set where
    field decoded : decode (encode value) ≡ inj₂ value

{-# OPTIONS --safe #-}
-- The nine embedded application migrations. This is the concrete DDL/data
-- contract supplied to MigrationDriver.executeOriginalSQL; PostgreSQL executes
-- these operations inside the driver's transaction, before both ledger writes.
-- SQL expression arithmetic, collation and NULL semantics are database
-- dependency contracts, not an invented SQL interpreter.
module Mimir.MigrationSchema where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (String; toList)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Migrations public
  using (Migration; initial; searchPath; evidenceEdges; betaBeliefs)
  renaming (name to migrationName; beliefEmbeddings to embeddingTable; learningLedger to learning;
    reviewCandidates to candidates; assessments to assessment; itemOwners to owners;
    predecessor to requires; manifest to ordered)

data Type : Set where uuid text bigint timestamp jsonb double boolean vector : Type
data Default : Set where noDefault now zero falseDefault : Default
record Column : Set where
  constructor column
  field name : String; type : Type; nullable : Bool; defaultValue : Default

required : String → Type → Column
required name type = column name type false noDefault
optional : String → Type → Column
optional name type = column name type true noDefault

data Expr : Set where
  columnValue : String → Expr
  number : String → Expr -- exact SQL decimal literal, interpreted by PostgreSQL
  literal : String → Expr
  add subtract multiply absolute charLength : List Expr → Expr
  less lessEqual equal between oneOf : List Expr → Expr

data DeleteAction : Set where restrict cascade : DeleteAction
record ForeignKey : Set where
  constructor references
  field columns : List String; target : String; targetColumns : List String; onDelete : DeleteAction

record Table : Set where
  constructor table
  field
    name : String
    columns : List Column
    primary : List String
    unique : List (List String)
    foreignKeys : List ForeignKey
    checks : List Expr

record Index : Set where
  constructor index
  field name tableName : String; columns : List String; predicate : Maybe Expr

experienceFK : ForeignKey
experienceFK = references ("experience_id" ∷ []) "mimir_experiences" ("id" ∷ []) cascade

chunkVectors beliefVectors : Table
chunkVectors = table "public.chunk_embeddings"
  (required "chunk_id" uuid ∷ optional "embedding" vector ∷ []) ("chunk_id" ∷ []) [] [] []
beliefVectors = table "public.belief_embeddings"
  (required "belief_id" uuid ∷ optional "embedding" vector ∷ []) ("belief_id" ∷ []) [] [] []

experiences : Table
experiences = table "mimir_experiences"
  (required "id" uuid ∷ required "project" text ∷ required "revision" bigint ∷
   column "review_revision" bigint false zero ∷ column "reviewed_revision" bigint false zero ∷
   column "updated_at" timestamp false now ∷ []) ("id" ∷ []) [] []
  (less (number "0" ∷ columnValue "revision" ∷ []) ∷ [])

experienceVersions : Table
experienceVersions = table "mimir_experience_versions"
  (required "experience_id" uuid ∷ required "revision" bigint ∷ required "payload" jsonb ∷
   column "created_at" timestamp false now ∷ []) ("experience_id" ∷ "revision" ∷ []) []
  (experienceFK ∷ []) []

reviewVersions : Table
reviewVersions = table "mimir_review_versions"
  (required "experience_id" uuid ∷ required "revision" bigint ∷ required "experience_revision" bigint ∷
   required "payload" jsonb ∷ column "created_at" timestamp false now ∷ [])
  ("experience_id" ∷ "revision" ∷ []) []
  (experienceFK ∷ references ("experience_id" ∷ "experience_revision" ∷ [])
    "mimir_experience_versions" ("experience_id" ∷ "revision" ∷ []) restrict ∷ []) []

reviewCandidates : Table
reviewCandidates = table "mimir_review_candidates"
  (required "experience_id" uuid ∷ required "candidate_key" text ∷ required "kind" text ∷
   required "node_id" uuid ∷ required "declaration" jsonb ∷ column "retired" boolean false falseDefault ∷ [])
  ("experience_id" ∷ "candidate_key" ∷ []) (("node_id" ∷ []) ∷ []) (experienceFK ∷ [])
  (between (charLength (columnValue "candidate_key" ∷ []) ∷ number "1" ∷ number "128" ∷ []) ∷
   oneOf (columnValue "kind" ∷ literal "belief" ∷ literal "pattern" ∷ []) ∷ [])

unitInterval : String → Expr
unitInterval name = between (columnValue name ∷ number "0" ∷ number "1" ∷ [])

assessments : Table
assessments = table "mimir_assessment_contributions"
  (required "experience_id" uuid ∷ required "review_revision" bigint ∷ required "belief_id" uuid ∷
   required "scope" text ∷ required "rubric" text ∷ required "positive" double ∷ required "negative" double ∷
   required "benefit" double ∷ required "benefit_weight" double ∷ required "payload" jsonb ∷ [])
  ("experience_id" ∷ "review_revision" ∷ "belief_id" ∷ "scope" ∷ "rubric" ∷ []) []
  (references ("experience_id" ∷ "review_revision" ∷ []) "mimir_review_versions"
    ("experience_id" ∷ "revision" ∷ []) cascade ∷ [])
  (unitInterval "positive" ∷ unitInterval "negative" ∷
   between (columnValue "benefit" ∷ number "-1" ∷ number "1" ∷ []) ∷ unitInterval "benefit_weight" ∷
   lessEqual (add (columnValue "positive" ∷ columnValue "negative" ∷ []) ∷ number "1.000000000000001" ∷ []) ∷
   lessEqual (absolute (columnValue "benefit" ∷ []) ∷ columnValue "benefit_weight" ∷ []) ∷ [])

itemOwners : Table
itemOwners = table "mimir_learning_item_owners"
  (required "item_id" uuid ∷ required "experience_id" uuid ∷ required "source_ref" text ∷ required "actor" text ∷ [])
  ("item_id" ∷ []) [] (experienceFK ∷ []) []

-- Label creation catches all PostgreSQL exceptions in the existing SQL; that
-- native behavior is explicit and must not be confused with a label-exists proof.
data DDL : Set where
  ensureCurrentDatabaseGraph : DDL
  tryVertexLabel tryEdgeLabel : String → DDL
  setDatabaseSearchPath : List String → DDL
  createIfAbsent create : Table → DDL
  addNullableColumn : String → Column → DDL
  createIndex : Index → DDL
  backfillMissingAlpha0 : List (String × Expr) → DDL

kappa alpha beta : Expr
kappa = add (number "2.0" ∷ multiply (columnValue "confidence" ∷ number "198.0" ∷ []) ∷ [])
alpha = multiply (columnValue "probability" ∷ kappa ∷ [])
beta = multiply (subtract (number "1.0" ∷ columnValue "probability" ∷ []) ∷ kappa ∷ [])

body : Migration → List DDL
body initial = ensureCurrentDatabaseGraph ∷ tryVertexLabel "Belief" ∷ tryVertexLabel "Pattern" ∷
  tryVertexLabel "DocumentChunk" ∷ tryEdgeLabel "SUPPORTS" ∷ tryEdgeLabel "DEFEATS" ∷
  tryEdgeLabel "CAUSES" ∷ tryEdgeLabel "CONTRADICTS" ∷ tryEdgeLabel "CONTAINS" ∷ createIfAbsent chunkVectors ∷ []
body searchPath = setDatabaseSearchPath ("ag_catalog" ∷ "$user" ∷ "public" ∷ []) ∷ []
body embeddingTable = createIfAbsent beliefVectors ∷ []
body evidenceEdges = tryEdgeLabel "GROUNDS" ∷ []
body betaBeliefs = backfillMissingAlpha0 (("alpha0" , alpha) ∷ ("beta0" , beta) ∷
  ("alpha" , alpha) ∷ ("beta" , beta) ∷ []) ∷ []
body learning = create experiences ∷ create experienceVersions ∷ create reviewVersions ∷
  createIndex (index "mimir_pending_reviews" "mimir_experiences" ("updated_at" ∷ "id" ∷ [])
    (just (less (columnValue "reviewed_revision" ∷ columnValue "revision" ∷ [])))) ∷ []
body candidates = addNullableColumn "mimir_review_versions" (optional "request" jsonb) ∷ create reviewCandidates ∷
  createIndex (index "mimir_review_candidates_node" "mimir_review_candidates" ("node_id" ∷ []) nothing) ∷ []
body assessment = create assessments ∷
  createIndex (index "mimir_assessment_lookup" "mimir_assessment_contributions" ("belief_id" ∷ "scope" ∷ "rubric" ∷ []) nothing) ∷ []
body owners = create itemOwners ∷ []

-- Backfill guards only alpha0. Already migrated vertices are untouched even
-- if another field is absent; the specification does not silently repair data.
module Backfill (Scalar : Set) (evaluate : Expr → (String → Maybe Scalar) → Maybe Scalar) where
  Row = String → Maybe Scalar
  assignment : Row → List (String × Maybe Scalar)
  assignment row with row "alpha0"
  ... | just value = []
  ... | nothing = map (λ { (name , expression) → name , evaluate expression row })
      (("alpha0" , alpha) ∷ ("beta0" , beta) ∷ ("alpha" , alpha) ∷ ("beta" , beta) ∷ [])

  existingPriorUntouched : ∀ row value → row "alpha0" ≡ just value → assignment row ≡ []
  existingPriorUntouched row value present rewrite present = refl

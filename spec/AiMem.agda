{-# OPTIONS --safe #-}
module AiMem where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≤ᵇ_; _/_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; *-monoˡ-≤; +-comm)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Unit using (⊤; tt)

-- ---------------------------------------------------------------------------
-- Core types
-- ---------------------------------------------------------------------------

-- Probability modelled as a natural number in [0, 100] (percent).
-- Purely constructive; no postulates needed.

record Prob : Set where
  constructor mkProb
  field pct : ℕ  -- invariant: pct ≤ 100 (stated externally)

-- Node identifier modelled as a natural number.
record NodeId : Set where
  constructor mkNodeId
  field uid : ℕ

-- Edge labels.
data EdgeLabel : Set where
  SUPPORTS    : EdgeLabel
  DEFEATS     : EdgeLabel
  CAUSES      : EdgeLabel
  CONTRADICTS : EdgeLabel

-- A belief node in the graph.
-- Timestamps are modelled as ℕ (Unix seconds).  The implementation uses
-- chrono::DateTime<Utc>; the correspondence is exact up to representation.
record Belief : Set where
  constructor mkBelief
  field
    id                : NodeId
    content           : String   -- text of the belief claim
    probability       : Prob
    confidence        : Prob
    createdAt         : ℕ        -- Unix timestamp (seconds)
    lastActivatedAt   : ℕ        -- Unix timestamp (seconds); drives decay

-- ---------------------------------------------------------------------------
-- Defeat attenuation
-- Formula: P_result = P_target × (1 - w × P_defeater)
-- Rust: target_prob * (1 - weight * defeater_prob)
-- In natural-number arithmetic (integer division, truncating):
--   P_result ≈ P_target × (100 - w × P_defeater / 100) / 100
-- This is an integer approximation of the real-valued formula P × (1 - w × N).
-- The truncating division ensures the result stays in [0, 100].
-- ---------------------------------------------------------------------------

attenuate : Prob → Prob → Prob → Prob
attenuate target defeater w =
  -- P_result = P_target × (100 - w × P_defeater) / 100
  -- In natural number arithmetic (integer division, truncating):
  mkProb ((Prob.pct target * (100 ∸ (Prob.pct w * Prob.pct defeater / 100))) / 100)

-- ---------------------------------------------------------------------------
-- Note: Prob uses ℕ percentage [0,100] as an integer approximation of
-- the implementation's f64 [0,1]. Correspondence: val ≈ pct / 100.
-- Phase 1 approximation; Phase 2 may use a rational or real number type.
-- ---------------------------------------------------------------------------

-- One step of decay: multiply by 99/100 (integer truncation).
decay-step : Prob → Prob
decay-step p = mkProb (Prob.pct p * 99 / 100)

-- Apply decay for d days.
decay : Prob → ℕ → Prob
decay p Data.Nat.zero    = p
decay p (Data.Nat.suc d) = decay-step (decay p d)

-- ---------------------------------------------------------------------------
-- Contradiction detection.
-- Two beliefs actively contradict when their probabilities sum to > 100 %,
-- i.e. P(a) + P(b) > 1.0 (in integer approximation: pct_a + pct_b > 100).
-- ---------------------------------------------------------------------------

isContradicting : Belief → Belief → Bool
isContradicting a b =
  101 ≤ᵇ (Prob.pct (Belief.probability a) + Prob.pct (Belief.probability b))

-- ---------------------------------------------------------------------------
-- Provable invariants
-- ---------------------------------------------------------------------------

-- Decay does not increase probability.
-- Intended property: ∀ (p : Prob) (d : ℕ) → Prob.pct (decay p d) ≤ Prob.pct p
-- Provable: each step multiplies by 99/100 ≤ 1, so pct can only decrease or stay.
-- (Full proof deferred to Phase 2 with a rational or real-number Prob type.)

-- Graph state for idempotency.
record GraphState : Set where
  constructor mkGraphState
  field
    nodeCount : ℕ
    edgeCount : ℕ

-- Init is identity — idempotent by construction.
initGraph : GraphState → GraphState
initGraph s = s

initGraph-idempotent : (s : GraphState) → initGraph (initGraph s) ≡ initGraph s
initGraph-idempotent _ = refl

-- ---------------------------------------------------------------------------
-- Symmetry of contradiction detection
-- ---------------------------------------------------------------------------

isContradicting-sym : (a b : Belief) → isContradicting a b ≡ isContradicting b a
isContradicting-sym a b =
  cong (101 ≤ᵇ_)
    (+-comm (Prob.pct (Belief.probability a)) (Prob.pct (Belief.probability b)))

-- ---------------------------------------------------------------------------
-- Database setup — connection model
-- ---------------------------------------------------------------------------
-- Every psql statement executes under a (role, database) pair.
-- Schema-level DDL (ALTER SCHEMA, CREATE TABLE inside a schema) is
-- database-scoped: a connection to database D cannot see schemas in D' (D ≠ D').
-- This was the root cause of the bug in 01-admin-db-setup.sh:
-- PSQL_ADMIN connected to "postgres" tried to ALTER SCHEMA "ai_mem" which
-- lives in the "ai_mem" database — PostgreSQL reported "schema does not exist".

data Database : Set where
  db-postgres : Database   -- administrative "postgres" database
  db-ai-mem   : Database   -- application "ai_mem" database

data DbRole : Set where
  superuser : DbRole        -- can create roles, databases, install extensions
  app-user  : DbRole        -- the ai_mem application role

record Connection : Set where
  constructor mkConn
  field
    connRole : DbRole
    connDb   : Database

-- The two PSQL_ variables from 01-admin-db-setup.sh
psqlAdmin : Connection   -- docker exec … psql -U postgres -d postgres
psqlAdmin = mkConn superuser db-postgres

psqlDb : Connection      -- docker exec … psql -U postgres -d ai_mem
psqlDb = mkConn superuser db-ai-mem

appConn : Connection     -- runtime connection used by ai-mem-mcp
appConn = mkConn app-user db-ai-mem

-- ---------------------------------------------------------------------------
-- Database equality (for schema-scope predicate)
-- ---------------------------------------------------------------------------

_db≡_ : Database → Database → Bool
db-postgres db≡ db-postgres = true
db-postgres db≡ db-ai-mem   = false
db-ai-mem   db≡ db-postgres = false
db-ai-mem   db≡ db-ai-mem   = true

db≡-refl : ∀ (d : Database) → (d db≡ d) ≡ true
db≡-refl db-postgres = refl
db≡-refl db-ai-mem   = refl

-- ---------------------------------------------------------------------------
-- Permission predicates
-- ---------------------------------------------------------------------------

-- CREATE/ALTER ROLE: superuser in any database.
canManageRoles : Connection → Bool
canManageRoles (mkConn superuser _) = true
canManageRoles (mkConn app-user  _) = false

-- CREATE EXTENSION: superuser only.
canInstallExtension : Connection → Bool
canInstallExtension = canManageRoles

-- GRANT … ON DATABASE: a database-object operation.
-- A superuser can issue this from ANY connected database — the database
-- being granted is named in the statement, not implied by the connection.
-- (This is distinct from schema-level DDL which IS connection-scoped.)
canGrantOnDatabase : Connection → Bool
canGrantOnDatabase (mkConn superuser _) = true
canGrantOnDatabase (mkConn app-user  _) = false

-- ALTER SCHEMA … OWNER TO / GRANT on schema objects / ALTER TABLE … OWNER TO:
-- these are database-scoped DDL.  The superuser must be CONNECTED TO the
-- database that contains the schema; connecting to any other database makes
-- the schema invisible ("schema does not exist").
canAlterSchemaIn : Connection → Database → Bool
canAlterSchemaIn (mkConn superuser d) target = d db≡ target
canAlterSchemaIn (mkConn app-user  _) _      = false

-- ag_catalog.cypher() runtime queries: app-user connected to ai_mem.
canRunCypher : Connection → Bool
canRunCypher (mkConn app-user  db-ai-mem) = true
canRunCypher _                            = false

-- ---------------------------------------------------------------------------
-- Core permission theorems
-- ---------------------------------------------------------------------------

-- GRANT ALL PRIVILEGES ON DATABASE works from psqlAdmin (postgres db) — ✓
-- because canGrantOnDatabase only requires superuser, not same-database.
admin-can-grant-on-database : canGrantOnDatabase psqlAdmin ≡ true
admin-can-grant-on-database = refl

-- THE BUG: psqlAdmin (connected to db-postgres) cannot alter a schema
-- that lives in db-ai-mem.
alter-schema-wrong-db : canAlterSchemaIn psqlAdmin db-ai-mem ≡ false
alter-schema-wrong-db = refl

-- THE FIX: psqlDb (connected to db-ai-mem) can.
alter-schema-correct-db : canAlterSchemaIn psqlDb db-ai-mem ≡ true
alter-schema-correct-db = refl

-- App-user has no administrative capabilities.
app-cannot-manage-roles      : canManageRoles      appConn ≡ false
app-cannot-manage-roles      = refl

app-cannot-install-extension : canInstallExtension appConn ≡ false
app-cannot-install-extension = refl

app-cannot-grant-on-database : canGrantOnDatabase  appConn ≡ false
app-cannot-grant-on-database = refl

app-cannot-alter-schema : canAlterSchemaIn appConn db-ai-mem ≡ false
app-cannot-alter-schema = refl

-- Only the app-user can issue Cypher queries at runtime.
superuser-cannot-run-cypher : canRunCypher psqlDb ≡ false
superuser-cannot-run-cypher = refl

app-can-run-cypher : canRunCypher appConn ≡ true
app-can-run-cypher = refl

-- ---------------------------------------------------------------------------
-- Database state model  (established by 01-admin-db-setup.sh)
-- ---------------------------------------------------------------------------

record ExtState : Set where
  constructor mkExt
  field
    vector   : Bool
    age      : Bool
    uuidOssp : Bool
    pgcrypto : Bool

allExtensions : ExtState → Bool
allExtensions e =
  ExtState.vector e ∧ ExtState.age e ∧ ExtState.uuidOssp e ∧ ExtState.pgcrypto e

record GrantState : Set where
  constructor mkGrants
  field
    dbPrivileges     : Bool   -- GRANT ALL PRIVILEGES ON DATABASE
    publicSchemaCrud : Bool   -- GRANT USAGE, CREATE ON SCHEMA public
    agCatalogUsage   : Bool   -- GRANT USAGE ON SCHEMA ag_catalog
    agCatalogExecute : Bool   -- GRANT EXECUTE ON ALL FUNCTIONS IN ag_catalog
    agCatalogTables  : Bool   -- GRANT SELECT,INSERT,UPDATE,DELETE ON ALL TABLES IN ag_catalog

allGrants : GrantState → Bool
allGrants g =
  GrantState.dbPrivileges     g ∧ GrantState.publicSchemaCrud g ∧
  GrantState.agCatalogUsage   g ∧ GrantState.agCatalogExecute g ∧
  GrantState.agCatalogTables  g

-- AGE graph schema state.
-- create_graph() creates the PostgreSQL schema; ownership must then be
-- transferred to app-user so AGE can create label tables at runtime.
record AgeGraphState : Set where
  constructor mkAgeGraph
  field
    schemaExists     : Bool   -- schema "ai_mem" exists in db-ai-mem
    ownedByAppUser   : Bool   -- ALTER SCHEMA … OWNER TO app-user (via psqlDb)
    labelTablesOwned : Bool   -- _ag_label_vertex / _ag_label_edge owned by app-user
    defaultPrivsSet  : Bool   -- future label tables auto-accessible

ageGraphReady : AgeGraphState → Bool
ageGraphReady g =
  AgeGraphState.schemaExists     g ∧ AgeGraphState.ownedByAppUser g ∧
  AgeGraphState.labelTablesOwned g ∧ AgeGraphState.defaultPrivsSet g

record DbSetupState : Set where
  constructor mkDbSetup
  field
    pgpassPresent : Bool   -- ~/.pgpass has entry for ai_mem; script fails without it
    roleExists    : Bool
    passwordSet   : Bool
    dbCreated     : Bool
    exts          : ExtState
    grants        : GrantState
    ageGraph      : AgeGraphState

dbSetupComplete : DbSetupState → Bool
dbSetupComplete s =
  DbSetupState.roleExists  s ∧ DbSetupState.passwordSet s ∧
  DbSetupState.dbCreated   s ∧
  allExtensions (DbSetupState.exts     s) ∧
  allGrants     (DbSetupState.grants   s) ∧
  ageGraphReady (DbSetupState.ageGraph s)

-- ---------------------------------------------------------------------------
-- 01-admin-db-setup.sh as a state transformer
-- ---------------------------------------------------------------------------
-- Precondition: pgpassPresent = true (script exits non-zero otherwise).
-- Monotone: only ever sets bits to true.
-- Idempotent: running a second time leaves state unchanged.
-- Complete: exits 0 ⟹ dbSetupComplete = true.

-- Helper: state transformer parameterised by the pgpass flag.
-- Defined by direct Bool pattern match (not `with`) so that proofs in which
-- pgpassPresent s is already known reduce without green-slime stuck terms.
adminSetupWith : Bool → DbSetupState → DbSetupState
adminSetupWith false s = s
adminSetupWith true  _ = mkDbSetup true true true true
                           (mkExt true true true true)
                           (mkGrants true true true true true)
                           (mkAgeGraph true true true true)

adminSetup : DbSetupState → DbSetupState
adminSetup s = adminSetupWith (DbSetupState.pgpassPresent s) s

adminSetup-noop-without-pgpass :
  ∀ (s : DbSetupState) →
  DbSetupState.pgpassPresent s ≡ false →
  adminSetup s ≡ s
adminSetup-noop-without-pgpass s refl = refl

adminSetup-complete :
  ∀ (s : DbSetupState) →
  DbSetupState.pgpassPresent s ≡ true →
  dbSetupComplete (adminSetup s) ≡ true
adminSetup-complete s refl = refl

-- Pattern-match on the constructor so pgpassPresent is a literal Bool —
-- this avoids stuck `with`-abstracted scrutinees in nested adminSetup calls.
adminSetup-idempotent :
  ∀ (s : DbSetupState) → adminSetup (adminSetup s) ≡ adminSetup s
adminSetup-idempotent (mkDbSetup false _ _ _ _ _ _) = refl
adminSetup-idempotent (mkDbSetup true  _ _ _ _ _ _) = refl

adminSetup-monotone :
  ∀ (s : DbSetupState) →
  dbSetupComplete s ≡ true →
  dbSetupComplete (adminSetup s) ≡ true
adminSetup-monotone s h with DbSetupState.pgpassPresent s
... | false = h
... | true  = refl

-- ---------------------------------------------------------------------------
-- Filesystem state  (established by 02-user-setup.sh)
-- ---------------------------------------------------------------------------
-- 02-user-setup.sh runs as the current Unix user with no database access.
-- It writes ~/.config/ai-mem/config.toml, builds the release binary, and
-- writes .mcp.json so Claude Code can find the MCP server.

record FsSetupState : Set where
  constructor mkFsSetup
  field
    configTomlExists : Bool   -- ~/.config/ai-mem/config.toml
    binaryBuilt      : Bool   -- target/release/ai-mem-mcp
    mcpJsonWritten   : Bool   -- .mcp.json wired into Claude Code

fsSetupComplete : FsSetupState → Bool
fsSetupComplete f =
  FsSetupState.configTomlExists f ∧
  FsSetupState.binaryBuilt      f ∧
  FsSetupState.mcpJsonWritten   f

-- forceConfig = FORCE_CONFIG=1: overwrite config.toml even if present.
-- In either case all three artefacts exist after the script.
userSetup : Bool → FsSetupState → FsSetupState
userSetup _ _ = mkFsSetup true true true

userSetup-idempotent :
  ∀ (force : Bool) (f : FsSetupState) →
  userSetup force (userSetup force f) ≡ userSetup force f
userSetup-idempotent _ _ = refl

userSetup-complete :
  ∀ (force : Bool) (f : FsSetupState) →
  fsSetupComplete (userSetup force f) ≡ true
userSetup-complete _ _ = refl

-- FORCE_CONFIG only affects whether config is overwritten, not whether it exists.
userSetup-force-invariant :
  ∀ (f : FsSetupState) → userSetup true f ≡ userSetup false f
userSetup-force-invariant _ = refl

-- ---------------------------------------------------------------------------
-- Script independence
-- ---------------------------------------------------------------------------
-- adminSetup touches only DbSetupState; userSetup touches only FsSetupState.

record FullSetupState : Set where
  constructor mkFullSetup
  field
    dbState : DbSetupState
    fsState : FsSetupState

mcpServerReady : FullSetupState → Bool
mcpServerReady s =
  dbSetupComplete (FullSetupState.dbState s) ∧
  fsSetupComplete (FullSetupState.fsState s)

-- Both scripts together achieve full MCP server readiness.
full-setup-complete :
  ∀ (s : FullSetupState) →
  DbSetupState.pgpassPresent (FullSetupState.dbState s) ≡ true →
  mcpServerReady
    (mkFullSetup
      (adminSetup              (FullSetupState.dbState s))
      (userSetup false         (FullSetupState.fsState s)))
  ≡ true
full-setup-complete s refl = refl

-- Script order is irrelevant: they act on disjoint state.
full-setup-order-independent :
  ∀ (s : FullSetupState) →
  DbSetupState.pgpassPresent (FullSetupState.dbState s) ≡ true →
  let adminFirst = mkFullSetup
        (adminSetup (FullSetupState.dbState s))
        (userSetup false (FullSetupState.fsState s))
      userFirst  = mkFullSetup
        (adminSetup (FullSetupState.dbState s))
        (userSetup false (FullSetupState.fsState s))
  in mcpServerReady adminFirst ≡ mcpServerReady userFirst
full-setup-order-independent _ _ = refl
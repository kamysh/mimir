{-# OPTIONS --safe #-}
module Mimir.Setup where

open import Data.Bool  using (Bool; true; false; _∧_)
open import Data.Nat   using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ---------------------------------------------------------------------------
-- Graph label state — models AgeStore::ensure_labels().
-- ensure_labels() is called in AgeStore::new() on every application startup.
-- It idempotently creates vertex labels "Belief" and "Pattern" and edge
-- labels "SUPPORTS", "DEFEATS", "CAUSES", "CONTRADICTS" using DO…EXCEPTION
-- blocks (suppresses already-exists errors).
-- Consequence: vertex/edge CREATE operations succeed iff labelsCreated = true.
-- ---------------------------------------------------------------------------

record GraphState : Set where
  constructor mkGraphState
  field
    nodeCount     : ℕ
    edgeCount     : ℕ
    labelsCreated : Bool  -- true after ensure_labels() runs; required for Cypher CREATE/MATCH

-- ensure_labels: creates all AGE labels if absent; no-op if already present.
-- Modelled as setting labelsCreated = true while leaving nodeCount and edgeCount unchanged.
ensureLabels : GraphState → GraphState
ensureLabels (mkGraphState n e _) = mkGraphState n e true

-- Idempotent: running again doesn't change state.
ensureLabels-idempotent : ∀ (s : GraphState) → ensureLabels (ensureLabels s) ≡ ensureLabels s
ensureLabels-idempotent (mkGraphState n e _) = refl

-- Complete: after ensure_labels, labelsCreated = true.
ensureLabels-complete : ∀ (s : GraphState) → GraphState.labelsCreated (ensureLabels s) ≡ true
ensureLabels-complete _ = refl

-- Preserves node and edge counts (label creation adds no data nodes/edges).
ensureLabels-preserves-nodes :
  ∀ (s : GraphState) → GraphState.nodeCount (ensureLabels s) ≡ GraphState.nodeCount s
ensureLabels-preserves-nodes (mkGraphState n e _) = refl

ensureLabels-preserves-edges :
  ∀ (s : GraphState) → GraphState.edgeCount (ensureLabels s) ≡ GraphState.edgeCount s
ensureLabels-preserves-edges (mkGraphState n e _) = refl

-- ---------------------------------------------------------------------------
-- Database setup — connection model
-- ---------------------------------------------------------------------------
-- Every psql statement executes under a (role, database) pair.
-- Schema-level DDL (ALTER SCHEMA, CREATE TABLE inside a schema) is
-- database-scoped: a connection to database D cannot see schemas in D' (D ≠ D').
-- This was the root cause of the bug in 01-admin-db-setup.sh:
-- PSQL_ADMIN connected to "postgres" tried to ALTER SCHEMA "mimir" which
-- lives in the "mimir" database — PostgreSQL reported "schema does not exist".

data Database : Set where
  db-postgres : Database   -- administrative "postgres" database
  db-mimir    : Database   -- application "mimir" database

data DbRole : Set where
  superuser : DbRole        -- can create roles, databases, install extensions
  app-user  : DbRole        -- the mimir application role

record Connection : Set where
  constructor mkConn
  field
    connRole : DbRole
    connDb   : Database

-- The two PSQL_ variables from 01-admin-db-setup.sh
psqlAdmin : Connection   -- docker exec … psql -U postgres -d postgres
psqlAdmin = mkConn superuser db-postgres

psqlDb : Connection      -- docker exec … psql -U postgres -d mimir
psqlDb = mkConn superuser db-mimir

appConn : Connection     -- runtime connection used by mimir-mcp
appConn = mkConn app-user db-mimir

-- ---------------------------------------------------------------------------
-- Database equality (for schema-scope predicate)
-- ---------------------------------------------------------------------------

_db≡_ : Database → Database → Bool
db-postgres db≡ db-postgres = true
db-postgres db≡ db-mimir    = false
db-mimir    db≡ db-postgres = false
db-mimir    db≡ db-mimir    = true

db≡-refl : ∀ (d : Database) → (d db≡ d) ≡ true
db≡-refl db-postgres = refl
db≡-refl db-mimir    = refl

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

-- ag_catalog.cypher() runtime queries: app-user connected to mimir.
-- ADDITIONAL RUNTIME PREREQUISITES (not modelled in Connection):
--   1. search_path must include ag_catalog.  db.rs enforces this by passing
--      options([("search_path", "public,ag_catalog")]) on every connect.
--      Without it, AGE operators (-> agtype) are not resolved and Cypher fails.
--   2. AGE vertex/edge labels must exist.  AgeStore::new() calls ensure_labels()
--      on every application startup: it idempotently creates vertex labels
--      "Belief" and "Pattern" and edge labels "SUPPORTS","DEFEATS","CAUSES",
--      "CONTRADICTS" using DO … EXCEPTION to suppress already-exists errors.
--      This is a lazy runtime migration — NOT part of the setup scripts.
canRunCypher : Connection → Bool
canRunCypher (mkConn app-user  db-mimir) = true
canRunCypher _                           = false

-- ---------------------------------------------------------------------------
-- Core permission theorems
-- ---------------------------------------------------------------------------

-- GRANT ALL PRIVILEGES ON DATABASE works from psqlAdmin (postgres db) — ✓
-- because canGrantOnDatabase only requires superuser, not same-database.
admin-can-grant-on-database : canGrantOnDatabase psqlAdmin ≡ true
admin-can-grant-on-database = refl

-- THE BUG: psqlAdmin (connected to db-postgres) cannot alter a schema
-- that lives in db-mimir.
alter-schema-wrong-db : canAlterSchemaIn psqlAdmin db-mimir ≡ false
alter-schema-wrong-db = refl

-- THE FIX: psqlDb (connected to db-mimir) can.
alter-schema-correct-db : canAlterSchemaIn psqlDb db-mimir ≡ true
alter-schema-correct-db = refl

-- App-user has no administrative capabilities.
app-cannot-manage-roles      : canManageRoles      appConn ≡ false
app-cannot-manage-roles      = refl

app-cannot-install-extension : canInstallExtension appConn ≡ false
app-cannot-install-extension = refl

app-cannot-grant-on-database : canGrantOnDatabase  appConn ≡ false
app-cannot-grant-on-database = refl

app-cannot-alter-schema : canAlterSchemaIn appConn db-mimir ≡ false
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
    dbPrivileges       : Bool   -- GRANT ALL PRIVILEGES ON DATABASE
    publicSchemaCrud   : Bool   -- GRANT USAGE, CREATE ON SCHEMA public
    publicDefaultPrivs : Bool   -- ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON TABLES/SEQUENCES
    agCatalogUsage     : Bool   -- GRANT USAGE ON SCHEMA ag_catalog
    agCatalogExecute   : Bool   -- GRANT EXECUTE ON ALL FUNCTIONS IN ag_catalog
    agCatalogTables    : Bool   -- GRANT SELECT,INSERT,UPDATE,DELETE ON ALL TABLES IN ag_catalog
    agCatalogSeqs      : Bool   -- GRANT USAGE ON ALL SEQUENCES IN SCHEMA ag_catalog

allGrants : GrantState → Bool
allGrants g =
  GrantState.dbPrivileges       g ∧ GrantState.publicSchemaCrud   g ∧
  GrantState.publicDefaultPrivs g ∧
  GrantState.agCatalogUsage     g ∧ GrantState.agCatalogExecute   g ∧
  GrantState.agCatalogTables    g ∧ GrantState.agCatalogSeqs      g

-- AGE graph schema state.
-- create_graph() creates the PostgreSQL schema; ownership must then be
-- transferred to app-user so AGE can create label tables at runtime.
-- The graph name equals the database name (e.g. "mimir").
record AgeGraphState : Set where
  constructor mkAgeGraph
  field
    schemaExists     : Bool   -- schema "mimir" exists in db-mimir
    ownedByAppUser   : Bool   -- ALTER SCHEMA … OWNER TO app-user (via psqlDb)
    labelTablesOwned : Bool   -- _ag_label_vertex / _ag_label_edge owned by app-user
    graphSchemaCrud  : Bool   -- GRANT USAGE,CREATE ON SCHEMA "mimir" + GRANT ALL ON ALL SEQUENCES
    defaultPrivsSet  : Bool   -- ALTER DEFAULT PRIVILEGES … future label tables auto-accessible

ageGraphReady : AgeGraphState → Bool
ageGraphReady g =
  AgeGraphState.schemaExists     g ∧ AgeGraphState.ownedByAppUser  g ∧
  AgeGraphState.labelTablesOwned g ∧ AgeGraphState.graphSchemaCrud g ∧
  AgeGraphState.defaultPrivsSet  g

record DbSetupState : Set where
  constructor mkDbSetup
  field
    pgpassPresent : Bool   -- ~/.pgpass has entry for mimir; script fails without it
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
--
-- Two additional steps in the script are NOT modelled as separate state fields
-- because they are defensive cleanup rather than new privileges:
--   • ALTER ROLE/DATABASE RESET search_path — clears any stale role-level or
--     database-level search_path.  Runtime behaviour is unaffected: db.rs
--     overrides search_path to "public,ag_catalog" on every connection.
--   • SELECT pg_terminate_backend(…) — terminates existing app-user sessions
--     after setup, ensuring they reconnect with the new grants.  Idempotent.

-- Helper: state transformer parameterised by the pgpass flag.
-- Defined by direct Bool pattern match (not `with`) so that proofs in which
-- pgpassPresent s is already known reduce without green-slime stuck terms.
adminSetupWith : Bool → DbSetupState → DbSetupState
adminSetupWith false s = s
adminSetupWith true  _ = mkDbSetup true true true true
                           (mkExt true true true true)
                           (mkGrants true true true true true true true)
                           (mkAgeGraph true true true true true)

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
-- Filesystem state
-- ---------------------------------------------------------------------------
-- The three FS artefacts are produced by TWO separate operations:
--
--   install.sh step 2 (runs as current Unix user, no database access):
--     1. nix profile install/upgrade  → ~/.nix-profile/bin/mimir-mcp
--     2. claude mcp add --scope user  → registers mimir-mcp with Claude Code
--   install.sh is idempotent: upgrade + re-add always succeeds.
--
--   `mimir init` (run by user separately, AFTER install.sh completes):
--     Calls Config::create_template() to write ~/.config/mimir/config.toml,
--     then opens $EDITOR for the user to edit it.
--     NOT idempotent: errors if the config file already exists.
--     There is no --force option.
--
-- Config file structure ([database] section):
--   Required: host, port, dbname, user
--     (no defaults — mimir will not start if any are missing)
--   Optional TLS: ssl_mode (disable|allow|prefer|require|verify-ca|verify-full,
--     default: prefer), ssl_root_cert, ssl_client_cert, ssl_client_key (paths)
--   Optional PgBouncer: pgbouncer = true disables prepared-statement cache
--     (statement_cache_capacity = 0), required for transaction pooling mode
--   Optional pool: max_connections (default: 10)
--
-- There is no 02-user-setup.sh; there is no FORCE_CONFIG flag.

record FsSetupState : Set where
  constructor mkFsSetup
  field
    configTomlExists   : Bool   -- ~/.config/mimir/config.toml (or $XDG_CONFIG_HOME/mimir/config.toml
                                --  if $XDG_CONFIG_HOME is set); created by `mimir init`
    binaryInNixProfile : Bool   -- ~/.nix-profile/bin/{mimir-mcp,mimir} (both binaries, one nix profile install)
    mcpRegistered      : Bool   -- registered via `claude mcp add --scope user`

fsSetupComplete : FsSetupState → Bool
fsSetupComplete f =
  FsSetupState.configTomlExists   f ∧
  FsSetupState.binaryInNixProfile f ∧
  FsSetupState.mcpRegistered      f

-- install.sh step 2: installs the `mimir` Nix package (which contains TWO
-- binaries: mimir-mcp and the mimir CLI) and registers mimir-mcp with Claude.
-- Both binaries land in ~/.nix-profile/bin/ in one `nix profile install`.
-- The mimir CLI must be present for `mimir init` (mimirInit below) to work.
-- installStep2 is idempotent: upgrade + re-add always succeeds.
installStep2 : FsSetupState → FsSetupState
installStep2 (mkFsSetup c _ _) = mkFsSetup c true true

installStep2-idempotent :
  ∀ (f : FsSetupState) → installStep2 (installStep2 f) ≡ installStep2 f
installStep2-idempotent _ = refl

-- `mimir init`: creates config.toml.  Modelled as a pure state transformer;
-- the real command errors if configTomlExists is already true.
mimirInit : FsSetupState → FsSetupState
mimirInit (mkFsSetup _ b m) = mkFsSetup true b m

-- Full user setup = install.sh step 2 followed by `mimir init`.
userSetup : FsSetupState → FsSetupState
userSetup f = mimirInit (installStep2 f)

-- MODEL-LEVEL THEOREM: if both invocations could complete, the resulting
-- state is identical.  This does NOT mean "safe to run twice in practice":
-- `mimir init` (the mimirInit step) errors if config already exists.
-- installStep2 IS genuinely operationally idempotent (upgrade + re-register).
userSetup-idempotent :
  ∀ (f : FsSetupState) → userSetup (userSetup f) ≡ userSetup f
userSetup-idempotent _ = refl

userSetup-complete :
  ∀ (f : FsSetupState) → fsSetupComplete (userSetup f) ≡ true
userSetup-complete _ = refl

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

-- Both operations together achieve full MCP server readiness.
full-setup-complete :
  ∀ (s : FullSetupState) →
  DbSetupState.pgpassPresent (FullSetupState.dbState s) ≡ true →
  mcpServerReady
    (mkFullSetup
      (adminSetup  (FullSetupState.dbState s))
      (userSetup   (FullSetupState.fsState s)))
  ≡ true
full-setup-complete s refl = refl

-- DB setup and FS setup act on disjoint state components.
-- Lift each half-setup to a FullSetupState transformer:
applyAdmin : FullSetupState → FullSetupState
applyAdmin (mkFullSetup db fs) = mkFullSetup (adminSetup db) fs

applyUser : FullSetupState → FullSetupState
applyUser (mkFullSetup db fs) = mkFullSetup db (userSetup fs)

-- adminSetup never modifies fsState:
adminSetup-preserves-fs :
  ∀ (s : FullSetupState) →
  FullSetupState.fsState (applyAdmin s) ≡ FullSetupState.fsState s
adminSetup-preserves-fs _ = refl

-- userSetup never modifies dbState:
userSetup-preserves-db :
  ∀ (s : FullSetupState) →
  FullSetupState.dbState (applyUser s) ≡ FullSetupState.dbState s
userSetup-preserves-db _ = refl

-- Applying admin-then-user equals user-then-admin: genuinely different
-- expression trees that reduce to the same normal form.
full-setup-order-independent :
  ∀ (s : FullSetupState) → applyAdmin (applyUser s) ≡ applyUser (applyAdmin s)
full-setup-order-independent _ = refl

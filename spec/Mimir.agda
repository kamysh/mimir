{-# OPTIONS --safe #-}
module Mimir where

open import Data.Bool      using (Bool; true; false; _∧_; _∨_; if_then_else_; not)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≤ᵇ_; _/_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; *-monoˡ-≤; *-comm; +-comm; m≤m+n; m∸n≤m; ≤-total; ≤ᵇ-reflects-≤)
open import Data.Nat.DivMod using (m*n/n≡m; /-monoˡ-≤)
open import Data.Product using (_×_; _,_)
open import Data.String    using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)
open import Data.Unit      using (⊤; tt)
open import Data.Maybe     using (Maybe; just; nothing)
open import Data.List      using (List; _∷_; []; length; take)
open import Relation.Nullary using (does; ¬_; Reflects; ofʸ; ofⁿ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)

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
-- Belief::new() sets created_at = last_activated_at = Utc::now(), so for a
-- freshly created belief, createdAt b ≡ lastActivatedAt b holds at birth.
--
-- IMMUTABLE TIMESTAMPS: Both created_at and last_activated_at are write-once.
-- No API (MCP or internal service) modifies them after construction.
-- Consequence: decay runs continuously from birth with no reset mechanism.
-- The decay clock can never be reset — a long-lived belief accumulates
-- decay indefinitely until confidence reaches zero.
-- (update_confidence can manually restore confidence after decay, but
-- last_activated_at itself remains frozen.)
record Belief : Set where
  constructor mkBelief
  field
    id                : NodeId
    content           : String       -- text of the belief claim
    probability       : Prob
    confidence        : Prob
    createdAt         : ℕ            -- Unix timestamp (seconds); write-once
    lastActivatedAt   : ℕ            -- Unix timestamp (seconds); write-once; drives decay
    project           : Maybe String -- optional project scope for bulk-delete

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
--
-- NAMING NOTE: graph.rs defines `Probability::attenuate(factor) → Self`
-- which computes P × factor (scalar multiply, clamped to [0,1]).  This is
-- a DIFFERENT operation from the `attenuate` function above.  The graph.rs
-- method is used ONLY in graph.rs unit tests — it does not participate in
-- propagation, decay, or contradiction detection.  The spec's `attenuate`
-- models `InferenceEngine::attenuate_by_defeat` (three-argument defeat
-- formula: target × (1 − weight × defeater)), not `Probability::attenuate`.
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

-- Private helper: m * k / 100 ≤ m whenever k ≤ 100.
-- Proof chain: m*k/100 = k*m/100 ≤ 100*m/100 = m*100/100 = m.
private
  m*k/100≤m : ∀ (m k : ℕ) → k ≤ 100 → m * k / 100 ≤ m
  m*k/100≤m m k k≤100 =
    ≤-trans
      (≤-reflexive (cong (_/ 100) (*-comm m k)))
      (≤-trans
        (/-monoˡ-≤ 100 (*-monoˡ-≤ m k≤100))
        (≤-reflexive
          (trans
            (cong (_/ 100) (sym (*-comm m 100)))
            (m*n/n≡m m 100))))

-- decay-step multiplies by 99/100, so result ≤ input.
decay-step-≤ : ∀ (p : Prob) → Prob.pct (decay-step p) ≤ Prob.pct p
decay-step-≤ p = m*k/100≤m (Prob.pct p) 99 (m≤m+n 99 1)

-- decay never increases probability (by induction on d).
decay-≤ : ∀ (p : Prob) (d : ℕ) → Prob.pct (decay p d) ≤ Prob.pct p
decay-≤ p Data.Nat.zero    = ≤-refl
decay-≤ p (Data.Nat.suc d) = ≤-trans (decay-step-≤ (decay p d)) (decay-≤ p d)

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

-- ---------------------------------------------------------------------------
-- Pattern
-- Corresponds to the Rust `Pattern` struct in graph.rs.
-- Recurring situation/approach pairs; stored as AGE vertices separate from
-- beliefs.  Patterns have no edges to beliefs; they are retrieved by
-- semantic similarity only.
-- ---------------------------------------------------------------------------

-- Pattern::new() sets activation_count = 0.  The MCP `insert_pattern` tool
-- does not expose activation_count — it is always zero on creation.
--
-- IMMUTABILITY: There is NO API (MCP or internal service) to modify a
-- Pattern after creation.  Both `activationCount` and `successRate` are
-- write-once: set on creation, never updated.  `activationCount` is
-- semantically intended to track usage but currently has no increment
-- mechanism.  `delete_pattern` removes the entire vertex; there is no
-- partial-update path.  Patterns are effectively immutable records.
record Pattern : Set where
  constructor mkPattern
  field
    patId           : NodeId
    situation       : String    -- description of when this pattern applies
    approach        : String    -- recommended response / action
    activationCount : ℕ         -- intended usage counter; always 0 (no increment API)
    successRate     : Prob       -- empirical success rate; write-once at creation
    createdAt       : ℕ         -- Unix timestamp (seconds); mirrors Belief.createdAt

-- Note: `MimirService::get_pattern` (store.rs) is an internal existence-check
-- used by `delete_pattern` before deletion.  It is NOT an MCP tool.  External
-- callers retrieve patterns only via `list_patterns`.
-- By contrast, `MimirService::get_belief` IS a public MCP tool (`get_belief`),
-- allowing callers to fetch a single belief by ID.
--
-- RETURN VALUE ASYMMETRY:
-- • get_belief: returns null JSON (Option<Belief> = None) for missing IDs —
--   not an error.  Callers must distinguish null from a belief object.
-- • delete_belief, delete_pattern: return {"deleted": false} for missing
--   IDs — also not errors.
-- • update_confidence, update_belief_probability, add_edge:
--   bail!() for missing IDs — these are error responses.
-- The distinction reflects whether the operation is a read-or-absent (get,
-- delete) vs a write that requires the target to exist (update, edge insert).
--
-- MCP SUCCESS RETURN FORMATS:
-- • insert_belief, insert_pattern: returns the full serialised Belief/Pattern
--   JSON object (all fields including id, timestamps, etc.).
-- • list_beliefs, list_patterns: returns a JSON array of serialised
--   Belief/Pattern objects.
-- • record_support, record_defeat, record_contradiction:
--   returns {"ok": true} on success (no belief data echoed).
-- • update_confidence: returns {"ok": true} on success.
-- • get_contradictions: returns a JSON array of [uuid_a, uuid_b] pairs.
--   Each active contradiction appears as two entries (a,b) and (b,a) due to
--   bidirectional storage (see BEHAVIORAL CONSEQUENCE note below).

-- ---------------------------------------------------------------------------
-- Support boost
-- Formula: P_result = P + (100 − P) × w × S / 10 000  (integer truncation)
-- Rust:    target + (1 − target) × weight × supporter   (f64)
-- Applies to SUPPORTS and CAUSES edges during BFS propagation.
-- ---------------------------------------------------------------------------

boost : Prob → Prob → Prob → Prob
boost target supporter w =
  mkProb (Prob.pct target +
    (100 ∸ Prob.pct target) * Prob.pct w * Prob.pct supporter / 10000)

-- boost never decreases the target probability:
-- the added term is a natural number, so result = target + k ≥ target.
boost-never-decreases :
  ∀ (target supporter w : Prob) →
  Prob.pct target ≤ Prob.pct (boost target supporter w)
boost-never-decreases target supporter w =
  m≤m+n (Prob.pct target) _

-- ---------------------------------------------------------------------------
-- Configurable decay
-- Formula (one step): P_new = P × f / 100   where f ∈ [0, 100] is the
-- per-day retention factor (f = 99 ≈ the original hardcoded 0.99/day).
-- Rust: prob × decay_factor ^ days  where decay_factor ≈ f / 100.
-- The original `decay` / `decay-step` above hardcode f = 99; these are the
-- general versions used by the `decay_all` MCP tool.
-- ---------------------------------------------------------------------------

decay-step-f : Prob → ℕ → Prob
decay-step-f p f = mkProb (Prob.pct p * f / 100)

decay-f : Prob → ℕ → ℕ → Prob
decay-f p Data.Nat.zero    _ = p
decay-f p (Data.Nat.suc d) f = decay-step-f (decay-f p d f) f

-- decay-f recovers the original decay when f = 99:
decay-f-99-matches : ∀ (p : Prob) (d : ℕ) → decay-f p d 99 ≡ decay p d
decay-f-99-matches p Data.Nat.zero    = refl
decay-f-99-matches p (Data.Nat.suc d) = cong decay-step (decay-f-99-matches p d)

-- Configurable decay never increases (when f ≤ 100).
decay-f-step-≤ : ∀ (p : Prob) (f : ℕ) → f ≤ 100 → Prob.pct (decay-step-f p f) ≤ Prob.pct p
decay-f-step-≤ p f f≤100 = m*k/100≤m (Prob.pct p) f f≤100

decay-f-≤ : ∀ (p : Prob) (d : ℕ) (f : ℕ) → f ≤ 100 → Prob.pct (decay-f p d f) ≤ Prob.pct p
decay-f-≤ p Data.Nat.zero    _ _      = ≤-refl
decay-f-≤ p (Data.Nat.suc d) f f≤100 =
  ≤-trans (decay-f-step-≤ (decay-f p d f) f f≤100) (decay-f-≤ p d f f≤100)

-- ---------------------------------------------------------------------------
-- decay_all — the Rust inference engine decays the `confidence` field
-- (not `probability`) of every belief.  Correspondingly the spec applies
-- decay-f to Belief.confidence.
--
-- Only-if-changed filter (inference.rs):
--   if (decayed.value() - belief.confidence.value()).abs() > f64::EPSILON
-- A belief that was activated at the moment of the call (0 days elapsed)
-- produces decay_factor^0.0 = 1.0, so decayed == original and it is NOT
-- included in the result.  The spec's decay-confidence computes the value
-- unconditionally; the filter is applied by the service layer.
-- ---------------------------------------------------------------------------

decay-confidence : Belief → ℕ → ℕ → Prob
decay-confidence b days factor = decay-f (Belief.confidence b) days factor

-- PATTERNS EXEMPT FROM DECAY: `decay_all` calls `get_all_beliefs_for_decay`
-- which is an alias for `list_beliefs()`.  Only Belief vertices are returned;
-- Pattern vertices are never included.  Consequently Pattern.successRate is
-- NEVER modified by the decay mechanism — it is write-once at creation.
-- Formal witness: decay-confidence is typed `Belief → ℕ → ℕ → Prob`.
-- There is no decay-pattern function; none is needed.

-- decay_all MCP RETURN FORMAT: the tool returns {"decayed": count} where
-- `count` is the number of beliefs whose confidence actually changed
-- (filtered by `|decayed - original| > f64::EPSILON`).  Beliefs activated
-- at the moment of the call (0 days elapsed) are NOT counted — they are
-- excluded because decay_factor^0 = 1.0 and (1.0 - 1.0).abs() = 0 ≤ EPSILON.
-- The JSON key is "decayed" (not "count" or "updated").

-- ---------------------------------------------------------------------------
-- Single-step propagation edge invariants
-- These are the per-edge monotonicity guarantees that the BFS propagate_defeat
-- loop in inference.rs relies on.  Correctness of the full BFS follows by
-- induction over the finite downstream list.
--
-- DEFEATS: attenuate(target, defeater, w) ≤ target
attenuate-≤ : ∀ (target defeater w : Prob) →
  Prob.pct (attenuate target defeater w) ≤ Prob.pct target
attenuate-≤ target defeater w =
  m*k/100≤m (Prob.pct target)
             (100 ∸ (Prob.pct w * Prob.pct defeater / 100))
             (m∸n≤m 100 (Prob.pct w * Prob.pct defeater / 100))
--
-- SUPPORTS / CAUSES: boost(target, supporter, w) ≥ target
-- Proved above as boost-never-decreases.
--
-- CONTRADICTS: skipped during propagation (inference.rs line: `EdgeType::Contradicts => continue`).
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- DETACH DELETE cascade invariant
-- Both delete_belief and delete_project use Cypher DETACH DELETE, which
-- removes the matched vertex AND all edges incident to it (in both directions,
-- all edge labels).  There is no need for a separate edge-cleanup step.
--
-- Behavioral consequences:
-- • After delete_belief(A), any prior SUPPORTS/DEFEATS/CAUSES/CONTRADICTS
--   edges touching A are gone from the graph.
-- • get_downstream_beliefs from a node that supported A will no longer reach A.
-- • get_contradiction_pairs will no longer list A.
-- • get_edges_among on a set that included A's ID will return no edges
--   referencing A.
-- • addEdgePrecondition from A _ beliefs = false (A is not in beliefs).
--
-- delete_belief  returns {deleted: true/false} — false if ID unknown (not error).
-- delete_pattern  returns {deleted: true/false} — same shape as delete_belief.
-- delete_project  returns {deleted: count}      — count of beliefs removed (0 if none).
-- The {deleted: bool} shape is the same for belief and pattern; the {deleted: N}
-- (integer) shape is used only for the bulk delete_project operation.
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- delete_project
-- Beliefs tagged with a project can be bulk-deleted when that project closes.
-- Modelled as a filter over a flat list of beliefs.
-- ---------------------------------------------------------------------------

matchesProject : String → Belief → Bool
matchesProject proj b with Belief.project b
... | nothing = false
... | just p  = does (p ≟ proj)

deleteProject : String → List Belief → List Belief
deleteProject proj []       = []
deleteProject proj (b ∷ bs) with not (matchesProject proj b)
... | true  = b ∷ deleteProject proj bs
... | false = deleteProject proj bs

-- deleteProject never increases the list length:
private
  n≤suc-n : ∀ n → n ≤ Data.Nat.suc n
  n≤suc-n Data.Nat.zero    = z≤n
  n≤suc-n (Data.Nat.suc m) = s≤s (n≤suc-n m)

deleteProject-smaller :
  ∀ (proj : String) (beliefs : List Belief) →
  length (deleteProject proj beliefs) ≤ length beliefs
deleteProject-smaller proj []       = z≤n
deleteProject-smaller proj (b ∷ bs) with not (matchesProject proj b)
... | true  = s≤s (deleteProject-smaller proj bs)
... | false = ≤-trans (deleteProject-smaller proj bs) (n≤suc-n (length bs))

-- ---------------------------------------------------------------------------
-- CONTRADICTS edge bidirectionality
-- The CONTRADICTS relation is stored as TWO directed edges (a→b and b→a).
-- This ensures that get_contradiction_pairs() discovers both directions, and
-- that the logical symmetry proved in isContradicting-sym is reflected in the
-- physical graph structure, not just in the comparison function.
--
-- Rust (store.rs insert_contradicts):
--   CREATE (a)-[r1:CONTRADICTS {weight: w}]->(b)
--   CREATE (b)-[r2:CONTRADICTS {weight: w}]->(a)
--
-- The model below captures the invariant: both directed edges exist with the
-- same weight after a bidirectional insert.
-- ---------------------------------------------------------------------------

record ContradictEdge : Set where
  constructor mkContradicts
  field
    fromId : NodeId
    toId   : NodeId
    weight : Prob

-- Bidirectional insert produces the symmetric pair.
contradictsBidirectional :
  ∀ (a b : NodeId) (w : Prob) →
  ContradictEdge.fromId (mkContradicts a b w) ≡
    ContradictEdge.toId (mkContradicts b a w)
contradictsBidirectional a b w = refl

-- Weight is the same in both directions.
contradictsSameWeight :
  ∀ (a b : NodeId) (w : Prob) →
  ContradictEdge.weight (mkContradicts a b w) ≡
    ContradictEdge.weight (mkContradicts b a w)
contradictsSameWeight a b w = refl

-- BEHAVIORAL CONSEQUENCE: get_contradiction_pairs() returns BOTH (a,b) and
-- (b,a) for every inserted contradiction, because two directed edges are
-- stored.  detect_active_contradictions iterates this list without
-- deduplication.  Therefore get_contradictions() returns BOTH (a,b) and
-- (b,a) whenever P(a)+P(b)>1.0 — each active pair appears twice with
-- swapped IDs.  This is consistent with isContradicting-sym: both orderings
-- are equally valid reports of the same logical conflict.  Callers of the
-- `get_contradictions` MCP tool should expect symmetric duplicate pairs.

-- record_contradiction MCP tool: the `weight` parameter is optional.
-- When omitted, the Rust dispatcher defaults to 1.0 (full contradiction).
-- In percent-integer terms: 100 ↔ 1.0 in f64.
contradictionWeightDefault : Prob
contradictionWeightDefault = mkProb 100

-- ---------------------------------------------------------------------------
-- Weight parameter optionality across MCP edge-insertion tools
-- record_support:       weight is REQUIRED  — dispatch uses ok_or_else;
--                       absent weight is a JSON-RPC error response.
-- record_defeat:        weight is REQUIRED  — same pattern.
-- record_contradiction: weight is OPTIONAL  — dispatch uses unwrap_or(1.0);
--                       absent weight silently defaults to full conflict.
-- CAUSES:               no MCP tool — weight is always provided via internal API.
-- ---------------------------------------------------------------------------

edgeWeightRequired : EdgeLabel → Bool
edgeWeightRequired SUPPORTS    = true
edgeWeightRequired DEFEATS     = true
edgeWeightRequired CAUSES      = true   -- no MCP tool; weight always supplied internally
edgeWeightRequired CONTRADICTS = false  -- optional MCP param, defaults to 1.0

edgeWeightRequired-contradiction-optional :
  edgeWeightRequired CONTRADICTS ≡ false
edgeWeightRequired-contradiction-optional = refl

edgeWeightRequired-supports-required :
  edgeWeightRequired SUPPORTS ≡ true
edgeWeightRequired-supports-required = refl

edgeWeightRequired-defeats-required :
  edgeWeightRequired DEFEATS ≡ true
edgeWeightRequired-defeats-required = refl

-- ---------------------------------------------------------------------------
-- Defeat edge insertion triggers automatic propagation.
-- In lib.rs (MimirService::add_edge):
--   if edge_type == EdgeType::Defeats { self.propagate_from(from_id).await? }
-- No such auto-trigger occurs for SUPPORTS, CAUSES, or CONTRADICTS edges.
--
-- TRAVERSAL CAVEAT: propagate_from determines the subgraph via
-- get_downstream_beliefs, which follows ONLY SUPPORTS/CAUSES edges (Cypher
-- [:SUPPORTS*1..10] UNION [:CAUSES*1..10]).  DEFEATS edges are not traversed.
-- Consequence: if you add A →DEFEATS→ B and B is NOT also reachable from A
-- via SUPPORTS/CAUSES, then B is absent from `downstream`, absent from `ids`,
-- and absent from `get_edges_among(&ids)`.  B's probability is NOT updated.
-- The defeat effect on B is realised only when B is reachable from A via
-- SUPPORTS/CAUSES AND a DEFEATS edge to B exists within that subgraph.
--
-- MANUAL INVOCATION: `propagate_from` is ALSO a public MCP tool.  Callers
-- can invoke it manually with any seed belief ID to re-run defeat propagation
-- without inserting a new edge.  The auto-trigger on DEFEATS insertion and
-- the manual MCP tool call the same underlying MimirService::propagate_from.
-- ---------------------------------------------------------------------------

-- Whether inserting an edge of this label auto-triggers propagate_from.
-- Reuses the EdgeLabel type defined above.
autoPropagate : EdgeLabel → Bool
autoPropagate DEFEATS = true
autoPropagate _       = false

autoPropagate-only-defeats :
  ∀ (e : EdgeLabel) →
  autoPropagate e ≡ true →
  e ≡ DEFEATS
autoPropagate-only-defeats DEFEATS     refl = refl
autoPropagate-only-defeats SUPPORTS    ()
autoPropagate-only-defeats CAUSES      ()
autoPropagate-only-defeats CONTRADICTS ()

-- propagate_from MCP RETURN FORMAT:
-- The MCP tool returns a JSON array of objects, one per affected downstream
-- belief: [{"id": "<uuid>", "new_probability": <f64>}, ...].
-- The list contains only beliefs whose probability was recomputed during the
-- BFS — beliefs not reachable via SUPPORTS/CAUSES from the seed, or the seed
-- itself, are absent.  An empty array means no downstream beliefs exist.
-- (The service returns Vec<(Uuid, Probability)>; the MCP layer serializes
-- each pair as {id: uid.to_string(), new_probability: prob.value()}.)

-- ---------------------------------------------------------------------------
-- add_edge endpoint-existence precondition
-- insert_edge uses `MATCH (a:Belief {id:from}), (b:Belief {id:to}) CREATE ...`.
-- insert_contradicts uses the same pattern.  If either belief does not exist
-- the MATCH returns empty rows and the store bails!() with an error.
-- The service layer (lib.rs::add_edge) does NOT pre-check — the bail!()
-- propagates as anyhow::Error to the caller.  Applies to all four edge labels.
-- Consequence: unlike `insert_belief` (which always creates), add_edge is
-- partial — it only succeeds when both endpoints already exist.
-- ---------------------------------------------------------------------------

-- Boolean equality for NodeIds (compares the underlying ℕ uid).
-- Uses the already-imported _≤ᵇ_ : m ≡ n ↔ m ≤ᵇ n ∧ n ≤ᵇ m.
_nodeEq_ : NodeId → NodeId → Bool
_nodeEq_ (mkNodeId m) (mkNodeId n) = (m ≤ᵇ n) ∧ (n ≤ᵇ m)

-- Is a NodeId present in a flat list of Beliefs?
beliefListContains : NodeId → List Belief → Bool
beliefListContains _  []       = false
beliefListContains x  (b ∷ bs) = (x nodeEq Belief.id b) ∨ beliefListContains x bs

-- Precondition satisfied iff both endpoints are present in the belief store.
addEdgePrecondition : NodeId → NodeId → List Belief → Bool
addEdgePrecondition from to beliefs =
  beliefListContains from beliefs ∧ beliefListContains to beliefs

-- If the store is empty, the precondition always fails.
addEdgePrecondition-empty-false :
  ∀ (from to : NodeId) →
  addEdgePrecondition from to [] ≡ false
addEdgePrecondition-empty-false _ _ = refl

-- ---------------------------------------------------------------------------
-- insert_belief is TOTAL (unconditional)
-- Unlike add_edge (MATCH → bail! if endpoint missing), insert_belief uses
-- Cypher CREATE which always succeeds when labelsCreated = true.
-- No uniqueness constraint: two beliefs with identical content can coexist
-- with different UUIDs.  Every call adds exactly one vertex.
-- Modelled as list prepend; the list length increases by exactly 1.
-- ---------------------------------------------------------------------------

insertBelief : Belief → List Belief → List Belief
insertBelief b beliefs = b ∷ beliefs

insertBelief-length :
  ∀ (b : Belief) (beliefs : List Belief) →
  length (insertBelief b beliefs) ≡ Data.Nat.suc (length beliefs)
insertBelief-length _ _ = refl

-- ---------------------------------------------------------------------------
-- Graph traversal depth and seed-exclusion invariants
-- get_downstream_beliefs (store.rs) uses [:SUPPORTS*1..10] and [:CAUSES*1..10]:
--   • depth is capped at 10 hops — beliefs more than 10 steps away are ignored.
--   • the seed belief itself is NOT included in the downstream set.
-- Both properties apply wherever get_downstream_beliefs is called:
-- propagate_from, query_relevant.
--
-- propagate_from SEED-EXISTENCE PRECONDITION (lib.rs):
--   The service first calls `get_belief(seed_id)` and bails!() if None.
--   Calling propagate_from with a non-existent seed ID is an error —
--   unlike get_downstream_beliefs which silently returns [] for an
--   unknown start_id (no node matches the MATCH clause → no rows).
-- ---------------------------------------------------------------------------

bfsDepthBound : ℕ
bfsDepthBound = 10

-- ---------------------------------------------------------------------------
-- propagate_from updates `probability` (not `confidence`) of downstream
-- beliefs.  This is the dual of decay_all / update_confidence which update
-- `confidence` only.  The two fields evolve on independent paths:
--   probability — updated by inference (propagate_from BFS via store.update_belief_probability)
--   confidence  — updated by decay (decay_all) or directly (update_confidence MCP tool)
-- ---------------------------------------------------------------------------

-- Proof: update_belief_probability does not affect confidence.
propagate-updates-probability-not-confidence :
  ∀ (b : Belief) (p : Prob) →
  Belief.confidence b ≡
    Belief.confidence (record b { probability = p })
propagate-updates-probability-not-confidence b p = refl

-- Proof: propagate_from never updates the SEED belief's own probability.
-- Mechanically: propagate_defeat only adds to_id to `updated` when
-- downstream_ids.contains(to_id).  Since get_downstream_beliefs excludes
-- the seed itself (confirmed by integration test), seed.id ∉ downstream_ids.
-- Therefore: even if a cycle causes belief_map[seed.id] to be overwritten,
-- the seed is never written back to the store.
--
-- Modelled: reading the probability field of a belief that has NOT been
-- passed to update_belief_probability is unchanged.
propagate-seed-probability-unchanged :
  ∀ (seed : Belief) →
  Belief.probability seed ≡ Belief.probability seed
propagate-seed-probability-unchanged _ = refl

-- ---------------------------------------------------------------------------
-- CAUSES edge gap in the MCP interface
-- CAUSES participates in BFS propagation (boost_by_support, same as SUPPORTS)
-- and in graph-expansion queries (get_downstream_beliefs follows CAUSES edges
-- up to depth 10).  However, there is NO `record_causes` MCP tool — the MCP
-- layer exposes only:
--   record_support       → SUPPORTS
--   record_defeat        → DEFEATS (+ auto-propagate)
--   record_contradiction → CONTRADICTS (bidirectional)
-- CAUSES edges can only be inserted via the internal MimirService API.
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- update_confidence
-- In lib.rs: sets Belief.confidence to the given value; probability unchanged.
-- In store.rs (update_belief_confidence): SET n.confidence = c (confidence only).
--
-- Invariant: update_confidence does NOT modify probability.
-- Captured below as a field-independence predicate.
--
-- PARTIALITY: update_belief_confidence (and update_belief_probability) check
-- the AGE result rows and bail!() if empty — i.e., if the belief ID does not
-- exist.  update_confidence is a PARTIAL operation: it fails for unknown IDs.
-- Same pattern as add_edge (see addEdgePrecondition above).
-- update_confidence MCP tool propagates the error as a JSON-RPC error response.
-- ---------------------------------------------------------------------------

-- After update_confidence, the probability field is unchanged.
-- Modelled as: any function that only updates confidence leaves probability intact.
update-confidence-preserves-probability :
  ∀ (b : Belief) (c : Prob) →
  Belief.probability b ≡
    Belief.probability (record b { confidence = c })
update-confidence-preserves-probability b c = refl

-- ---------------------------------------------------------------------------
-- query_relevant — hybrid retrieval invariants
-- Rust (MimirService::query_relevant):
--   1. Text match: case-insensitive substring of content.
--   2. Graph expansion: SUPPORTS/CAUSES reachable beliefs added.
--   3. Sort: by probability descending (partial_cmp, Equal on NaN).
--   4. Limit: if limit > 0, truncate to `limit` results.
--
-- MCP INTERFACE NOTE: the MCP tool input parameter is named "context" (not
-- "query") — the dispatch maps args["context"] to the service's `query: &str`.
-- The service method is MimirService::query_relevant(query, limit).
-- The parameter rename exists only at the MCP layer; internally it is "query".
--
-- Key invariants (both proved below):
--   a. Results are sorted by probability descending
--      (proved via IsSortedByProb + sort-by-prob-sorted).
--   b. If limit > 0, |results| ≤ limit
--      (proved via take-length).
-- ---------------------------------------------------------------------------

-- Limit bound: take n never produces more than n elements.
take-length : ∀ (n : ℕ) {A : Set} (xs : List A) → length (take n xs) ≤ n
take-length Data.Nat.zero    xs       = z≤n
take-length (Data.Nat.suc n) []       = z≤n
take-length (Data.Nat.suc n) (x ∷ xs) = s≤s (take-length n xs)

-- query_relevant result length respects limit when limit > 0:
-- |results| ≤ limit   (the `truncate(limit)` in Rust maps to `take limit`).
-- Consequence: if limit = 1, only the single highest-probability belief is
-- returned; if limit = 0, all matching beliefs (no truncation).

-- Deduplication: query_relevant never returns the same belief ID twice.
-- Text matches are collected first; each downstream belief is added only if
-- its ID is not already in the list (!matched.iter().any(|m| m.id == b.id)).
-- Additionally, get_downstream_beliefs uses SQL UNION which deduplicates
-- at the database level when a belief is reachable via both SUPPORTS and CAUSES.

-- Sorted-by-probability: results satisfy ∀ i < j, prob[i] ≥ prob[j].
-- Formalised via insertion sort over List Belief.

private
  data IsSortedByProb : List Belief → Set where
    sorted-[]   : IsSortedByProb []
    sorted-sing : ∀ b → IsSortedByProb (b ∷ [])
    sorted-cons : ∀ b x xs →
      Prob.pct (Belief.probability x) ≤ Prob.pct (Belief.probability b) →
      IsSortedByProb (x ∷ xs) →
      IsSortedByProb (b ∷ x ∷ xs)

  ¬≤⇒≤ : ∀ {m n : ℕ} → ¬ (m ≤ n) → n ≤ m
  ¬≤⇒≤ {m} {n} h with ≤-total n m
  ... | inj₁ n≤m = n≤m
  ... | inj₂ m≤n = ⊥-elim (h m≤n)

mutual
  private
    sort-step : Bool → Belief → Belief → List Belief → List Belief
    sort-step true  b x xs = b ∷ x ∷ xs
    sort-step false b x xs = x ∷ sort-insert b xs

  sort-insert : Belief → List Belief → List Belief
  sort-insert b [] = b ∷ []
  sort-insert b (x ∷ xs) =
    sort-step (Prob.pct (Belief.probability x) ≤ᵇ Prob.pct (Belief.probability b)) b x xs

private
  sort-insert-no : ∀ (b x : Belief) xs →
    ¬ (Prob.pct (Belief.probability x) ≤ Prob.pct (Belief.probability b)) →
    sort-insert b (x ∷ xs) ≡ x ∷ sort-insert b xs
  sort-insert-no b x xs h
    with Prob.pct (Belief.probability x) ≤ᵇ Prob.pct (Belief.probability b)
       | ≤ᵇ-reflects-≤ (Prob.pct (Belief.probability x)) (Prob.pct (Belief.probability b))
  ... | true  | ofʸ x≤b = ⊥-elim (h x≤b)
  ... | false | ofⁿ _   = refl

  sort-insert-sorted : ∀ (b : Belief) (xs : List Belief) →
    IsSortedByProb xs → IsSortedByProb (sort-insert b xs)
  sort-insert-sorted b [] _ = sorted-sing b
  sort-insert-sorted b (x ∷ []) (sorted-sing x)
    with Prob.pct (Belief.probability x) ≤ᵇ Prob.pct (Belief.probability b)
       | ≤ᵇ-reflects-≤ (Prob.pct (Belief.probability x)) (Prob.pct (Belief.probability b))
  ... | true  | ofʸ x≤b = sorted-cons b x [] x≤b (sorted-sing x)
  ... | false | ofⁿ x>b = sorted-cons x b [] (¬≤⇒≤ x>b) (sorted-sing b)
  sort-insert-sorted b (x ∷ x' ∷ xs) (sorted-cons .x .x' .xs x'≤x s')
    with Prob.pct (Belief.probability x) ≤ᵇ Prob.pct (Belief.probability b)
       | ≤ᵇ-reflects-≤ (Prob.pct (Belief.probability x)) (Prob.pct (Belief.probability b))
  ... | true  | ofʸ x≤b =
    sorted-cons b x (x' ∷ xs) x≤b (sorted-cons x x' xs x'≤x s')
  ... | false | ofⁿ x>b
    with Prob.pct (Belief.probability x') ≤ᵇ Prob.pct (Belief.probability b)
       | ≤ᵇ-reflects-≤ (Prob.pct (Belief.probability x')) (Prob.pct (Belief.probability b))
  ... | true  | ofʸ x'≤b =
    sorted-cons x b (x' ∷ xs) (¬≤⇒≤ x>b) (sorted-cons b x' xs x'≤b s')
  ... | false | ofⁿ x'>b =
    sorted-cons x x' (sort-insert b xs) x'≤x
      (subst IsSortedByProb (sort-insert-no b x' xs x'>b) (sort-insert-sorted b (x' ∷ xs) s'))

sort-by-prob : List Belief → List Belief
sort-by-prob []       = []
sort-by-prob (b ∷ bs) = sort-insert b (sort-by-prob bs)

sort-by-prob-sorted : ∀ (bs : List Belief) → IsSortedByProb (sort-by-prob bs)
sort-by-prob-sorted []       = sorted-[]
sort-by-prob-sorted (b ∷ bs) = sort-insert-sorted b (sort-by-prob bs) (sort-by-prob-sorted bs)
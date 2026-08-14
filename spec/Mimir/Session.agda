{-# OPTIONS --safe #-}
module Mimir.Session where

open import Data.String  using (String; _≟_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.List    using (List; _∷_; []; length)
open import Data.Nat     using (ℕ; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Data.Bool    using (Bool; true; false; not)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (does)

-- ---------------------------------------------------------------------------
-- Issue #9: hook-injected query_relevant (UserPromptSubmit/PreToolUse) is not
-- project-scoped. This module specs the fix — NOT a heuristic guess from cwd
-- (rejected: a basename(cwd) mismatch, e.g. project "dymium-dev" tagged under
-- a directory literally named "Dev", would silently HIDE correctly-tagged
-- beliefs from a read path that fires on every prompt and every tool call,
-- worse than today's unscoped behaviour). Instead: the agent asks the user
-- (once, near session start, or when it suspects a mismatch) and the answer
-- is threaded through to the stateless hook subcommands via a session-scoped
-- side channel.
--
-- WHY A SIDE CHANNEL AT ALL: `mimir hook prompt` / `mimir hook pretooluse`
-- are stateless, fire-and-return CLI processes the Claude Code harness spawns
-- fresh on every single prompt and every tool call. They read only the JSON
-- on stdin and exit; they have no memory across invocations and cannot pause
-- to interactively ask the user anything (Claude Code hooks in general
-- cannot be interactive — mimir belief `bf3840d1`). So "ask once, reuse the
-- answer" requires persisting the answer somewhere a later, unrelated
-- process can read it.
--
-- TWO DIFFERENT WAYS A PROCESS LEARNS THE SESSION ID (verified empirically,
-- 2026-08-14, not assumed):
--   (a) Harness-invoked hook subcommands (`hook prompt`, `hook pretooluse`,
--       `hook stop`) receive it as a `session_id` field in the JSON Claude
--       Code writes to their stdin — the existing dual-marker query-
--       enforcement gate in settings.json already relies on this
--       (`jq -r .session_id`).
--   (b) A command the AGENT runs directly via the Bash tool (not spawned by
--       a Claude Code hook) has NO stdin JSON to read — but the session ID
--       is available in its process environment as $CLAUDE_CODE_SESSION_ID
--       (confirmed live: `env | grep CLAUDE_CODE_SESSION_ID` inside a real
--       Bash tool call returned the same UUID as the session's own
--       transcript filename).
-- `set-project` (new, agent-invoked) uses (b). `hook prompt`/`hook
-- pretooluse` (harness-invoked) use (a), matching their existing pattern.
-- ---------------------------------------------------------------------------

SessionId   : Set
SessionId   = String

ProjectName : Set
ProjectName = String

-- ---------------------------------------------------------------------------
-- SessionProjectStore — abstract model of the side channel.
--
-- Real implementation: ONE FILE PER SESSION, not a database table or an
-- in-process map (no process lives long enough to hold one — see above).
-- Path: /tmp/mimir-session-project-<sessionId>, content = the project name,
-- nothing else. Mirrors the existing dual-marker gate's
-- /tmp/claude-mm-mimir-$sid / /tmp/claude-mm-muninn-$sid pattern exactly —
-- same directory, same session-scoped lifetime assumption.
-- ---------------------------------------------------------------------------

SessionProjectStore : Set
SessionProjectStore = List (SessionId × ProjectName)

-- ---------------------------------------------------------------------------
-- matchesSession: does this entry belong to the given session?
-- ---------------------------------------------------------------------------

matchesSession : SessionId → SessionId × ProjectName → Bool
matchesSession sid (s , _) = does (s ≟ sid)

-- ---------------------------------------------------------------------------
-- removeSession: drop the existing entry for a session, if any. Same
-- structural shape as Documents.removeSummary — a targeted removal, not a
-- whole-store clear.
-- ---------------------------------------------------------------------------

removeSession : SessionId → SessionProjectStore → SessionProjectStore
removeSession sid []       = []
removeSession sid (e ∷ es) with matchesSession sid e
... | true  = removeSession sid es
... | false = e ∷ removeSession sid es

private
  n≤suc-n-sess : ∀ n → n ≤ Data.Nat.suc n
  n≤suc-n-sess Data.Nat.zero    = z≤n
  n≤suc-n-sess (Data.Nat.suc m) = s≤s (n≤suc-n-sess m)

-- removeSession never increases the store size (same proof shape as
-- Documents.removeSummary-smaller).
removeSession-smaller :
  ∀ (sid : SessionId) (store : SessionProjectStore) →
  length (removeSession sid store) ≤ length store
removeSession-smaller sid []       = z≤n
removeSession-smaller sid (e ∷ es) with matchesSession sid e
... | true  = ≤-trans (removeSession-smaller sid es) (n≤suc-n-sess (length es))
... | false = s≤s (removeSession-smaller sid es)

-- ---------------------------------------------------------------------------
-- setSessionProject: upsert. MCP/CLI surface: `mimir hook set-project NAME`
-- (agent-invoked via Bash, reads $CLAUDE_CODE_SESSION_ID — see header).
--
-- Upsert, not append: calling this again for the same session (the agent
-- corrects itself, or the user changes their mind mid-session) replaces
-- rather than accumulates — same reasoning as Documents.setDocumentSummary,
-- a stale second entry for one key would make lookup ambiguous.
-- ---------------------------------------------------------------------------

setSessionProject : SessionId → ProjectName → SessionProjectStore → SessionProjectStore
setSessionProject sid proj store = (sid , proj) ∷ removeSession sid store

-- ---------------------------------------------------------------------------
-- getSessionProject: lookup. Called from `hook prompt`/`hook pretooluse`.
--
-- CRITICAL SEMANTIC: absence (`nothing`) means "the agent hasn't declared a
-- project for this session yet" — the caller MUST fall back to today's
-- unscoped query_relevant call (project = None), never to a guess. This is
-- the whole point of the design: the filter value only ever comes from an
-- explicit answer, so a missing entry degrades to the pre-existing
-- behaviour, not to a wrong one.
-- ---------------------------------------------------------------------------

getSessionProject : SessionId → SessionProjectStore → Maybe ProjectName
getSessionProject sid []       = nothing
getSessionProject sid (e ∷ es) with matchesSession sid e
... | true  = just (proj₂ e)
... | false = getSessionProject sid es

-- ---------------------------------------------------------------------------
-- AT-MOST-ONE-ENTRY-PER-SESSION INVARIANT and the upsert round-trip
-- (getSessionProject sid (setSessionProject sid proj store) ≡ just proj)
-- are STATED, not proved from types — same status as Documents.agda's own
-- at-most-one-summary invariant and the file-level CONSISTENCY INVARIANT.
-- Both follow immediately from removeSession's definition (it strips every
-- prior entry for `sid` before the new one is prepended) but a full String-
-- decidable-equality proof is more machinery than this module's value
-- warrants; removeSession-smaller above already gives the load-bearing size
-- guarantee (upsert can only shrink-then-grow-by-one, never leak entries).
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- MCP / CLI interface notes
-- ---------------------------------------------------------------------------
--
-- mimir hook set-project NAME    [new, issue #9]
--   Agent-invoked via Bash, NOT wired into settings.json as a Claude Code
--   hook (there is no hook event for "the agent decided something mid-
--   conversation"). Reads $CLAUDE_CODE_SESSION_ID from its own process
--   environment (see header for why this differs from the other hook
--   subcommands). Writes /tmp/mimir-session-project-<sid>, upsert semantics.
--   No stdout on success; exits 0. Never blocks anything (same fail-open
--   posture as hook prompt/pretooluse).
--
-- mimir hook prompt / mimir hook pretooluse    [EXTENDED, issue #9]
--   Now also read session_id from their existing stdin JSON and check
--   /tmp/mimir-session-project-<sid>. If present, pass Some(project) to
--   query_relevant (using list_beliefs_by_project's existing
--   `project = $p OR project IS NULL` semantics — untagged/global beliefs
--   still surface). If absent, unchanged: project = None, today's behaviour.
--   Never fabricate a value here — see getSessionProject's semantic note.
--
-- Prompt-level change (SKILL.md/CLAUDE.md, not this spec): near session
-- start, ask the user which project this session is about (or state a
-- confident guess and let them correct it), then call `mimir hook
-- set-project`. Mid-session, if a returned belief looks like it belongs to
-- a different project than the declared one, surface that suspicion and
-- offer to switch — this is the existing "reconcile the set" / disposition
-- discipline (SKILL.md), not new machinery.
--
-- NOT in scope for this module: `mimir hook stop`'s own project scoping
-- (infer_project_from_cwd) is a separate, lower-risk mechanism (a missed/
-- false Working-belief block, not silently hidden context) and is left as
-- is — a future issue could migrate it to this same side channel for
-- consistency, but that is not required for #9.
-- ---------------------------------------------------------------------------

{-# OPTIONS --safe #-}
-- Owned MCP child lifecycle and the client-wide request counter.
-- Creating the client starts a separate process group; dropping it queries
-- the owned child's current ID before killing the group and direct child.
module Mimir.JudgeMcpLifecycle where

open import Data.Bool using (Bool; true)
open import Data.List using (List; []; _∷_; _++_; length; drop)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _≤_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.UnixPath as Path
import Mimir.StandardLibrary as Conversion
import Mimir.McpClientTransport as Transport
import Mimir.McpClientRequest as Request
import Mimir.StructuredValue as V
import Mimir.Effects as Effects

record Command : Set where
  constructor command
  field executable : Text; arguments : List Text; mimirConfig : Path.Path
        pipedStdin pipedStdout pipedStderr killOnDrop ownProcessGroup : Bool

prepare : Text → List Text → Path.Path → Command
prepare program arguments config = command program arguments config true true true true true

data Stream : Set where stdin stdout stderr : Stream
record Child : Set where constructor child; field handle : ℕ
record Client : Set where
  constructor client
  field owner : Child; input output errorPipe : ℕ; nextID : ℕ

data Effect : Set where
  spawn : Command → Effect
  takePipe : Child → Stream → Effect
  currentChildID startKill : Child → Effect
  killGroup : ℕ → Effect
  captureStderr : ℕ → Effect

Reply : Effect → Set
Reply (spawn _) = Text ⊎ Child
Reply (takePipe _ _) = Text ⊎ ℕ
Reply (currentChildID _) = Maybe ℕ
Reply (startKill _) = Text ⊎ ⊤
Reply (killGroup _) = Text ⊎ ⊤
Reply (captureStderr _) = ⊤
open Effects.Protocol Effect Reply public

dropChild : Child → Script ⊤
dropChild owned = ask (currentChildID owned) λ where
  nothing → ask (startKill owned) (λ _ → done tt)
  (just pid) → ask (killGroup pid) (λ _ → ask (startKill owned) (λ _ → done tt))

dropClient : Client → Script ⊤
dropClient owned = dropChild (Client.owner owned)

-- Before all pipes are installed, the Client destructor does not exist yet;
-- tokio Child::kill_on_drop still owns and terminates the direct child.
pipeFailure : Child → Text → Script (Text ⊎ Client)
pipeFailure owned error = ask (startKill owned) (λ _ → done (inj₁ error))

pipes : Child → Script (Text ⊎ Client)
pipes owned = ask (takePipe owned stdin) λ where
  (inj₁ error) → pipeFailure owned error
  (inj₂ input) → ask (takePipe owned stdout) λ where
    (inj₁ error) → pipeFailure owned error
    (inj₂ output) → ask (takePipe owned stderr) λ where
      (inj₁ error) → pipeFailure owned error
      (inj₂ errorPipe) → ask (captureStderr errorPipe) (λ _ → done (inj₂ (client owned input output errorPipe 1)))

start : Text → List Text → Path.Path → Script (Text ⊎ Client)
start program arguments config = ask (spawn (prepare program arguments config)) λ where
  (inj₁ error) → done (inj₁ error)
  (inj₂ owned) → pipes owned

-- Cancellation can precede construction of Client. Derive ownership from
-- the actual startup prefix rather than inventing a complete client value.
data Ownership : Set where
  absent : Ownership
  installing connected : Child → Ownership

ownerAfter : Ownership → List Event → Ownership
ownerAfter owner [] = owner
ownerAfter owner ((spawn request , inj₂ ownedChild) ∷ rest) = ownerAfter (installing ownedChild) rest
ownerAfter (installing ownedChild) ((captureStderr pipe , tt) ∷ rest) = ownerAfter (connected ownedChild) rest
ownerAfter owner ((startKill ownedChild , reply) ∷ rest) = ownerAfter absent rest
ownerAfter owner (_ ∷ rest) = ownerAfter owner rest

cancelOwned : Ownership → Script ⊤
cancelOwned absent = done tt
cancelOwned (installing ownedChild) = ask (startKill ownedChild) (λ _ → done tt)
cancelOwned (connected ownedChild) = dropChild ownedChild

cancelBeforeSpawnHasNoEffects : ∀ events → Runs (cancelOwned absent) events tt → events ≡ []
cancelBeforeSpawnHasNoEffects .[] (returned tt) = refl

cancelInstallingUsesChildGuard : ∀ ownedChild events → Runs (cancelOwned (installing ownedChild)) events tt →
  Data.Product.Σ (Reply (startKill ownedChild)) (λ reply → events ≡ (startKill ownedChild , reply) ∷ [])
cancelInstallingUsesChildGuard ownedChild events (replied _ _ reply (returned tt)) = reply , refl

data StderrState : Set where reading closed : List Byte → StderrState
data StderrInput : Set where bytes : List Byte → StderrInput; eof failure : StderrInput

retain : List Byte → List Byte → List Byte
retain previous next = drop (length combined ∸ 4096) combined
  where combined = previous ++ next

data StderrStep : StderrState → StderrInput → StderrState → Set where
  received : ∀ previous next → 1 ≤ length next → length next ≤ 1024 →
    StderrStep (reading previous) (bytes next) (reading (retain previous next))
  ended : ∀ previous → StderrStep (reading previous) eof (closed previous)
  failed : ∀ previous → StderrStep (reading previous) failure (closed previous)

module Calls (conversion : Conversion.Contract) (diagnostics : Transport.Diagnostics conversion) where
  module T = Transport conversion
  module R = Request conversion
  data Outcome : Set where overflow : Outcome; response : R.Outcome → Outcome

  data Call (before : Client) (method : Text) (params : V.Value) :
    List T.E.Event → Client → Outcome → Set where
    full : 18446744073709551615 ≤ Client.nextID before → Call before method params [] before overflow
    exchanged : ∀ events result → Client.nextID before ≤ 18446744073709551614 →
      T.With.Pending.Runs diagnostics (Client.nextID before)
        (T.With.Pending.start diagnostics (Client.nextID before) method params) events result →
      Call before method params events (record before { nextID = suc (Client.nextID before) }) (response result)

-- Projection used when composing scoped calls from independent protocols.
-- A receipt retains the actual request ID of its transport.
data Issued : Set where
  issued overflowRejected : ℕ → Issued

data Chain : Maybe Client → List Issued → Maybe Client → Set where
  empty : ∀ client → Chain client [] client
  next : ∀ client calls after → Client.nextID client ≤ 18446744073709551614 →
    Chain (just (record client { nextID = suc (Client.nextID client) })) calls after →
    Chain (just client) (issued (Client.nextID client) ∷ calls) after
  full : ∀ client calls after → 18446744073709551615 ≤ Client.nextID client →
    Chain (just client) calls after →
    Chain (just client) (overflowRejected (Client.nextID client) ∷ calls) after

ownerPreserved : ∀ {before calls after} → Chain before calls after →
  Data.Maybe.map Client.owner before ≡ Data.Maybe.map Client.owner after
ownerPreserved (empty owned) = refl
ownerPreserved (next owned calls after bounded execution) = ownerPreserved execution
ownerPreserved (full owned calls after bounded execution) = ownerPreserved execution

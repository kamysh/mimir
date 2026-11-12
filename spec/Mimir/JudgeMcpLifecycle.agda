{-# OPTIONS --safe #-}
-- Owned MCP child lifecycle and local request IDs.
-- Stopping a client requires confirmation that its owned work has stopped.
module Mimir.JudgeMcpLifecycle where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (≡-dec)
open import Data.Char using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.UnixPath as Path
import Mimir.StandardLibrary as Conversion
import Mimir.McpClientTransport as Transport
import Mimir.McpClientRequest as Request
import Mimir.StructuredValue as V
import Mimir.Effects as Effects

_≟Text_ = ≡-dec _≟_

record Command : Set where
  constructor command
  field executable : Text; arguments : List Text; mimirConfig : Path.Path

prepare : Text → List Text → Path.Path → Command
prepare program arguments config = command program arguments config

data Stream : Set where stdin stdout stderr : Stream
record Child : Set where constructor child; field handle : Text
record Client : Set where
  constructor client
  field owner : Child; input output errorPipe : Text

data Effect : Set where
  spawn : Command → Effect
  -- Local random hexadecimal text for a temporary transport exchange.
  randomHexID : Effect
  takePipe : Child → Stream → Effect
  stopOwned : Child → Effect
  captureStderr : Text → Effect

Reply : Effect → Set
Reply (spawn _) = Text ⊎ Child
-- A request that is not a durable database identity uses a local random
-- hexadecimal string for transport correlation.
Reply randomHexID = Text ⊎ Text
Reply (takePipe _ _) = Text ⊎ Text
-- Success confirms that all work owned by the child, including embedding,
-- has stopped. A request to stop is not itself a successful receipt.
Reply (stopOwned _) = ⊤
Reply (captureStderr _) = ⊤
open Effects.Protocol Effect Reply public

dropChild : Child → Script (Text ⊎ ⊤)
dropChild owned = ask (stopOwned owned) (λ _ → done (inj₂ tt))

dropClient : Client → Script (Text ⊎ ⊤)
dropClient owned = dropChild (Client.owner owned)

dropChildConfirmsStop : ∀ owned events → Runs (dropChild owned) events (inj₂ tt) →
  Data.Product.Σ (List Event) (λ prefix →
    events ≡ prefix ++ ((stopOwned owned , tt) ∷ []))
dropChildConfirmsStop owned .((stopOwned owned , tt) ∷ [])
  (replied _ _ tt (returned (inj₂ tt))) = [] , refl

-- On setup failure, stop all owned work before returning the error.
-- A stop request without confirmation cannot complete this operation.
pipeFailure : Child → Text → Script (Text ⊎ Client)
pipeFailure owned error = dropChild owned >>= λ where
  (inj₁ cleanupFailure) → done (inj₁ cleanupFailure)
  (inj₂ tt) → done (inj₁ error)

pipes : Child → Script (Text ⊎ Client)
pipes owned = ask (takePipe owned stdin) λ where
  (inj₁ error) → pipeFailure owned error
  (inj₂ input) → ask (takePipe owned stdout) λ where
    (inj₁ error) → pipeFailure owned error
    (inj₂ output) → ask (takePipe owned stderr) λ where
      (inj₁ error) → pipeFailure owned error
      (inj₂ errorPipe) → ask (captureStderr errorPipe) (λ _ → done (inj₂ (client owned input output errorPipe)))

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
ownerAfter (installing owned) ((stopOwned stoppedChild , tt) ∷ rest)
  with Child.handle owned ≟Text Child.handle stoppedChild
... | yes _ = ownerAfter absent rest
... | no _ = ownerAfter (installing owned) rest
ownerAfter (connected owned) ((stopOwned stoppedChild , tt) ∷ rest)
  with Child.handle owned ≟Text Child.handle stoppedChild
... | yes _ = ownerAfter absent rest
... | no _ = ownerAfter (connected owned) rest
ownerAfter owner (_ ∷ rest) = ownerAfter owner rest

cancelOwned : Ownership → Script (Text ⊎ ⊤)
cancelOwned absent = done (inj₂ tt)
cancelOwned (installing ownedChild) = dropChild ownedChild
cancelOwned (connected ownedChild) = dropChild ownedChild

cancelBeforeSpawnHasNoEffects : ∀ events → Runs (cancelOwned absent) events (inj₂ tt) → events ≡ []
cancelBeforeSpawnHasNoEffects .[] (returned (inj₂ tt)) = refl

cancelInstallingConfirmsStop : ∀ ownedChild events → Runs (cancelOwned (installing ownedChild)) events (inj₂ tt) →
  Data.Product.Σ (List Event) (λ prefix → events ≡ prefix ++ ((stopOwned ownedChild , tt) ∷ []))
cancelInstallingConfirmsStop ownedChild events = dropChildConfirmsStop ownedChild events

-- Successful cancellation clears ownership only after the stop receipt.
cancelOwnedReleases : ∀ owner events → Runs (cancelOwned owner) events (inj₂ tt) →
  ownerAfter owner events ≡ absent
cancelOwnedReleases absent .[] (returned (inj₂ tt)) = refl
cancelOwnedReleases (installing ownedChild) events
  (replied _ _ tt (returned (inj₂ tt)))
  with Child.handle ownedChild ≟Text Child.handle ownedChild
... | yes _ = refl
... | no unequal = ⊥-elim (unequal refl)
cancelOwnedReleases (connected ownedChild) events
  (replied _ _ tt (returned (inj₂ tt)))
  with Child.handle ownedChild ≟Text Child.handle ownedChild
... | yes _ = refl
... | no unequal = ⊥-elim (unequal refl)

-- This holds for every completed cancellation, including setup failures;
-- there is no alternative return that leaves the owned child running.
cancelCompletionConfirmsStop : ∀ owner events result → Runs (cancelOwned owner) events result →
  result ≡ inj₂ tt × ownerAfter owner events ≡ absent
cancelCompletionConfirmsStop absent .[] .(inj₂ tt) (returned _) = refl , refl
cancelCompletionConfirmsStop (installing ownedChild) events .(inj₂ tt)
  execution@(replied _ _ tt (returned _)) = refl , cancelOwnedReleases (installing ownedChild) events execution
cancelCompletionConfirmsStop (connected ownedChild) events .(inj₂ tt)
  execution@(replied _ _ tt (returned _)) = refl , cancelOwnedReleases (connected ownedChild) events execution

module Calls (conversion : Conversion.Contract) (diagnostics : Transport.Diagnostics conversion) where
  module T = Transport conversion
  module R = Request conversion
  data Outcome : Set where idUnavailable : Text → Outcome; response : R.Outcome → Outcome

  data Call (before : Client) (method : Text) (params : V.Value) :
    List T.E.Event → Client → Outcome → Set where
    idFailed : ∀ allocationEvents failure → Runs (ask randomHexID done) allocationEvents (inj₁ failure) →
      Call before method params [] before (idUnavailable failure)
    exchanged : ∀ requestID allocationEvents events result →
      Runs (ask randomHexID done) allocationEvents (inj₂ requestID) →
      T.With.Pending.Runs diagnostics requestID
        (T.With.Pending.start diagnostics requestID method params) events result →
      Call before method params events before (response result)

-- Projection used when composing scoped calls from independent protocols.
-- A receipt retains the actual request ID of its transport.
data Issued : Set where
  issued : Text → Issued
  allocationUnavailable : Issued
  stoppedClient : (client : Client) → (events : List Event) →
    Runs (dropClient client) events (inj₂ tt) → Issued

data Chain : Maybe Client → List Issued → Maybe Client → Set where
  empty : ∀ client → Chain client [] client
  next : ∀ client requestID calls after → Chain (just client) calls after →
    Chain (just client) (issued requestID ∷ calls) after
  unavailable : ∀ client calls after → Chain (just client) calls after →
    Chain (just client) (allocationUnavailable ∷ calls) after
  stopped : ∀ client events proof calls after → Chain nothing calls after →
    Chain (just client) (stoppedClient client events proof ∷ calls) after

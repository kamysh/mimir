{-# OPTIONS --safe #-}
-- Concrete work checkpoints and the destructors demanded when that work is
-- stopped. Ownership comes from the component protocols' actual prefixes.
module Mimir.JudgeOwnedWork where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using (List; []; _∷_; _++_; filterᵇ; map)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.StructuredValue as V
import Mimir.JudgeHarnessAdapter as Harness
import Mimir.JudgeAPIAdapter as API
import Mimir.JudgeConfiguration as Config
import Mimir.ReviewObservation as Observation
import Mimir.JudgeMcpLifecycle as Client
import Mimir.McpClientRequest as Request
import Mimir.JudgeLock as Lock
import Mimir.JudgeWrite as Write
import Mimir.JudgeStateRecords as Records
import Mimir.UnixPath as Path
import Mimir.Effects as Effects
import Mimir.Collections as Collections

module Bound (conversion : Conversion.Contract) (format : Encoding.Formatting) (libraries : Harness.Libraries) where
  private
    module L = Lock.With Path.Path ℕ Text
    module W = Write.With Path.Path ℕ Text
    module FS = W.FS
    module R = Records.Over ℕ
    module H config program selected tools = Harness.Run conversion format libraries config program selected tools
    module A config provider selected tools = API.Run conversion format libraries config provider selected tools
    module Q = Request conversion

  record HeldLock : Set where
    field held : L.Locked
          events : List L.FS.Event
          acquired : L.FS.Runs (L.requestLock held) events (inj₂ (just held))

  module IDs = Collections.Equality ℕ _≟_

  record StartingClient : Set where
    field program : Text; arguments : List Text; configuration : Path.Path
          events : List Client.Event
          residual : Client.Script (Text Data.Sum.⊎ Client.Client)
          prefix : Client.Prefix (Client.start program arguments configuration) events residual

  record ReadyClient : Set where
    field program : Text; arguments : List Text; configuration : Path.Path
          initial : Client.Client
          events : List Client.Event
          started : Client.Runs (Client.start program arguments configuration) events (inj₂ initial)
          calls : List Client.Issued
          current : Client.Client
          chain : Client.Chain (just initial) calls (just current)

  record Resources : Set where
    field ownedClient : Maybe ReadyClient
          locks : List HeldLock
          distinct : IDs.Unique (map (λ held → L.Locked.handle (HeldLock.held held)) locks)

  HasClient : Resources → Set
  HasClient resources = Σ ReadyClient (λ owned → Resources.ownedClient resources ≡ just owned)

  data HasLock : List HeldLock → Set where
    someLock : ∀ first rest → HasLock (first ∷ rest)

  record ToolPoint : Set where
    field ownedClient : ReadyClient
          method : Text; arguments : V.Value
          expected : ℕ
          counter : expected ≡ Client.Client.nextID (ReadyClient.current ownedClient)
          nextCounter : ℕ
          launched : Q.Counter.launch 18446744073709551615 (Client.Client.nextID (ReadyClient.current ownedClient)) method arguments ≡
            Q.Counter.started expected nextCounter (Q.Pending.start expected method arguments)
          events : List Q.E.Event
          state : Q.Pending.State expected
          prefix : Q.Pending.Prefix expected (Q.Pending.start expected method arguments) events state

  -- Close is a synchronous guard, not a background filesystem job. These
  -- are the blocking requests issued by the replacement protocol.
  data FileJob : FS.Operation → Set where
    opening : ∀ path mode → FileJob (FS.openFile path mode)
    writing : ∀ handle bytes → FileJob (FS.writeAll handle bytes)
    syncing : ∀ handle → FileJob (FS.syncAll handle)
    moving : ∀ source target → FileJob (FS.rename source target)
    removing : ∀ path → FileJob (FS.removeFile path)

  data SavePosition : FS.Script W.Outcome → Set where
    between : ∀ residual → SavePosition residual
    awaiting : ∀ (job : ℕ) operation next → FileJob operation → SavePosition (FS.ask operation next)

  record SavingPoint : Set where
    field temporary target directory : Path.Path
          bytes : List Byte
          events : List FS.Event
          residual : FS.Script W.Outcome
          prefix : FS.Prefix (W.replace temporary target directory bytes) events residual
          position : SavePosition residual

  -- Only the one operation already running is joined. Its continuation is
  -- recorded but never run: stopping cannot launch the next normal write.
  settleSave : SavingPoint → FS.Script (SavingPoint × Bool)
  settleSave point with SavingPoint.position point
  ... | between residual = FS.done (point , true)
  ... | awaiting job operation next kind = FS.ask (FS.awaitExisting job operation) λ where
      (inj₁ error) → FS.done (point , false)
      (inj₂ reply) → FS.done (record point
        { events = SavingPoint.events point ++ ((operation , reply) ∷ [])
        ; residual = next reply
        ; prefix = FS.prefixAppend (SavingPoint.prefix point) (FS.replied operation next reply (FS.stopped _))
        ; position = between (next reply) } , true)

  -- Only descriptors actually opened by the interrupted replacement are
  -- closed. Successful closes remove them from the owned set immediately.
  descriptorsAfter : List ℕ → List FS.Event → List ℕ
  descriptorsAfter owned [] = owned
  descriptorsAfter owned ((FS.openFile path mode , inj₂ handle) ∷ events) = descriptorsAfter (handle ∷ owned) events
  descriptorsAfter owned ((FS.close handle , tt) ∷ events) =
    descriptorsAfter (filterᵇ (λ candidate → not (does (candidate ≟ handle))) owned) events
  descriptorsAfter owned (_ ∷ events) = descriptorsAfter owned events

  data Activity : Set where
    startup : Maybe StartingClient → Activity
    harness : ∀ config program selected tools before last → H.Checkpoint config program selected tools before last → Activity
    api : ∀ config provider selected tools before last events point →
      A.Trace config provider selected tools (A.start config provider selected tools before last) events point →
      Activity
    tool : ToolPoint → Activity
    saving : SavingPoint → Activity
    maintenance : Activity -- daily or finalization notification/read work
    waiting : Activity

  data Valid : Activity → Resources → Set where
    booting : ∀ resources → Resources.ownedClient resources ≡ nothing → Valid (startup nothing) resources
    starting : ∀ resources owned → Resources.ownedClient resources ≡ nothing → HasLock (Resources.locks resources) →
      Valid (startup (just owned)) resources
    harnessWork : ∀ resources config program selected tools before last point → HasClient resources → HasLock (Resources.locks resources) →
      Valid (harness config program selected tools before last point) resources
    apiWork : ∀ resources config provider selected tools before last events point execution → HasClient resources → HasLock (Resources.locks resources) →
      Valid (api config provider selected tools before last events point execution) resources
    toolWork : ∀ resources point → Resources.ownedClient resources ≡ just (ToolPoint.ownedClient point) → HasLock (Resources.locks resources) →
      Valid (tool point) resources
    savingWork : ∀ resources point →
      Any (λ held → SavingPoint.directory point ≡ L.Locked.path (HeldLock.held held)) (Resources.locks resources) →
      Valid (saving point) resources
    notifying : ∀ resources → Valid maintenance resources
    betweenBatches : ∀ resources → Resources.ownedClient resources ≡ nothing → Resources.locks resources ≡ [] → Valid waiting resources

  record Work : Set where
    field future : ℕ -- native owned future identity; no generator is specified
          activity : Activity
          resources : Resources
          valid : Valid activity resources
          savedReport : Maybe R.Report

  data Pending : Set where
    none modelResult notificationResult : Pending
    toolResult : ℕ → Text → V.Value → Pending
    fileResult : Path.Path → Pending

  unconfirmed : Activity → Pending
  unconfirmed (startup owned) = none
  unconfirmed (harness config program selected tools before last point) = modelResult
  unconfirmed (api config provider selected tools before last events point execution) = modelResult
  unconfirmed (tool point) = toolResult (ToolPoint.expected point) (ToolPoint.method point) (ToolPoint.arguments point)
  unconfirmed (saving point) = fileResult (SavingPoint.target point)
  unconfirmed maintenance = notificationResult
  unconfirmed waiting = none

  record Stopped : Set where
    constructor stopped
    field savedReport : Maybe R.Report
          pending : Pending

  data Effect : Set where
    startingClient : StartingClient → Effect
    readyClient : ReadyClient → Effect
    lock : HeldLock → Effect
    harness : ∀ config program selected tools before last → H.Checkpoint config program selected tools before last → Effect
    api : ∀ config provider selected tools → A.State config provider selected tools → Effect
    stopSave : SavingPoint → Effect
  Reply : Effect → Set
  Reply effect = ⊤
  module E = Effects.Protocol Effect Reply
  open E using (Script; ask; done; _>>=_)

  clientCleanup : Maybe ReadyClient → Script ⊤
  clientCleanup nothing = done tt
  clientCleanup (just ownedClient) = ask (readyClient ownedClient) done
  locksCleanup : List HeldLock → Script ⊤
  locksCleanup [] = done tt
  locksCleanup (held ∷ remaining) = ask (lock held) (λ _ → locksCleanup remaining)

  cleanupActivity : Activity → Script ⊤
  cleanupActivity (startup nothing) = done tt
  cleanupActivity (startup (just ownedClient)) = ask (startingClient ownedClient) done
  cleanupActivity (harness config program selected tools before last point) = ask (harness config program selected tools before last point) done
  cleanupActivity (api config provider selected tools before last events point execution) = ask (api config provider selected tools point) done
  cleanupActivity (tool point) = done tt
  cleanupActivity (saving point) = ask (stopSave point) done
  cleanupActivity maintenance = done tt
  cleanupActivity waiting = done tt

  cleanupResources : Work → Script ⊤
  cleanupResources work = cleanupActivity (Work.activity work) >>= λ _ →
    clientCleanup (Resources.ownedClient (Work.resources work)) >>= λ _ → locksCleanup (Resources.locks (Work.resources work))

  cleanup : Work → Script Stopped
  cleanup work = cleanupResources work >>= λ _ →
    done (stopped (Work.savedReport work) (unconfirmed (Work.activity work)))

  -- File-future cancellation closes owned descriptors. It does not rename,
  -- remove a possibly published target, or pretend a pending save rolled back.
  closeDescriptors : List ℕ → FS.Script ⊤
  closeDescriptors [] = FS.done tt
  closeDescriptors (handle ∷ remaining) = FS.ask (FS.close handle) (λ _ → closeDescriptors remaining)

  temporaryOwnedAfter : Bool → List FS.Event → Bool
  temporaryOwnedAfter owned [] = owned
  temporaryOwnedAfter owned ((FS.openFile path FS.exclusiveWrite0600NoFollowCloseOnExec , inj₂ handle) ∷ events) =
    temporaryOwnedAfter true events
  temporaryOwnedAfter owned ((FS.rename source target , inj₂ tt) ∷ events) = temporaryOwnedAfter false events
  temporaryOwnedAfter owned ((FS.removeFile path , reply) ∷ events) = temporaryOwnedAfter false events
  temporaryOwnedAfter owned (_ ∷ events) = temporaryOwnedAfter owned events

  creationBefore : ∀ temporary target directory bytes events residual →
    FS.Prefix (W.replace temporary target directory bytes) events residual →
    temporaryOwnedAfter false events ≡ true →
    Σ ℕ (λ handle → Σ (List FS.Event) (λ rest →
      events ≡ (FS.openFile temporary FS.exclusiveWrite0600NoFollowCloseOnExec , inj₂ handle) ∷ rest))
  creationBefore temporary target directory bytes events residual (FS.stopped _) ()
  creationBefore temporary target directory bytes events residual (FS.replied _ _ (inj₁ error) (FS.stopped _)) ()
  creationBefore temporary target directory bytes events residual (FS.replied _ _ (inj₂ handle) remaining) owned = handle , _ , refl

  temporaryCleanup : SavingPoint → Bool → FS.Script ⊤
  temporaryCleanup point certain with temporaryOwnedAfter false (SavingPoint.events point) | not certain
  ... | true | false = FS.ask (FS.removeFile (SavingPoint.temporary point)) (λ _ → FS.done tt)
  ... | _ | _ = FS.done tt

  removalRequiresCreation : ∀ point certain events → FS.Runs (temporaryCleanup point certain) events tt → W.ContainsRemoval events →
    Σ ℕ (λ handle → Σ (List FS.Event) (λ rest →
      SavingPoint.events point ≡
      (FS.openFile (SavingPoint.temporary point) FS.exclusiveWrite0600NoFollowCloseOnExec , inj₂ handle) ∷ rest))
  removalRequiresCreation point certain events execution removed
    with temporaryOwnedAfter false (SavingPoint.events point) in owned | not certain
  ... | true | false = creationBefore (SavingPoint.temporary point) (SavingPoint.target point) (SavingPoint.directory point)
    (SavingPoint.bytes point) (SavingPoint.events point) (SavingPoint.residual point) (SavingPoint.prefix point) owned
  ... | false | pending with execution
  ...   | FS.returned tt with removed
  ...     | ()
  removalRequiresCreation point certain events execution removed | true | true with execution
  ... | FS.returned tt with removed
  ...   | ()

  cancelSave : SavingPoint → FS.Script ⊤
  cancelSave point = settleSave point FS.>>= λ { (settled , certain) →
    closeDescriptors (descriptorsAfter [] (SavingPoint.events settled)) FS.>>= λ _ → temporaryCleanup settled certain }

  unavailableResultCannotRemove : ∀ point events → FS.Runs (temporaryCleanup point false) events tt → events ≡ []
  unavailableResultCannotRemove point events execution with temporaryOwnedAfter false (SavingPoint.events point)
  ... | false with execution
  ... | FS.returned tt = refl
  unavailableResultCannotRemove point events execution | true with execution
  ... | FS.returned tt = refl

  data Receipt : (effect : Effect) → Reply effect → Set where
    startupDropped : ∀ ownedClient events → Client.Runs
      (Client.cancelOwned (Client.ownerAfter Client.absent (StartingClient.events ownedClient))) events tt →
      Receipt (startingClient ownedClient) tt
    clientDropped : ∀ ownedClient events → Client.Runs
      (Client.dropClient (ReadyClient.current ownedClient)) events tt → Receipt (readyClient ownedClient) tt
    lockReleased : ∀ held events → L.FS.Runs (L.release (HeldLock.held held)) events tt → Receipt (lock held) tt
    harnessDropped : ∀ config program selected tools before last point events →
      H.P.Runs config program selected tools (H.cancelCheckpoint config program selected tools point) events tt →
      Receipt (harness config program selected tools before last point) tt
    apiDropped : ∀ config provider selected tools point events →
      A.P.Runs config provider selected tools (A.cancel config provider selected tools point) events tt →
      Receipt (api config provider selected tools point) tt
    saveDropped : ∀ point events → FS.Runs (cancelSave point) events tt →
      Receipt (stopSave point) tt

  data Runs {Result : Set} : Script Result → List E.Event → Result → Set where
    returned : ∀ result → Runs (done result) [] result
    replied : ∀ effect continuation reply events result → Receipt effect reply → Runs (continuation reply) events result →
      Runs (ask effect continuation) ((effect , reply) ∷ events) result

  locksCleanupExact : ∀ heldLocks events → Runs (locksCleanup heldLocks) events tt →
    events ≡ map (λ held → lock held , tt) heldLocks
  locksCleanupExact [] events (returned tt) = refl
  locksCleanupExact (held ∷ remaining) events (replied _ _ tt rest _ receipt execution) =
    cong ((lock held , tt) ∷_) (locksCleanupExact remaining rest execution)

  constantResult : ∀ {A B : Set} (program : Script A) (value : B) events result →
    Runs (program >>= λ _ → done value) events result → result ≡ value
  constantResult (done initial) value events result (returned _) = refl
  constantResult (ask effect next) value events result (replied _ _ reply rest _ receipt execution) =
    constantResult (next reply) value rest result execution

  cleanupPreservesReport : ∀ work events result → Runs (cleanup work) events result → Stopped.savedReport result ≡ Work.savedReport work
  cleanupPreservesReport work events result execution rewrite constantResult (cleanupResources work) _ events result execution = refl

  cleanupRetainsUncertainty : ∀ work events result → Runs (cleanup work) events result →
    Stopped.pending result ≡ unconfirmed (Work.activity work)
  cleanupRetainsUncertainty work events result execution rewrite constantResult (cleanupResources work) _ events result execution = refl

  waitingNeedsNoResourceActions : ∀ work → Work.activity work ≡ waiting → ∀ events result →
    Runs (cleanup work) events result → events ≡ []
  waitingNeedsNoResourceActions work paused events result execution rewrite paused with Work.valid work
  ... | betweenBatches resources noClient noLocks rewrite noClient | noLocks with execution
  ... | returned _ = refl

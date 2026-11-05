{-# OPTIONS --safe #-}
-- Replacement of one locked private state file. Creation failure does not
-- authorize removal of a pre-existing temporary path. Successful rename and
-- successful directory sync are separate observations.
module Mimir.AtomicFile where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Effects

data Operation : Set where
  createExclusive0600NoFollow writeAll syncFile renameTarget syncDirectory removeOwnedTemp : Operation
data IOReceipt : Set where ok failed : IOReceipt
data Failure : Set where create write fileSync rename directorySync : Failure
data Result : Set where
  committed : Result
  unchanged : Failure → Result
  durabilityUnknown : Result

open Protocol Operation (λ _ → IOReceipt) public

cleanup : Result → Script Result
cleanup result = ask removeOwnedTemp (λ _ → done result)

afterRename : Script Result
afterRename = ask syncDirectory λ where
  ok → done committed
  failed → done durabilityUnknown

renameFile : Script Result
renameFile = ask renameTarget λ where
  ok → afterRename
  failed → cleanup (unchanged rename)

syncTemporary : Script Result
syncTemporary = ask syncFile λ where
  ok → renameFile
  failed → cleanup (unchanged fileSync)

writeTemporary : Script Result
writeTemporary = ask writeAll λ where
  ok → syncTemporary
  failed → cleanup (unchanged write)

replace : Script Result
replace = ask createExclusive0600NoFollow λ where
  ok → writeTemporary
  failed → done (unchanged create)

-- The target has already been renamed when directory sync fails. No claim
-- that the old value survived is emitted, and no temporary file remains owned.
directoryFailureIsUncertain : ∀ events result →
  Runs afterRename ((syncDirectory , failed) ∷ events) result →
  events ≡ [] × result ≡ durabilityUnknown
directoryFailureIsUncertain events result (replied _ _ _ (returned _)) = refl , refl

createFailureCannotRemoveAnotherFile : ∀ events result →
  Runs replace ((createExclusive0600NoFollow , failed) ∷ events) result →
  events ≡ [] × result ≡ unchanged create
createFailureCannotRemoveAnotherFile events result (replied _ _ _ (returned _)) = refl , refl

data Contains (operation : Operation) : List Event → Set where
  here : ∀ reply tail → Contains operation ((operation , reply) ∷ tail)
  later : ∀ event {tail} → Contains operation tail → Contains operation (event ∷ tail)

cleanupRequiresCreation : ∀ events result → Runs replace events result →
  Contains removeOwnedTemp events →
  Contains createExclusive0600NoFollow events
cleanupRequiresCreation events result (replied _ _ ok rest) contains = here ok _
cleanupRequiresCreation events result (replied _ _ failed (returned _)) (later _ ())

record SuccessfulCreation (events : List Event) : Set where
  constructor created
  field tail : List Event; exact : events ≡ (createExclusive0600NoFollow , ok) ∷ tail

cleanupRequiresOwnedTemp : ∀ events result → Runs replace events result →
  Contains removeOwnedTemp events → SuccessfulCreation events
cleanupRequiresOwnedTemp events result (replied _ _ ok rest) contains = created _ refl
cleanupRequiresOwnedTemp events result (replied _ _ failed (returned _)) (later _ ())

-- A complete successful replacement has all five successful receipts, in
-- order. No cleanup or write attempt substitutes for a sync acknowledgement.
successTrace : List Event
successTrace = (createExclusive0600NoFollow , ok) ∷ (writeAll , ok) ∷
  (syncFile , ok) ∷ (renameTarget , ok) ∷ (syncDirectory , ok) ∷ []

committedRequiresEveryReceipt : ∀ events → Runs replace events committed → events ≡ successTrace
committedRequiresEveryReceipt events
  (replied _ _ ok (replied _ _ ok (replied _ _ ok
    (replied _ _ ok (replied _ _ ok (returned _)))))) = refl
committedRequiresEveryReceipt events (replied _ _ ok (replied _ _ failed (replied _ _ _ ())))
committedRequiresEveryReceipt events (replied _ _ ok (replied _ _ ok (replied _ _ failed (replied _ _ _ ()))))
committedRequiresEveryReceipt events (replied _ _ ok (replied _ _ ok (replied _ _ ok (replied _ _ failed (replied _ _ _ ())))))

-- Abstract storage semantics for the acknowledged operations, separately from
-- the control protocol above. Other files are deliberately an arbitrary frame.
module Storage (Payload Frame : Set) where
  record World : Set where
    constructor world
    field visible durable : Payload; others : Frame

  renameValue : Payload → World → World
  renameValue value before = record before { visible = value }

  syncValue : World → World
  syncValue before = record before { durable = World.visible before }

  renamePreservesFrame : ∀ value before → World.others (renameValue value before) ≡ World.others before
  renamePreservesFrame value before = refl

  syncPreservesFrame : ∀ before → World.others (syncValue before) ≡ World.others before
  syncPreservesFrame before = refl

  durableAfterBothReceipts : ∀ value before →
    World.durable (syncValue (renameValue value before)) ≡ value
  durableAfterBothReceipts value before = refl

  -- Crash recovery before the directory receipt may observe either mapping.
  -- This is explicit nondeterminism, not a postulate about OS reliability.
  data Recovered (before : World) : Payload → Set where
    previous : Recovered before (World.durable before)
    renamed : Recovered before (World.visible before)

  acknowledgedRecovery : ∀ value before recovered →
    Recovered (syncValue (renameValue value before)) recovered → recovered ≡ value
  acknowledgedRecovery value before recovered previous = refl
  acknowledgedRecovery value before recovered renamed = refl

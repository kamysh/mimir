{-# OPTIONS --safe #-}
-- Digest cursor protocol. The public day syntax is YYYY-MM-DD shaped ASCII,
-- as currently specified by the application; it is not calendar validation.
module Mimir.DigestDelivery where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; Bounded; bounded?)
open import Mimir.DecimalLexer using (DigitAt; classify)
open import Mimir.TextOrder
import Mimir.Saturating as Sat
open import Mimir.Effects
open import Mimir.NotificationDelivery using (WriteReceipt; durable; refused; uncertain; MailReceipt; accepted; retryable; authRequired; unavailable; BuildReceipt; built; invalid)

data Slot : Set where digit dash : Slot
Fits : Slot → Char → Set
Fits digit c = DigitAt c
Fits dash c = c ≡ '-'

fits? : ∀ slot c → Dec (Fits slot c)
fits? digit c = classify c
fits? dash c = c ≟ '-'

data Matches : List Slot → Text → Set where
  end : Matches [] []
  next : ∀ {s slots c chars} → Fits s c → Matches slots chars → Matches (s ∷ slots) (c ∷ chars)

matches? : ∀ slots chars → Dec (Matches slots chars)
matches? [] [] = yes end
matches? [] (_ ∷ _) = no (λ ())
matches? (_ ∷ _) [] = no (λ ())
matches? (s ∷ slots) (c ∷ chars) with fits? s c | matches? slots chars
... | yes fit | yes rest = yes (next fit rest)
... | no notFit | _ = no (λ { (next fit rest) → notFit fit })
... | _ | no notRest = no (λ { (next fit rest) → notRest rest })

daySlots : List Slot
daySlots = digit ∷ digit ∷ digit ∷ digit ∷ dash ∷ digit ∷ digit ∷ dash ∷ digit ∷ digit ∷ []

record Digest : Set where
  constructor digest
  field throughDay body : Text

DigestValid : Digest → Set
DigestValid d = Matches daySlots (Digest.throughDay d) × Bounded 262144 (Digest.body d)

digestValid? : ∀ d → Dec (DigestValid d)
digestValid? d = matches? daySlots (Digest.throughDay d) ×-dec bounded? 262144 (Digest.body d)

record Cursor : Set where
  constructor cursor
  field throughDay : Maybe Text; nextDue : ℕ; lastAttemptFailed : Bool

Covered : Cursor → Text → Set
Covered (cursor nothing due failed) requested = ⊥
Covered (cursor (just previous) due failed) requested = requested ≤Text previous

covered? : ∀ before requested → Dec (Covered before requested)
covered? (cursor nothing due failed) requested = no (λ ())
covered? (cursor (just previous) due failed) requested = requested ≤Text? previous

Forward : Cursor → Text → Set
Forward (cursor nothing due failed) requested = ⊤
Forward (cursor (just previous) due failed) requested = previous ≤Text requested

notCoveredAdvances : ∀ before requested → ¬ Covered before requested → Forward before requested
notCoveredAdvances (cursor nothing due failed) requested notCovered = tt
notCoveredAdvances (cursor (just previous) due failed) requested notCovered =
  notReverseImpliesForward previous requested notCovered

reserve : ℕ → ℕ → Cursor → Cursor
reserve maximum now before = record before { nextDue = Sat.add maximum now 3600 ; lastAttemptFailed = true }

advance : Digest → Cursor
advance d = cursor (just (Digest.throughDay d)) 0 false

data Result : Set where disabled notNeeded retryPending sent invalidDigest invalidMessage storageFailed : Result
data Effect : Set where
  buildMessage sendMessage : Digest → Effect
  saveCursor : Cursor → Effect

Reply : Effect → Set
Reply (buildMessage _) = BuildReceipt
Reply (sendMessage _) = MailReceipt
Reply (saveCursor _) = WriteReceipt
open Protocol Effect Reply public

save : Cursor → Script Result → Script Result
save c after = ask (saveCursor c) λ where
  durable → after
  refused → done storageFailed
  uncertain → done storageFailed

afterMail : Digest → MailReceipt → Script Result
afterMail d accepted = save (advance d) (done sent)
afterMail d retryable = done retryPending
afterMail d authRequired = done retryPending
afterMail d unavailable = done retryPending

eligible : ℕ → ℕ → Cursor → Digest → Script Result
eligible maximum now before d = ask (buildMessage d) λ where
  invalid → done invalidMessage
  built → save (reserve maximum now before) (ask (sendMessage d) (afterMail d))

afterValidation : ℕ → ℕ → Cursor → Digest → Script Result
afterValidation maximum now before d with covered? before (Digest.throughDay d)
... | yes _ = done notNeeded
... | no _ with Cursor.nextDue before ≤? now
...   | no _ = done retryPending
...   | yes _ = eligible maximum now before d

send : Bool → ℕ → ℕ → Cursor → Digest → Script Result
send false maximum now before d = done disabled
send true maximum now before d with digestValid? d
... | no _ = done invalidDigest
... | yes _ = afterValidation maximum now before d

reservationPreservesCursor : ∀ maximum now before →
  Cursor.throughDay (reserve maximum now before) ≡ Cursor.throughDay before
reservationPreservesCursor maximum now before = refl

reservationBounded : ∀ maximum now before → Cursor.nextDue (reserve maximum now before) ≤ maximum
reservationBounded maximum now before = Sat.bounded maximum now 3600

data SentEvidence (maximum now : ℕ) (before : Cursor) (d : Digest) : List Event → Set where
  sentWithReceipts : SentEvidence maximum now before d
    ((buildMessage d , built) ∷ (saveCursor (reserve maximum now before) , durable) ∷
      (sendMessage d , accepted) ∷ (saveCursor (advance d) , durable) ∷ [])

sentOnlyAfterAcceptance : ∀ maximum now before d events → Runs (eligible maximum now before d) events sent →
  SentEvidence maximum now before d events
sentOnlyAfterAcceptance maximum now before d events
  (replied _ _ built (replied _ _ durable (replied _ _ accepted (replied _ _ durable (returned _))))) = sentWithReceipts

sendAdvancesMonotonically : ∀ maximum now before d events →
  Runs (afterValidation maximum now before d) events sent → Forward before (Digest.throughDay d)
sendAdvancesMonotonically maximum now before d events run with covered? before (Digest.throughDay d)
... | yes covered with run
...   | ()
sendAdvancesMonotonically maximum now before d events run | no notCovered =
  notCoveredAdvances before (Digest.throughDay d) notCovered

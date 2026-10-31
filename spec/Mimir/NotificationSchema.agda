{-# OPTIONS --safe #-}
module Mimir.NotificationSchema where

open import Data.Char using (Char; toℕ; _≟_)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable.Core using (_×-dec_; _⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text
open import Mimir.CharacterRules using (Control; control?; NoControls; noControls?; TokenValid; tokenValid?)
open import Mimir.Collections using (all?; negate)
open import Mimir.NotificationIncident using (Event; Status; failure; progress; recovery)
open import Mimir.Validation

AsciiAlphaNumeric : Char → Set
AsciiAlphaNumeric c = (48 ≤ toℕ c × toℕ c ≤ 57) ⊎
  ((65 ≤ toℕ c × toℕ c ≤ 90) ⊎ (97 ≤ toℕ c × toℕ c ≤ 122))

asciiAlphaNumeric? : ∀ c → Dec (AsciiAlphaNumeric c)
asciiAlphaNumeric? c = ((48 ≤? toℕ c) ×-dec (toℕ c ≤? 57)) ⊎-dec
  (((65 ≤? toℕ c) ×-dec (toℕ c ≤? 90)) ⊎-dec ((97 ≤? toℕ c) ×-dec (toℕ c ≤? 122)))

IdentifierChar : Char → Set
IdentifierChar c = AsciiAlphaNumeric c ⊎ (c ≡ '-' ⊎ (c ≡ '_' ⊎ c ≡ '.'))

identifierChar? : ∀ c → Dec (IdentifierChar c)
identifierChar? c = asciiAlphaNumeric? c ⊎-dec ((c ≟ '-') ⊎-dec ((c ≟ '_') ⊎-dec (c ≟ '.')))

Identifier : Text → Set
Identifier text = Nonempty text × (Bounded 64 text × All IdentifierChar text)

identifier? : ∀ text → Dec (Identifier text)
identifier? text = nonempty? text ×-dec (bounded? 64 text ×-dec all? identifierChar? text)

Summary : Text → Set
Summary text = Nonblank text × (Bounded 160 text × NoControls text)

summary? : ∀ text → Dec (Summary text)
summary? text = nonblank? text ×-dec (bounded? 160 text ×-dec noControls? text)

DetailChar : Char → Set
DetailChar c = c ≡ '\n' ⊎ (Control c → ⊥)

detailChar? : ∀ c → Dec (DetailChar c)
detailChar? c = (c ≟ '\n') ⊎-dec negate (control? c)

Details : Maybe Text → Set
Details nothing = ⊤
Details (just text) = Nonempty text × (Bounded 2048 text × All DetailChar text)

checkDetails : ∀ details → Checked (Details details)
checkDetails nothing = accepted tt
checkDetails (just text) = combine
  (check (fault [] emptyText "notification details must not be empty") (nonempty? text))
  (combine (check (fault [] textTooLong "notification details exceed 2048 UTF-8 bytes") (bounded? 2048 text))
    (check (fault [] malformedInput "notification details contain a control other than LF") (all? detailChar? text)))

StatusValid : Status → Set
StatusValid (failure code summary) = Identifier code × Summary summary
StatusValid progress = ⊤
StatusValid recovery = ⊤

checkStatus : ∀ status → Checked (StatusValid status)
checkStatus (failure code summary) = combine
  (at (key "code") (check (fault [] malformedInput "invalid notification code") (identifier? code)))
  (at (key "summary") (check (fault [] malformedInput "invalid notification summary") (summary? summary)))
checkStatus progress = accepted tt
checkStatus recovery = accepted tt

EventValid : Event → Set
EventValid e = Identifier (Event.source e) × (TokenValid 128 (Event.incidentKey e) ×
  (StatusValid (Event.status e) × Details (Event.details e)))

checkEvent : ∀ e → Checked (EventValid e)
checkEvent e = combine
  (at (key "source") (check (fault [] malformedInput "invalid notification source") (identifier? (Event.source e))))
  (combine (at (key "incident_key") (check (fault [] malformedInput "invalid notification incident key")
      (tokenValid? 128 (Event.incidentKey e))))
    (combine (at (key "status") (checkStatus (Event.status e)))
      (at (key "details") (checkDetails (Event.details e)))))

validEventNeverRejected : ∀ e → EventValid e → reported (checkEvent e) ≡ []
validEventNeverRejected e = noFalseRejection (checkEvent e)

{-# OPTIONS --safe #-}
-- Client-side JSON-RPC envelope semantics after syntax decoding. Duplicate
-- object keys and malformed JSON are handled by the wire decoder, not inferred
-- away here. Notification processing is bounded within each pending request.
module Mimir.RpcReply where

open import Data.Char using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _<?_) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)

data Identifier : Set where
  absent null invalid : Identifier
  integer : ℕ → Identifier
  string : Text → Identifier

data Failure : Set where
  wrongVersion invalidNotification notificationLimit wrongID missingResult : Failure

module Replies (Payload ApplicationError : Set) where
  record Envelope : Set where
    constructor envelope
    field
      version method : Maybe Text
      id : Identifier
      error : Maybe ApplicationError
      result : Maybe Payload
  open Envelope

  data Outcome : Set where
    notification : ℕ → Outcome
    succeeded : Payload → Outcome
    rejected : ApplicationError → Outcome
    failed : Failure → Outcome

  responseBody : Maybe ApplicationError → Maybe Payload → Outcome
  responseBody (just error) result = rejected error
  responseBody nothing (just result) = succeeded result
  responseBody nothing nothing = failed missingResult

  identify : ℕ → ℕ → Envelope → Outcome
  identify expected notifications frame with id frame
  ... | absent with method frame
  ...   | nothing = failed invalidNotification
  ...   | just method with notifications <? 64
  ...     | yes _ = notification (suc notifications)
  ...     | no _ = failed notificationLimit
  identify expected notifications frame | null = failed wrongID
  identify expected notifications frame | invalid = failed wrongID
  identify expected notifications frame | string text = failed wrongID
  identify expected notifications frame | integer id with id ≟ℕ expected
  ... | no _ = failed wrongID
  ... | yes _ = responseBody (error frame) (result frame)

  receive : ℕ → ℕ → Envelope → Outcome
  receive expected notifications frame with version frame
  ... | nothing = failed wrongVersion
  ... | just version with ≡-dec _≟_ version (toList "2.0")
  ...   | no _ = failed wrongVersion
  ...   | yes _ = identify expected notifications frame

  errorPreserved : ∀ error result → responseBody (just error) result ≡ rejected error
  errorPreserved error result = refl

  wrongIDRefused : ∀ expected notifications frame got → id frame ≡ integer got →
    got ≢ expected → identify expected notifications frame ≡ failed wrongID
  wrongIDRefused expected notifications frame got same different rewrite same
    with got ≟ℕ expected
  ... | no _ = refl
  ... | yes equal = ⊥-elim (different equal)

  notificationBound : ∀ expected notifications frame count →
    identify expected notifications frame ≡ notification count → count ≤ 64
  notificationBound expected notifications frame count proof with id frame
  ... | absent with method frame
  ...   | nothing with proof
  ...     | ()
  notificationBound expected notifications frame count proof | absent | just method
    with notifications <? 64
  ... | yes bound with proof
  ...   | refl = bound
  notificationBound expected notifications frame count proof | absent | just method | no bound
    with proof
  ... | ()
  notificationBound expected notifications frame count () | null
  notificationBound expected notifications frame count () | invalid
  notificationBound expected notifications frame count () | string text
  notificationBound expected notifications frame count proof | integer id
    with id ≟ℕ expected
  ... | no _ with proof
  ...   | ()
  notificationBound expected notifications frame count proof | integer id | yes _
    with error frame | Envelope.result frame
  ... | just error | value with proof
  ...   | ()
  notificationBound expected notifications frame count proof | integer id | yes _ | nothing | just value
    with proof
  ... | ()
  notificationBound expected notifications frame count proof | integer id | yes _ | nothing | nothing
    with proof
  ... | ()

  notificationAdvances : ∀ expected notifications frame count →
    identify expected notifications frame ≡ notification count → count ≡ suc notifications
  notificationAdvances expected notifications frame count proof with id frame
  ... | absent with method frame
  ...   | nothing with proof
  ...     | ()
  notificationAdvances expected notifications frame count proof | absent | just method
    with notifications <? 64
  ... | yes bound with proof
  ...   | refl = refl
  notificationAdvances expected notifications frame count proof | absent | just method | no bound
    with proof
  ... | ()
  notificationAdvances expected notifications frame count () | null
  notificationAdvances expected notifications frame count () | invalid
  notificationAdvances expected notifications frame count () | string text
  notificationAdvances expected notifications frame count proof | integer id
    with id ≟ℕ expected
  ... | no _ with proof
  ...   | ()
  notificationAdvances expected notifications frame count proof | integer id | yes _
    with error frame | Envelope.result frame
  ... | just error | value with proof
  ...   | ()
  notificationAdvances expected notifications frame count proof | integer id | yes _ | nothing | just value
    with proof
  ... | ()
  notificationAdvances expected notifications frame count proof | integer id | yes _ | nothing | nothing
    with proof
  ... | ()

  receivedNotification : ∀ expected notifications frame count →
    receive expected notifications frame ≡ notification count →
    identify expected notifications frame ≡ notification count
  receivedNotification expected notifications frame count proof with version frame
  ... | nothing with proof
  ...   | ()
  receivedNotification expected notifications frame count proof | just version
    with ≡-dec _≟_ version (toList "2.0")
  ... | no _ with proof
  ...   | ()
  receivedNotification expected notifications frame count proof | just version | yes _ = proof

-- Request identifiers never wrap. The upper bound is explicit so the same
-- proof applies to the u64 client counter and to smaller test transports.
module IDs (maximum : ℕ) where
  record Allocated : Set where
    constructor allocated
    field current next : ℕ

  allocate : ℕ → Maybe Allocated
  allocate counter with counter <? maximum
  ... | yes _ = just (allocated counter (suc counter))
  ... | no _ = nothing

  advances : ∀ counter allocation → allocate counter ≡ just allocation →
    Allocated.current allocation < Allocated.next allocation
  advances counter allocation proof with counter <? maximum
  ... | no _ with proof
  ...   | ()
  advances counter allocation proof | yes _ with proof
  ... | refl = Data.Nat.Properties.≤-refl

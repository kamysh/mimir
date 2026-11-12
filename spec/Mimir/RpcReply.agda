{-# OPTIONS --safe #-}
-- Client-side JSON-RPC envelope semantics after syntax decoding. Duplicate
-- object keys and malformed JSON are handled by the wire decoder, not inferred
-- away here. Notifications do not impose a cutoff on a pending request.
module Mimir.RpcReply where

open import Data.Char using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)

data Identifier : Set where
  absent null invalid : Identifier
  string : Text → Identifier

data Failure : Set where
  wrongVersion invalidNotification wrongID missingResult : Failure

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

  identify : Text → ℕ → Envelope → Outcome
  identify expected notifications frame with id frame
  ... | absent with method frame
  ...   | nothing = failed invalidNotification
  ...   | just method = notification (suc notifications)
  identify expected notifications frame | null = failed wrongID
  identify expected notifications frame | invalid = failed wrongID
  identify expected notifications frame | string id with ≡-dec _≟_ id expected
  ... | no _ = failed wrongID
  ... | yes _ = responseBody (error frame) (result frame)

  receive : Text → ℕ → Envelope → Outcome
  receive expected notifications frame with version frame
  ... | nothing = failed wrongVersion
  ... | just version with ≡-dec _≟_ version (toList "2.0")
  ...   | no _ = failed wrongVersion
  ...   | yes _ = identify expected notifications frame

  errorPreserved : ∀ error result → responseBody (just error) result ≡ rejected error
  errorPreserved error result = refl

  wrongIDRefused : ∀ expected notifications frame got → id frame ≡ string got →
    got ≢ expected → identify expected notifications frame ≡ failed wrongID
  wrongIDRefused expected notifications frame got same different rewrite same
    with ≡-dec _≟_ got expected
  ... | no _ = refl
  ... | yes equal = ⊥-elim (different equal)

  notificationAdvances : ∀ expected notifications frame count →
    identify expected notifications frame ≡ notification count → count ≡ suc notifications
  notificationAdvances expected notifications frame count proof with id frame
  ... | absent with method frame
  ...   | nothing with proof
  ...     | ()
  notificationAdvances expected notifications frame .(suc notifications) refl | absent | just method = refl
  notificationAdvances expected notifications frame count () | null
  notificationAdvances expected notifications frame count () | invalid
  notificationAdvances expected notifications frame count proof | string id
    with ≡-dec _≟_ id expected
  ... | no _ with proof
  ...   | ()
  notificationAdvances expected notifications frame count proof | string id | yes _
    with error frame | Envelope.result frame
  ... | just error | value with proof
  ...   | ()
  notificationAdvances expected notifications frame count proof | string id | yes _ | nothing | just value
    with proof
  ... | ()
  notificationAdvances expected notifications frame count proof | string id | yes _ | nothing | nothing
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

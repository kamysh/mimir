{-# OPTIONS --safe #-}
-- Connection negotiation over explicit transport/verification observations.
-- Cryptographic observations are inputs, not postulates of authenticity.
module Mimir.TLS where

open import Data.Bool using (Bool; true; false; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Mimir.ConfigurationValues using (Mode; disable; prefer; require; verifyCa; verifyFull)
open import Mimir.Connection using (Transport; plaintext; encrypted)
import Mimir.Connection as C
open import Mimir.Text using (Text)

legacyMode : Mode → C.Mode
legacyMode disable = C.disable
legacyMode prefer = C.prefer
legacyMode require = C.require
legacyMode verifyCa = C.verifyCa
legacyMode verifyFull = C.verifyFull

admissible : Mode → Transport → Bool → Bool → Bool
admissible m = C.admissible (legacyMode m)

data Identity : Set where
  absent : Identity
  present : (certificate key : Text) → Identity

record Options : Set where
  constructor options
  field mode : Mode; root : Maybe Text; identity : Identity

data OptionError : Set where mismatchedIdentity disabledCertificates : OptionError

checkDisabled : Mode → Maybe Text → Identity → OptionError ⊎ Options
checkDisabled disable nothing absent = inj₂ (options disable nothing absent)
checkDisabled disable nothing (present cert key) = inj₁ disabledCertificates
checkDisabled disable (just root) identity = inj₁ disabledCertificates
checkDisabled prefer root identity = inj₂ (options prefer root identity)
checkDisabled require root identity = inj₂ (options require root identity)
checkDisabled verifyCa root identity = inj₂ (options verifyCa root identity)
checkDisabled verifyFull root identity = inj₂ (options verifyFull root identity)

validateOptions : Mode → Maybe Text → Maybe Text → Maybe Text → OptionError ⊎ Options
validateOptions m root nothing nothing = checkDisabled m root absent
validateOptions m root (just cert) (just key) = checkDisabled m root (present cert key)
validateOptions m root nothing (just key) = inj₁ mismatchedIdentity
validateOptions m root (just cert) nothing = inj₁ mismatchedIdentity

noPartialIdentity₁ : ∀ m root cert →
  validateOptions m root (just cert) nothing ≡ inj₁ mismatchedIdentity
noPartialIdentity₁ m root cert = refl

noPartialIdentity₂ : ∀ m root key →
  validateOptions m root nothing (just key) ≡ inj₁ mismatchedIdentity
noPartialIdentity₂ m root key = refl

disabledHasNoCertificates : ∀ root identity result →
  checkDisabled disable root identity ≡ inj₂ result →
  Options.root result ≡ nothing × Options.identity result ≡ absent
disabledHasNoCertificates nothing absent .(options disable nothing absent) refl = refl , refl
disabledHasNoCertificates nothing (present cert key) result ()
disabledHasNoCertificates (just root) identity result ()

data Failure : Set where
  socketFailure negotiationFailure tlsUnavailable handshakeFailure
    verificationFailure authenticationFailure interrupted : Failure

data State : Set where
  connecting : State
  negotiating handshaking : State
  authenticating usable : Transport → Bool → Bool → State
  failed : Failure → State

data Event : Set where
  socketConnected serverAcceptsTLS serverDeclinesTLS : Event
  handshakeComplete : (trusted hostnameMatches : Bool) → Event
  authenticated : Event
  socketError negotiationError handshakeError authenticationError stop : Event

data Effect : Set where
  none sendSSLRequest startHandshake sendStartup closeTransport : Effect

record Result : Set where
  constructor result
  field state : State; effect : Effect

connected : Mode → Result
connected disable = result (authenticating plaintext false false) sendStartup
connected _ = result negotiating sendSSLRequest

declined : Mode → Result
declined prefer = result (authenticating plaintext false false) sendStartup
declined _ = result (failed tlsUnavailable) closeTransport

verified : Mode → Bool → Bool → Result
verified m trust hostname with admissible m encrypted trust hostname ≟ true
... | yes valid = result (authenticating encrypted trust hostname) sendStartup
... | no invalid = result (failed verificationFailure) closeTransport

step : Mode → State → Event → Result
step m (failed failure) event = result (failed failure) none
step m s stop = result (failed interrupted) closeTransport
step m connecting socketConnected = connected m
step m connecting socketError = result (failed socketFailure) closeTransport
step m negotiating serverAcceptsTLS = result handshaking startHandshake
step m negotiating serverDeclinesTLS = declined m
step m negotiating negotiationError = result (failed negotiationFailure) closeTransport
step m handshaking (handshakeComplete trust hostname) = verified m trust hostname
step m handshaking handshakeError = result (failed handshakeFailure) closeTransport
step m (authenticating transport trust hostname) authenticated =
  result (usable transport trust hostname) none
step m (authenticating transport trust hostname) authenticationError =
  result (failed authenticationFailure) closeTransport
step m state event = result state none

Allowed : Mode → State → Set
Allowed m (authenticating transport trust hostname) = admissible m transport trust hostname ≡ true
Allowed m (usable transport trust hostname) = admissible m transport trust hostname ≡ true
Allowed m _ = ⊤

connectedAllowed : ∀ m → Allowed m (Result.state (connected m))
connectedAllowed disable = refl
connectedAllowed prefer = tt
connectedAllowed require = tt
connectedAllowed verifyCa = tt
connectedAllowed verifyFull = tt

declinedAllowed : ∀ m → Allowed m (Result.state (declined m))
declinedAllowed disable = tt
declinedAllowed prefer = refl
declinedAllowed require = tt
declinedAllowed verifyCa = tt
declinedAllowed verifyFull = tt

verifiedAllowed : ∀ m trust hostname → Allowed m (Result.state (verified m trust hostname))
verifiedAllowed m trust hostname with admissible m encrypted trust hostname ≟ true
... | yes valid = valid
... | no invalid = tt

preservesPolicy : ∀ m s event → Allowed m s → Allowed m (Result.state (step m s event))
preservesPolicy m (failed failure) event valid = tt
preservesPolicy m connecting stop valid = tt
preservesPolicy m negotiating stop valid = tt
preservesPolicy m handshaking stop valid = tt
preservesPolicy m (authenticating transport trust hostname) stop valid = tt
preservesPolicy m (usable transport trust hostname) stop valid = tt
preservesPolicy m connecting socketConnected valid = connectedAllowed m
preservesPolicy m connecting socketError valid = tt
preservesPolicy m negotiating serverAcceptsTLS valid = tt
preservesPolicy m negotiating serverDeclinesTLS valid = declinedAllowed m
preservesPolicy m negotiating negotiationError valid = tt
preservesPolicy m handshaking (handshakeComplete trust hostname) valid = verifiedAllowed m trust hostname
preservesPolicy m handshaking handshakeError valid = tt
preservesPolicy m (authenticating transport trust hostname) authenticated valid = valid
preservesPolicy m (authenticating transport trust hostname) authenticationError valid = tt
preservesPolicy m connecting serverAcceptsTLS valid = valid
preservesPolicy m connecting serverDeclinesTLS valid = valid
preservesPolicy m connecting (handshakeComplete trusted hostnameMatches) valid = valid
preservesPolicy m connecting authenticated valid = valid
preservesPolicy m connecting negotiationError valid = valid
preservesPolicy m connecting handshakeError valid = valid
preservesPolicy m connecting authenticationError valid = valid
preservesPolicy m negotiating socketConnected valid = valid
preservesPolicy m negotiating (handshakeComplete trusted hostnameMatches) valid = valid
preservesPolicy m negotiating authenticated valid = valid
preservesPolicy m negotiating socketError valid = valid
preservesPolicy m negotiating handshakeError valid = valid
preservesPolicy m negotiating authenticationError valid = valid
preservesPolicy m handshaking socketConnected valid = valid
preservesPolicy m handshaking serverAcceptsTLS valid = valid
preservesPolicy m handshaking serverDeclinesTLS valid = valid
preservesPolicy m handshaking authenticated valid = valid
preservesPolicy m handshaking socketError valid = valid
preservesPolicy m handshaking negotiationError valid = valid
preservesPolicy m handshaking authenticationError valid = valid
preservesPolicy m (authenticating x x₁ x₂) socketConnected valid = valid
preservesPolicy m (authenticating x x₁ x₂) serverAcceptsTLS valid = valid
preservesPolicy m (authenticating x x₁ x₂) serverDeclinesTLS valid = valid
preservesPolicy m (authenticating x x₁ x₂) (handshakeComplete trusted hostnameMatches) valid = valid
preservesPolicy m (authenticating x x₁ x₂) socketError valid = valid
preservesPolicy m (authenticating x x₁ x₂) negotiationError valid = valid
preservesPolicy m (authenticating x x₁ x₂) handshakeError valid = valid
preservesPolicy m (usable x x₁ x₂) socketConnected valid = valid
preservesPolicy m (usable x x₁ x₂) serverAcceptsTLS valid = valid
preservesPolicy m (usable x x₁ x₂) serverDeclinesTLS valid = valid
preservesPolicy m (usable x x₁ x₂) (handshakeComplete trusted hostnameMatches) valid = valid
preservesPolicy m (usable x x₁ x₂) authenticated valid = valid
preservesPolicy m (usable x x₁ x₂) socketError valid = valid
preservesPolicy m (usable x x₁ x₂) negotiationError valid = valid
preservesPolicy m (usable x x₁ x₂) handshakeError valid = valid
preservesPolicy m (usable x x₁ x₂) authenticationError valid = valid

data Reachable (m : Mode) : State → Set where
  initial : Reachable m connecting
  next : ∀ {s} → Reachable m s → (event : Event) → Reachable m (Result.state (step m s event))

reachablePolicy : ∀ {m s} → Reachable m s → Allowed m s
reachablePolicy initial = tt
reachablePolicy (next reachable event) = preservesPolicy _ _ event (reachablePolicy reachable)

noRequiredPlaintext : ∀ m trust hostname → C.requiresTLS (legacyMode m) ≡ true →
  Reachable m (usable plaintext trust hostname) → ⊥
noRequiredPlaintext m trust hostname required reachable with
  trans (sym (C.required-modes-refuse-plaintext (legacyMode m) trust hostname required))
    (reachablePolicy reachable)
... | ()

handshakeFailureNeverDowngrades : ∀ m → step m handshaking handshakeError ≡
  result (failed handshakeFailure) closeTransport
handshakeFailureNeverDowngrades m = refl

failureAbsorbs : ∀ m failure event → step m (failed failure) event ≡ result (failed failure) none
failureAbsorbs m failure event = refl

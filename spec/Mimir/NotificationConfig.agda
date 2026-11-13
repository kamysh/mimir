{-# OPTIONS --safe #-}
-- Existing notification configuration semantics, including disabled-config
-- admission and provider-specific credential exclusions. Raw TOML fields and
-- bounded integer decoding are separate from these semantic checks.
module Mimir.NotificationConfig where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.String using (String; toList)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_×-dec_; _⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.CharacterRules using (NoControls; noControls?)
open import Mimir.NotificationSchema using (AsciiAlphaNumeric; asciiAlphaNumeric?)
open import Mimir.WhitespaceWords using (WholeWord; wholeWord?)
open import Mimir.EmailAddress using (Address; address?)
open import Mimir.Collections using (all?; negate)
open import Mimir.Validation

data TLS : Set where starttls encrypted : TLS
data Auth : Set where passwordAuth oauth2 anonymous : Auth
data Provider : Set where google microsoft : Provider

record OAuth : Set where
  constructor oauthSettings
  field
    provider : Provider
    clientID refreshToken : Text
    clientSecret tenant scope : Maybe Text

record Config : Set where
  constructor config
  field
    enabled : Bool
    host : Maybe Text
    port : Maybe ℕ
    tls : Maybe TLS
    fromAddress : Maybe Text
    recipients : List Text
    username password : Maybe Text
    auth : Maybe Auth
    oauth : Maybe OAuth
    -- Optional daily reporting has no Mimir-selected delivery time. The
    -- external calendar boundary interprets this user's local clock setting.
    dailyReportAt : Maybe Text
    -- User-configurable delivery controls, independent of review progress.
    timeoutSeconds retrySeconds maxAttempts : ℕ

defaults : Config
defaults = config false nothing nothing nothing nothing [] nothing nothing nothing nothing nothing 15 300 5

Required : ∀ {A : Set} → (A → Set) → Maybe A → Set
Required p nothing = ⊥
Required p (just value) = p value

required? : ∀ {A : Set} {P : A → Set} → ((a : A) → Dec (P a)) → ∀ value → Dec (Required P value)
required? check nothing = no (λ ())
required? check (just value) = check value

Optional : ∀ {A : Set} → (A → Set) → Maybe A → Set
Optional p nothing = ⊤
Optional p (just value) = p value

optional? : ∀ {A : Set} {P : A → Set} → ((a : A) → Dec (P a)) → ∀ value → Dec (Optional P value)
optional? check nothing = yes tt
optional? check (just value) = check value

Absent : ∀ {A : Set} → Maybe A → Set
Absent value = value ≡ nothing

absent? : ∀ {A : Set} (value : Maybe A) → Dec (Absent value)
absent? nothing = yes refl
absent? (just value) = no (λ ())

Present : ∀ {A : Set} → Maybe A → Set
Present = Required (λ _ → ⊤)

present? : ∀ {A : Set} (value : Maybe A) → Dec (Present value)
present? = required? (λ _ → yes tt)

Trimmed : Text → Set
Trimmed text = Nonblank text × (text ≡ trim text × NoControls text)

trimmed? : ∀ text → Dec (Trimmed text)
trimmed? text = nonblank? text ×-dec ((text ≟Text trim text) ×-dec noControls? text)

Credential : Text → Set
Credential = Trimmed

credential? : ∀ text → Dec (Credential text)
credential? = trimmed?

Host : Text → Set
Host text = Trimmed text × All (λ c → ¬ c ≡ '/' × ¬ c ≡ ':') text

host? : ∀ text → Dec (Host text)
host? text = trimmed? text ×-dec all? (λ c → negate (c ≟ '/') ×-dec negate (c ≟ ':')) text

NoDoubleDot : Text → Set
NoDoubleDot [] = ⊤
NoDoubleDot (c ∷ []) = ⊤
NoDoubleDot (c ∷ d ∷ rest) = ¬ (c ≡ '.' × d ≡ '.') × NoDoubleDot (d ∷ rest)

noDoubleDot? : ∀ text → Dec (NoDoubleDot text)
noDoubleDot? [] = yes tt
noDoubleDot? (c ∷ []) = yes tt
noDoubleDot? (c ∷ d ∷ rest) = negate ((c ≟ '.') ×-dec (d ≟ '.')) ×-dec noDoubleDot? (d ∷ rest)

TenantChar : Char → Set
TenantChar c = AsciiAlphaNumeric c ⊎ (c ≡ '-' ⊎ c ≡ '.')

tenantChar? : ∀ c → Dec (TenantChar c)
tenantChar? c = asciiAlphaNumeric? c ⊎-dec ((c ≟ '-') ⊎-dec (c ≟ '.'))

Tenant : Text → Set
Tenant text = Nonempty text × (NoDoubleDot text × All TenantChar text)

tenant? : ∀ text → Dec (Tenant text)
tenant? text = nonempty? text ×-dec (noDoubleDot? text ×-dec all? tenantChar? text)

MicrosoftScopes : Text → Set
MicrosoftScopes text = WholeWord (toList "https://outlook.office.com/SMTP.Send") text ×
  WholeWord (toList "offline_access") text

microsoftScopes? : ∀ text → Dec (MicrosoftScopes text)
microsoftScopes? text = wholeWord? (toList "https://outlook.office.com/SMTP.Send") text ×-dec
  wholeWord? (toList "offline_access") text

ProviderValid : OAuth → Set
ProviderValid (oauthSettings google clientID refreshToken secret tenant scope) =
  Absent tenant × Optional (λ value → value ≡ toList "https://mail.google.com/") scope
ProviderValid (oauthSettings microsoft clientID refreshToken secret tenant scope) =
  Required Tenant tenant × Required MicrosoftScopes scope

providerValid? : ∀ value → Dec (ProviderValid value)
providerValid? (oauthSettings google clientID refreshToken secret tenant scope) =
  absent? tenant ×-dec optional? (λ value → value ≟Text toList "https://mail.google.com/") scope
providerValid? (oauthSettings microsoft clientID refreshToken secret tenant scope) =
  required? tenant? tenant ×-dec required? microsoftScopes? scope

OAuthValid : OAuth → Set
OAuthValid value = Credential (OAuth.clientID value) ×
  (Credential (OAuth.refreshToken value) ×
  (Optional Credential (OAuth.clientSecret value) × ProviderValid value))

oauthValid? : ∀ value → Dec (OAuthValid value)
oauthValid? value = credential? (OAuth.clientID value) ×-dec
  (credential? (OAuth.refreshToken value) ×-dec
  (optional? credential? (OAuth.clientSecret value) ×-dec providerValid? value))

AuthValid : Config → Auth → Set
AuthValid cfg passwordAuth = Required Trimmed (Config.username cfg) ×
  (Required Trimmed (Config.password cfg) × Absent (Config.oauth cfg))
AuthValid cfg oauth2 = Required Trimmed (Config.username cfg) ×
  (Absent (Config.password cfg) × Required OAuthValid (Config.oauth cfg))
AuthValid cfg anonymous = Absent (Config.username cfg) ×
  (Absent (Config.password cfg) × Absent (Config.oauth cfg))

authValid? : ∀ cfg mode → Dec (AuthValid cfg mode)
authValid? cfg passwordAuth = required? trimmed? (Config.username cfg) ×-dec
  (required? trimmed? (Config.password cfg) ×-dec absent? (Config.oauth cfg))
authValid? cfg oauth2 = required? trimmed? (Config.username cfg) ×-dec
  (absent? (Config.password cfg) ×-dec required? oauthValid? (Config.oauth cfg))
authValid? cfg anonymous = absent? (Config.username cfg) ×-dec
  (absent? (Config.password cfg) ×-dec absent? (Config.oauth cfg))

Range : ℕ → ℕ → Set
Range maximum value = 1 ≤ value × value ≤ maximum

range? : ∀ maximum value → Dec (Range maximum value)
range? maximum value = (1 ≤? value) ×-dec (value ≤? maximum)

Recipients : List Text → Set
Recipients [] = ⊥
Recipients (first ∷ rest) = Address first × All Address rest

recipients? : ∀ values → Dec (Recipients values)
recipients? [] = no (λ ())
recipients? (first ∷ rest) = address? first ×-dec all? address? rest

EnabledValid : Config → Set
EnabledValid cfg = (Required Host (Config.host cfg) ×
  (Required (Range 65535) (Config.port cfg) × (Present (Config.tls cfg) ×
  (Required Address (Config.fromAddress cfg) × (Recipients (Config.recipients cfg) ×
  Required (AuthValid cfg) (Config.auth cfg)))))) ×
  (1 ≤ Config.timeoutSeconds cfg × (1 ≤ Config.retrySeconds cfg × 1 ≤ Config.maxAttempts cfg))

atCheck : ∀ {P : Set} → String → Dec P → Checked P
atCheck name decision = at (key name) (check (fault [] malformedInput "invalid notification configuration field") decision)

checkEnabled : ∀ cfg → Checked (EnabledValid cfg)
checkEnabled cfg = combine
  (combine (atCheck "host" (required? host? (Config.host cfg)))
  (combine (atCheck "port" (required? (range? 65535) (Config.port cfg)))
  (combine (atCheck "tls" (present? (Config.tls cfg)))
  (combine (atCheck "from" (required? address? (Config.fromAddress cfg)))
  (combine (atCheck "to" (recipients? (Config.recipients cfg)))
    (atCheck "auth" (required? (authValid? cfg) (Config.auth cfg))))))))
  (combine (atCheck "timeout_seconds" (1 ≤? Config.timeoutSeconds cfg))
    (combine (atCheck "retry_seconds" (1 ≤? Config.retrySeconds cfg))
      (atCheck "max_attempts" (1 ≤? Config.maxAttempts cfg))))

Valid : Config → Set
Valid cfg with Config.enabled cfg
... | false = ⊤
... | true = EnabledValid cfg

validate : ∀ cfg → Checked (Valid cfg)
validate cfg with Config.enabled cfg
... | false = accepted tt
... | true = at (key "email") (checkEnabled cfg)

validConfigurationNeverRejected : ∀ cfg → Valid cfg → reported (validate cfg) ≡ []
validConfigurationNeverRejected cfg = noFalseRejection (validate cfg)

anonymousExcludesCredentials : ∀ cfg → AuthValid cfg anonymous →
  Absent (Config.username cfg) × (Absent (Config.password cfg) × Absent (Config.oauth cfg))
anonymousExcludesCredentials cfg proof = proof

oauthExcludesPassword : ∀ cfg → AuthValid cfg oauth2 → Absent (Config.password cfg)
oauthExcludesPassword cfg proof = proj₁ (proj₂ proof)

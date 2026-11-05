{-# OPTIONS --safe #-}
-- The application's deliberately small address grammar: exactly one @,
-- nonempty sides, no Unicode whitespace or control. Not an RFC mailbox parser.
module Mimir.EmailAddress where

open import Data.Char using (Char; _≟_)
open import Data.Bool using (false; true)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_×-dec_; map′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text
open import Mimir.TextFields
open import Mimir.CharacterRules using (Control; control?)
open import Mimir.Collections using (all?; negate)

module At = Split (λ c → c ≡ '@') (λ c → c ≟ '@')

NoAt : Text → Set
NoAt = All (λ c → ¬ c ≡ '@')

noAt? : ∀ text → Dec (NoAt text)
noAt? = all? (λ c → negate (c ≟ '@'))

CleanChar : Char → Set
CleanChar c = isWhitespace c ≡ false × ¬ Control c

notWhitespace? : ∀ c → Dec (isWhitespace c ≡ false)
notWhitespace? c with isWhitespace c
... | false = yes refl
... | true = no (λ ())

cleanChar? : ∀ c → Dec (CleanChar c)
cleanChar? c = notWhitespace? c ×-dec negate (control? c)

record Address (input : Text) : Set where
  constructor address
  field
    local domain : Text
    exact : input ≡ local ++ ('@' ∷ domain)
    localNonempty : Nonempty local
    domainNonempty : Nonempty domain
    noAtLocal : NoAt local
    noAtDomain : NoAt domain
    clean : All CleanChar input

DomainPart : Text → Set
DomainPart [] = ⊥
DomainPart (c ∷ domain) = c ≡ '@' × (Nonempty domain × NoAt domain)

domainPart? : ∀ suffix → Dec (DomainPart suffix)
domainPart? [] = no (λ ())
domainPart? (c ∷ domain) = (c ≟ '@') ×-dec (nonempty? domain ×-dec noAt? domain)

ParsedValid : Text → Set
ParsedValid input = Nonempty (At.Cut.prefix (At.split input)) ×
  (DomainPart (At.Cut.suffix (At.split input)) × All CleanChar input)

parsedValid? : ∀ input → Dec (ParsedValid input)
parsedValid? input = nonempty? (At.Cut.prefix (At.split input)) ×-dec
  (domainPart? (At.Cut.suffix (At.split input)) ×-dec all? cleanChar? input)

fromCut : ∀ input (cut : At.Cut input) →
  Nonempty (At.Cut.prefix cut) → DomainPart (At.Cut.suffix cut) → All CleanChar input → Address input
fromCut input (At.cut local [] exact noAt boundary) nonempty () clean
fromCut input (At.cut local (c ∷ domain) exact noAt boundary) nonempty (refl , domainNonempty , noAtDomain) clean =
  address local domain exact nonempty domainNonempty noAt noAtDomain clean

parsedToAddress : ∀ {input} → ParsedValid input → Address input
parsedToAddress {input} (local , domain , clean) = fromCut input (At.split input) local domain clean

addressToParsed : ∀ {input} → Address input → ParsedValid input
addressToParsed (address local domain refl localNonempty domainNonempty noAtLocal noAtDomain clean)
  with At.maximalSplit local ('@' ∷ domain) noAtLocal refl
... | localExact , domainExact rewrite localExact | domainExact =
  localNonempty , (refl , domainNonempty , noAtDomain) , clean

address? : ∀ input → Dec (Address input)
address? input = map′ parsedToAddress addressToParsed (parsedValid? input)

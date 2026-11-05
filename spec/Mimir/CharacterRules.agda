{-# OPTIONS --safe #-}
-- Unicode Control is the stable C0/C1 category, not all Unicode whitespace.
module Mimir.CharacterRules where

open import Data.Char using (Char; toℕ; _≟_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable.Core using (_×-dec_; _⊎-dec_)
open import Mimir.Collections using (all?; negate)
open import Mimir.Text
open import Mimir.Validation

Control : Char → Set
Control c = toℕ c ≤ 31 ⊎ (127 ≤ toℕ c × toℕ c ≤ 159)

control? : ∀ c → Dec (Control c)
control? c = (toℕ c ≤? 31) ⊎-dec ((127 ≤? toℕ c) ×-dec (toℕ c ≤? 159))

NoControls : Text → Set
NoControls = All (λ c → Control c → ⊥)

noControls? : ∀ text → Dec (NoControls text)
noControls? = all? (λ c → negate (control? c))

TokenValid : ℕ → Text → Set
TokenValid maximum text = Nonempty text × (Bounded maximum text × NoControls text)

tokenValid? : ∀ maximum text → Dec (TokenValid maximum text)
tokenValid? maximum text = nonempty? text ×-dec (bounded? maximum text ×-dec noControls? text)

checkToken : ∀ maximum text → Checked (TokenValid maximum text)
checkToken maximum text = combine
  (check (fault [] emptyText "token must not be empty") (nonempty? text))
  (combine (check (fault [] textTooLong "token exceeds byte limit") (bounded? maximum text))
    (check (fault [] malformedInput "token contains a control character") (noControls? text)))

Letter : Char → Char → Char → Set
Letter lower upper actual = actual ≡ lower ⊎ actual ≡ upper

letter? : ∀ lower upper actual → Dec (Letter lower upper actual)
letter? lower upper actual = (actual ≟ lower) ⊎-dec (actual ≟ upper)

-- Exact ASCII case-insensitive bearer spelling; Unicode case folding does
-- not expand the accepted token-type language.
Bearer : Text → Set
Bearer (b ∷ e ∷ a ∷ r ∷ e′ ∷ r′ ∷ []) =
  Letter 'b' 'B' b × (Letter 'e' 'E' e × (Letter 'a' 'A' a ×
  (Letter 'r' 'R' r × (Letter 'e' 'E' e′ × Letter 'r' 'R' r′))))
Bearer _ = ⊥

bearer? : ∀ text → Dec (Bearer text)
bearer? (b ∷ e ∷ a ∷ r ∷ e′ ∷ r′ ∷ []) =
  letter? 'b' 'B' b ×-dec (letter? 'e' 'E' e ×-dec (letter? 'a' 'A' a ×-dec
  (letter? 'r' 'R' r ×-dec (letter? 'e' 'E' e′ ×-dec letter? 'r' 'R' r′))))
bearer? [] = no (λ ())
bearer? (_ ∷ []) = no (λ ())
bearer? (_ ∷ _ ∷ []) = no (λ ())
bearer? (_ ∷ _ ∷ _ ∷ []) = no (λ ())
bearer? (_ ∷ _ ∷ _ ∷ _ ∷ []) = no (λ ())
bearer? (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) = no (λ ())
bearer? (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _) = no (λ ())

{-# OPTIONS --safe #-}
module Mimir.ParsedPart where

open import Data.List using (_++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product using (Σ-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.Text using (Text)

record Part (A : Set) (spell : A → Text) (input : Text) : Set where
  constructor part
  field value : A; rest : Text; reconstruct : input ≡ spell value ++ rest

pairSpelling : ∀ {A B : Set} → (A → Text) → (B → Text) → A × B → Text
pairSpelling left right (a , b) = left a ++ right b

join : ∀ {A B : Set} {left : A → Text} {right : B → Text} {input}
  (first : Part A left input) → Part B right (Part.rest first) →
  Part (A × B) (pairSpelling left right) input
join {left = left} {right = right} (part a middle first) (part b rest second) =
  part (a , b) rest (trans first (trans (cong (left a ++_) second) (sym (++-assoc (left a) (right b) rest))))

Parser : (A : Set) → (A → Text) → Set
Parser A spell = (input : Text) → Maybe (Part A spell input)

sequence : ∀ {A B : Set} {left : A → Text} {right : B → Text} →
  Parser A left → Parser B right → Parser (A × B) (pairSpelling left right)
sequence first second input with first input
... | nothing = nothing
... | just a with second (Part.rest a)
...   | nothing = nothing
...   | just b = just (join a b)

Succeeded : ∀ {A : Set} {spell : A → Text} → Parser A spell → Text → Text → Set
Succeeded {A} {spell} parser input tail = Σ[ result ∈ Part A spell input ]
  (parser input ≡ just result × Part.rest result ≡ tail)

sequenceComplete : ∀ {A B : Set} {left : A → Text} {right : B → Text}
  (first : Parser A left) (second : Parser B right) input middle tail →
  Succeeded first input middle → Succeeded second middle tail →
  Succeeded (sequence first second) input tail
sequenceComplete first second input .(Part.rest a) tail
  (a , firstRead , refl) (b , secondRead , last)
  rewrite firstRead | secondRead = join a b , refl , last

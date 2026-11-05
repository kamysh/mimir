{-# OPTIONS --safe #-}
-- Exact decidable keys for validated typed payloads. Real-valued leaves model
-- finite floating comparison; lexical text leaves are never normalized.
module Mimir.SemanticKey where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
import Data.Nat.Properties as Nat
open import Data.Integer using (ℤ)
import Data.Integer.Properties as Int
open import Data.Rational using (ℚ)
import Data.Rational.Properties as Rational
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)

data Key : Set where
  natural : ℕ → Key
  integer : ℤ → Key
  text : Text → Key
  real : ℚ → Key
  fields : List Key → Key

mutual
  equal : (x y : Key) → Dec (x ≡ y)
  equal (natural x) (natural y) with x Nat.≟ y
  ... | yes refl = yes refl
  ... | no different = no (λ { refl → different refl })
  equal (integer x) (integer y) with x Int.≟ y
  ... | yes refl = yes refl
  ... | no different = no (λ { refl → different refl })
  equal (text x) (text y) with x ≟Text y
  ... | yes refl = yes refl
  ... | no different = no (λ { refl → different refl })
  equal (real x) (real y) with x Rational.≟ y
  ... | yes refl = yes refl
  ... | no different = no (λ { refl → different refl })
  equal (fields xs) (fields ys) with listEqual xs ys
  ... | yes refl = yes refl
  ... | no different = no (λ { refl → different refl })
  equal (natural _) (integer _) = no (λ ())
  equal (natural _) (text _) = no (λ ())
  equal (natural _) (real _) = no (λ ())
  equal (natural _) (fields _) = no (λ ())
  equal (integer _) (natural _) = no (λ ())
  equal (integer _) (text _) = no (λ ())
  equal (integer _) (real _) = no (λ ())
  equal (integer _) (fields _) = no (λ ())
  equal (text _) (natural _) = no (λ ())
  equal (text _) (integer _) = no (λ ())
  equal (text _) (real _) = no (λ ())
  equal (text _) (fields _) = no (λ ())
  equal (real _) (natural _) = no (λ ())
  equal (real _) (integer _) = no (λ ())
  equal (real _) (text _) = no (λ ())
  equal (real _) (fields _) = no (λ ())
  equal (fields _) (natural _) = no (λ ())
  equal (fields _) (integer _) = no (λ ())
  equal (fields _) (text _) = no (λ ())
  equal (fields _) (real _) = no (λ ())

  listEqual : (xs ys : List Key) → Dec (xs ≡ ys)
  listEqual [] [] = yes refl
  listEqual [] (_ ∷ _) = no (λ ())
  listEqual (_ ∷ _) [] = no (λ ())
  listEqual (x ∷ xs) (y ∷ ys) with equal x y | listEqual xs ys
  ... | yes refl | yes refl = yes refl
  ... | no different | _ = no (λ { refl → different refl })
  ... | _ | no different = no (λ { refl → different refl })

textFaithful : ∀ x y → text x ≡ text y → x ≡ y
textFaithful x .x refl = refl

realFaithful : ∀ x y → real x ≡ real y → x ≡ y
realFaithful x .x refl = refl

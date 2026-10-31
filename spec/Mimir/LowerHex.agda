{-# OPTIONS --safe #-}
-- Fixed two-digit lowercase hexadecimal for every byte, including leading
-- zeros. The finite digit fact covers all 16x16 pairs, not example fixtures.
module Mimir.LowerHex where

open import Data.Char using (Char)
import Data.Char.Properties as Char
open import Data.Fin using (Fin; toℕ)
import Data.Fin.Properties as Fin
open import Data.List using (List; []; _∷_; map)
import Data.List.Properties as List
import Data.Vec as Vec
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
import Mimir.Radix as Radix
open import Mimir.ExactBytes using (Byte)

alphabet : Vec.Vec Char 16
alphabet = '0' Vec.∷ '1' Vec.∷ '2' Vec.∷ '3' Vec.∷ '4' Vec.∷ '5' Vec.∷ '6' Vec.∷ '7' Vec.∷
  '8' Vec.∷ '9' Vec.∷ 'a' Vec.∷ 'b' Vec.∷ 'c' Vec.∷ 'd' Vec.∷ 'e' Vec.∷ 'f' Vec.∷ Vec.[]

character : Fin 16 → Char
character = Vec.lookup alphabet

injective? : ∀ first second → Dec (character first ≡ character second → first ≡ second)
injective? first second with first Fin.≟ second
... | yes same = yes (λ _ → same)
... | no different with character first Char.≟ character second
...   | yes same = no (λ implication → different (implication same))
...   | no distinct = yes (λ same → ⊥-elim (distinct same))

abstract
  characterInjective : ∀ first second → character first ≡ character second → first ≡ second
  characterInjective = toWitness {a? = Fin.all? (λ first → Fin.all? (injective? first))} tt

module Hex = Radix.Base 15
Digits = Vec.Vec (Fin 16) 2

digits : Byte → Digits
digits byte = Hex.Expansion.digits (Hex.encode 2 (toℕ byte) (Fin.toℕ<n byte))

digitsValue : ∀ byte → Hex.value (digits byte) ≡ toℕ byte
digitsValue byte = Hex.decodeEncode 2 (toℕ byte) (Fin.toℕ<n byte)

digitsInjective : ∀ first second → digits first ≡ digits second → first ≡ second
digitsInjective first second same = Fin.toℕ-injective
  (trans (sym (digitsValue first)) (trans (cong Hex.value same) (digitsValue second)))

render : List Digits → List Char
render [] = []
render ((low Vec.∷ high Vec.∷ Vec.[]) ∷ rest) = character high ∷ character low ∷ render rest

renderInjective : ∀ first second → render first ≡ render second → first ≡ second
renderInjective [] [] same = refl
renderInjective [] ((_ Vec.∷ _ Vec.∷ Vec.[]) ∷ _) ()
renderInjective ((_ Vec.∷ _ Vec.∷ Vec.[]) ∷ _) [] ()
renderInjective ((low Vec.∷ high Vec.∷ Vec.[]) ∷ rest)
  ((otherLow Vec.∷ otherHigh Vec.∷ Vec.[]) ∷ remaining) same =
  cong₂ _∷_ (cong₂ Vec._∷_
    (characterInjective low otherLow (List.∷-injectiveˡ (List.∷-injectiveʳ same)))
    (cong (λ digit → digit Vec.∷ Vec.[]) (characterInjective high otherHigh (List.∷-injectiveˡ same))))
    (renderInjective rest remaining (List.∷-injectiveʳ (List.∷-injectiveʳ same)))

bytesInjective : ∀ first second → map digits first ≡ map digits second → first ≡ second
bytesInjective [] [] same = refl
bytesInjective [] (_ ∷ _) ()
bytesInjective (_ ∷ _) [] ()
bytesInjective (first ∷ rest) (second ∷ remaining) same = cong₂ _∷_
  (digitsInjective first second (List.∷-injectiveˡ same))
  (bytesInjective rest remaining (List.∷-injectiveʳ same))

encode : List Byte → List Char
encode bytes = render (map digits bytes)

encodeInjective : ∀ first second → encode first ≡ encode second → first ≡ second
encodeInjective first second same = bytesInjective first second (renderInjective (map digits first) (map digits second) same)

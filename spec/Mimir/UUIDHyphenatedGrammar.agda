{-# OPTIONS --safe #-}
-- Soundness/completeness of hyphenated parsing against five independent hex
-- groups and four literal separators, including mixed-case hexadecimal input.
module Mimir.UUIDHyphenatedGrammar where

open import Data.Fin using (#_; _≟_)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (_+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
import Data.Vec as V
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Mimir.Bits using (Byte)
import Mimir.HexBytes as Hex
import Mimir.UUIDGroups as G
import Mimir.UUIDHyphenated as H

dashSound : ∀ input rest → H.dash input ≡ just rest → input ≡ (# 45) ∷ rest
dashSound [] rest ()
dashSound (first ∷ input) rest observed with first ≟ (# 45)
... | no different with observed
...   | ()
dashSound (first ∷ input) .input refl | yes same = cong (_∷ input) same

takeGroupSound : ∀ {A : Set} count input next (output : A) → H.takeGroup count input next ≡ just output →
  Σ (V.Vec Byte count) (λ bytes → Σ (List Byte) (λ rest → Hex.Pairs input bytes ((# 45) ∷ rest) × next bytes rest ≡ just output))
takeGroupSound count input next output observed with Hex.read count input in parsed
... | nothing with observed
...   | ()
takeGroupSound count input next output observed | just (bytes , rest) with H.dash rest in separated
... | nothing with observed
...   | ()
takeGroupSound count input next output observed | just (bytes , rest) | just after = bytes , after ,
  subst (Hex.Pairs input bytes) (dashSound rest after separated) (Hex.sound count input bytes rest parsed) , observed

record Read (input : List Byte) (value : G.Groups) (rest : List Byte) : Set where
  constructor grouped
  field
    afterFirst afterSecond afterThird afterFourth : List Byte
    first : Hex.Pairs input (G.Groups.first value) ((# 45) ∷ afterFirst)
    second : Hex.Pairs afterFirst (G.Groups.second value) ((# 45) ∷ afterSecond)
    third : Hex.Pairs afterSecond (G.Groups.third value) ((# 45) ∷ afterThird)
    fourth : Hex.Pairs afterThird (G.Groups.fourth value) ((# 45) ∷ afterFourth)
    fifth : Hex.Pairs afterFourth (G.Groups.fifth value) rest

complete : ∀ {input value rest} → Read input value rest → H.read input ≡ just (value , rest)
complete {value = G.groups first second third fourth fifth} (grouped afterFirst afterSecond afterThird afterFourth p1 p2 p3 p4 p5)
  rewrite Hex.complete p1 | Hex.complete p2 | Hex.complete p3 | Hex.complete p4 | Hex.complete p5 = refl

consumedLength : ∀ {input value rest} → Read input value rest → length input ≡ 36 + length rest
consumedLength (grouped afterFirst afterSecond afterThird afterFourth p1 p2 p3 p4 p5)
  rewrite Hex.consumedLength p1 | Hex.consumedLength p2 | Hex.consumedLength p3 |
    Hex.consumedLength p4 | Hex.consumedLength p5 = refl

lastSound : ∀ input first second third fourth afterFirst afterSecond afterThird afterFourth value rest →
  Hex.Pairs input first ((# 45) ∷ afterFirst) → Hex.Pairs afterFirst second ((# 45) ∷ afterSecond) →
  Hex.Pairs afterSecond third ((# 45) ∷ afterThird) → Hex.Pairs afterThird fourth ((# 45) ∷ afterFourth) →
  H.afterFourth first second third fourth afterFourth ≡ just (value , rest) → Read input value rest
lastSound input first second third fourth afterFirst afterSecond afterThird afterFourth value rest p1 p2 p3 p4 observed
  with Hex.read 6 afterFourth in parsed
... | nothing with observed
...   | ()
lastSound input first second third fourth afterFirst afterSecond afterThird afterFourth .(G.groups first second third fourth fifth) .rest p1 p2 p3 p4 refl
  | just (fifth , rest) = grouped afterFirst afterSecond afterThird afterFourth p1 p2 p3 p4 (Hex.sound 6 afterFourth fifth rest parsed)

sound : ∀ input value rest → H.read input ≡ just (value , rest) → Read input value rest
sound input value rest observed with takeGroupSound 4 input H.afterFirst (value , rest) observed
... | first , afterFirst , p1 , remaining1 with takeGroupSound 2 afterFirst (H.afterSecond first) (value , rest) remaining1
...   | second , afterSecond , p2 , remaining2 with takeGroupSound 2 afterSecond (H.afterThird first second) (value , rest) remaining2
...     | third , afterThird , p3 , remaining3 with takeGroupSound 2 afterThird (H.afterFourth first second third) (value , rest) remaining3
...       | fourth , afterFourth , p4 , remaining4 =
  lastSound input first second third fourth afterFirst afterSecond afterThird afterFourth value rest p1 p2 p3 p4 remaining4

{-# OPTIONS --safe #-}
-- Canonical UUID output and ordered hyphenated parsing. Four separators occur
-- after 4, 2, 2 and 2 bytes; the last group has 6 bytes. Suffixes are preserved.
module Mimir.UUIDHyphenated where

open import Data.Fin using (#_; _≟_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; _+_; _*_; suc)
import Data.Vec as V
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Mimir.Bits using (Byte)
import Mimir.HexBytes as Hex
import Mimir.UUIDGroups as G

_>>=_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= next = nothing
just value >>= next = next value
infixl 1 _>>=_

dash : List Byte → Maybe (List Byte)
dash [] = nothing
dash (first ∷ rest) with first ≟ (# 45)
... | yes same = just rest
... | no different = nothing

spell : G.Groups → List Byte
spell (G.groups first second third fourth fifth) = Hex.encode first ++ ((# 45) ∷
  (Hex.encode second ++ ((# 45) ∷ (Hex.encode third ++ ((# 45) ∷
  (Hex.encode fourth ++ ((# 45) ∷ Hex.encode fifth)))))))

takeGroup : ∀ {A : Set} count → List Byte → (V.Vec Byte count → List Byte → Maybe A) → Maybe A
takeGroup count input next = Hex.read count input >>= λ where
  (value , rest) → dash rest >>= next value

afterFourth : V.Vec Byte 4 → V.Vec Byte 2 → V.Vec Byte 2 → V.Vec Byte 2 → List Byte → Maybe (G.Groups × List Byte)
afterFourth first second third fourth input = Hex.read 6 input >>= λ where
  (fifth , rest) → just (G.groups first second third fourth fifth , rest)

afterThird : V.Vec Byte 4 → V.Vec Byte 2 → V.Vec Byte 2 → List Byte → Maybe (G.Groups × List Byte)
afterThird first second third input = takeGroup 2 input (afterFourth first second third)

afterSecond : V.Vec Byte 4 → V.Vec Byte 2 → List Byte → Maybe (G.Groups × List Byte)
afterSecond first second input = takeGroup 2 input (afterThird first second)

afterFirst : V.Vec Byte 4 → List Byte → Maybe (G.Groups × List Byte)
afterFirst first input = takeGroup 2 input (afterSecond first)

read : List Byte → Maybe (G.Groups × List Byte)
read input = takeGroup 4 input afterFirst

tail4 : V.Vec Byte 2 → List Byte → List Byte
tail4 fourth end = Hex.encode fourth ++ ((# 45) ∷ end)

tail3 : V.Vec Byte 2 → V.Vec Byte 2 → List Byte → List Byte
tail3 third fourth end = Hex.encode third ++ ((# 45) ∷ tail4 fourth end)

tail2 : V.Vec Byte 2 → V.Vec Byte 2 → V.Vec Byte 2 → List Byte → List Byte
tail2 second third fourth end = Hex.encode second ++ ((# 45) ∷ tail3 third fourth end)

spellingLength : ∀ value → length (spell value) ≡ 36
spellingLength (G.groups first second third fourth fifth)
  rewrite length-++ (Hex.encode first) {ys = (# 45) ∷ tail2 second third fourth (Hex.encode fifth)} | Hex.encodedLength first |
    length-++ (Hex.encode second) {ys = (# 45) ∷ tail3 third fourth (Hex.encode fifth)} | Hex.encodedLength second |
    length-++ (Hex.encode third) {ys = (# 45) ∷ tail4 fourth (Hex.encode fifth)} | Hex.encodedLength third |
    length-++ (Hex.encode fourth) {ys = (# 45) ∷ Hex.encode fifth} | Hex.encodedLength fourth | Hex.encodedLength fifth = refl

spellingWithSuffix : ∀ value rest → spell value ++ rest ≡
  Hex.encode (G.Groups.first value) ++ ((# 45) ∷ (Hex.encode (G.Groups.second value) ++ ((# 45) ∷
  (Hex.encode (G.Groups.third value) ++ ((# 45) ∷ (Hex.encode (G.Groups.fourth value) ++ ((# 45) ∷
  (Hex.encode (G.Groups.fifth value) ++ rest))))))))
spellingWithSuffix (G.groups first second third fourth fifth) rest
  rewrite Data.List.Properties.++-assoc (Hex.encode first) ((# 45) ∷ tail2 second third fourth (Hex.encode fifth)) rest |
    Data.List.Properties.++-assoc (Hex.encode second) ((# 45) ∷ tail3 third fourth (Hex.encode fifth)) rest |
    Data.List.Properties.++-assoc (Hex.encode third) ((# 45) ∷ tail4 fourth (Hex.encode fifth)) rest |
    Data.List.Properties.++-assoc (Hex.encode fourth) ((# 45) ∷ Hex.encode fifth) rest = refl

roundTrip : ∀ value rest → read (spell value ++ rest) ≡ just (value , rest)
roundTrip value@(G.groups first second third fourth fifth) rest rewrite spellingWithSuffix value rest |
  Hex.roundTrip first ((# 45) ∷ tail2 second third fourth (Hex.encode fifth ++ rest)) |
  Hex.roundTrip second ((# 45) ∷ tail3 third fourth (Hex.encode fifth ++ rest)) |
  Hex.roundTrip third ((# 45) ∷ tail4 fourth (Hex.encode fifth ++ rest)) |
  Hex.roundTrip fourth ((# 45) ∷ (Hex.encode fifth ++ rest)) | Hex.roundTrip fifth rest = refl

encode : G.UUID → List Byte
encode value = spell (G.split value)

decode : List Byte → Maybe (G.UUID × List Byte)
decode input = read input >>= λ where (value , rest) → just (G.flatten value , rest)

uuidRoundTrip : ∀ value rest → decode (encode value ++ rest) ≡ just (value , rest)
uuidRoundTrip value rest rewrite roundTrip (G.split value) rest | G.flattenSplit value = refl

uuidLength : ∀ value → length (encode value) ≡ 36
uuidLength value = spellingLength (G.split value)

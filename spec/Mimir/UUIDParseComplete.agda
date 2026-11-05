{-# OPTIONS --safe #-}
-- Every admitted spelling is accepted: simple, hyphenated, braced and URN.
-- Completeness and soundness jointly cover rejection as well as acceptance.
module Mimir.UUIDParseComplete where

open import Data.Fin using (#_)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; _++_; length; take; drop)
open import Data.List.Properties using (length-++)
open import Data.Maybe using (just)
open import Data.Nat using (_+_; suc)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.Bits using (Byte)
import Mimir.HexBytes as Hex
import Mimir.UUIDGroups as G
import Mimir.UUIDHyphenated as H
import Mimir.UUIDHyphenatedGrammar as Groups
import Mimir.UUIDParse as P
import Mimir.UUIDParseGrammar as Grammar

regularLength : ∀ {input value} → Grammar.Regular input value → length input ≡ 36
regularLength (Grammar.regular parts meaning exact) = Groups.consumedLength meaning

regularDecoded : ∀ {input value} → Grammar.Regular input value → H.decode input ≡ just (value , [])
regularDecoded (Grammar.regular parts meaning exact) rewrite Groups.complete meaning | exact = refl

regularAccepted : ∀ {input value} → Grammar.Regular input value → P.readHyphenated input ≡ P.accepted value
regularAccepted {input} proof = trans (cong (λ size → P.hyphenatedSized size input) (regularLength proof))
  (cong (P.finish input P.hyphenated) (regularDecoded proof))

prefixLength : ∀ {expected input rest} → Grammar.Prefix expected input rest → length input ≡ length expected + length rest
prefixLength (Grammar.done rest) = refl
prefixLength (Grammar.lower small large byte expected input rest same later) = cong suc (prefixLength later)
prefixLength (Grammar.upper small large byte expected input rest same later) = cong suc (prefixLength later)

prefixComplete : ∀ {expected input rest} → Grammar.Prefix expected input rest → P.prefix expected input ≡ just rest
prefixComplete (Grammar.done rest) = refl
prefixComplete (Grammar.lower small large .small expected input rest refl later) with small Fin.≟ small
... | yes same = prefixComplete later
... | no impossible = ⊥-elim (impossible refl)
prefixComplete (Grammar.upper small large .large expected input rest refl later) with large Fin.≟ small
... | yes same = prefixComplete later
... | no notSmall with large Fin.≟ large
...   | yes same = prefixComplete later
...   | no impossible = ⊥-elim (impossible refl)

takePrefix : ∀ (first second : List Byte) → take (length first) (first ++ second) ≡ first
takePrefix [] second = refl
takePrefix (byte ∷ first) second = cong (byte ∷_) (takePrefix first second)

dropPrefix : ∀ (first second : List Byte) → drop (length first) (first ++ second) ≡ second
dropPrefix [] second = refl
dropPrefix (byte ∷ first) second = dropPrefix first second

takeBody : ∀ body value → Grammar.Regular body value → take 36 (body ++ ((# 125) ∷ [])) ≡ body
takeBody body value proof = trans (cong (λ size → take size (body ++ ((# 125) ∷ []))) (sym (regularLength proof)))
  (takePrefix body ((# 125) ∷ []))

dropBody : ∀ body value → Grammar.Regular body value → drop 36 (body ++ ((# 125) ∷ [])) ≡ (# 125) ∷ []
dropBody body value proof = trans (cong (λ size → drop size (body ++ ((# 125) ∷ []))) (sym (regularLength proof)))
  (dropPrefix body ((# 125) ∷ []))

bracedAccepted : ∀ body value → Grammar.Regular body value →
  P.braced ((# 123) ∷ (body ++ ((# 125) ∷ []))) ≡ P.accepted value
bracedAccepted body value proof rewrite dropBody body value proof | takeBody body value proof = regularAccepted proof

urnAccepted : ∀ input body value → Grammar.Prefix P.urnPrefix input body → Grammar.Regular body value → P.urn input ≡ P.accepted value
urnAccepted input body value prefix proof rewrite prefixComplete prefix = regularAccepted proof

complete : ∀ {input value} → Grammar.Accepted input value → P.read input ≡ P.accepted value
complete {input} (Grammar.simple proof) = trans (cong (λ size → P.readSized size input) (Hex.consumedLength proof))
  (cong (P.finish input P.any) (Hex.complete proof))
complete {input} (Grammar.hyphenated proof) = trans (cong (λ size → P.readSized size input) (regularLength proof)) (regularAccepted proof)
complete {value = value} (Grammar.braced body refl proof) = trans
  (cong (λ size → P.readSized size ((# 123) ∷ (body ++ ((# 125) ∷ []))))
    (cong suc (trans (length-++ body {ys = (# 125) ∷ []}) (cong (_+ 1) (regularLength proof)))))
  (bracedAccepted body value proof)
complete {input} {value} (Grammar.urn body prefix proof) = trans
  (cong (λ size → P.readSized size input) (trans (prefixLength prefix) (cong (9 +_) (regularLength proof))))
  (urnAccepted input body value prefix proof)

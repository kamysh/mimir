{-# OPTIONS --safe #-}
-- Lexical scanning precedes assembled UTF-8 validation, preserving error
-- precedence between malformed escapes/control bytes and invalid raw UTF-8.
module Mimir.JsonStringParser where

open import Data.Fin using (#_; toℕ; _≟_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (++-assoc; length-++-≤ʳ; length-++-≤ˡ)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_; s≤s⁻¹; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.Bits using (Byte)
import Mimir.ByteCursor as Cursor
import Mimir.JsonString as Grammar
import Mimir.JsonEscape as Escape
import Mimir.JsonEscapeParser as Escapes
import Mimir.UTF8Text as UTF8
import Mimir.UTF8Packet as Packet

data Code : Set where
  eofString controlCharacter expectedQuote : Code
  escapeError : Escapes.Code → Code
  invalidUnicode : Packet.Error → Code

module Fault = Cursor.WithCode Code
open Fault using (Failure; failed)

record BodyParsed (input : List Byte) : Set where
  constructor bodyParsed
  field
    body : Grammar.Body
    valid : Grammar.ValidBody body
    rest : List Byte
    exact : input ≡ Grammar.spellBody body ++ rest

escapeFailure : ∀ {input} → Escapes.Fault.Failure input → Failure input
escapeFailure (Escapes.Fault.failed code consumed remaining exact) = failed (escapeError code) consumed remaining exact

escapeSuffixBound : ∀ fuel {input} (result : Escapes.Parsed input) → length input ≤ fuel →
  length (Escapes.Parsed.rest result) ≤ fuel
escapeSuffixBound fuel (Escapes.parsed raw valid rest refl) bound =
  ≤-trans (length-++-≤ʳ rest {xs = Escape.spell raw}) bound

prepend : ∀ atom → Grammar.Valid atom → ∀ {input suffix} → input ≡ Grammar.spell atom ++ suffix →
  BodyParsed suffix → BodyParsed input
prepend atom valid exact (bodyParsed body admitted rest bodyExact) =
  bodyParsed (atom ∷ body) (valid All.∷ admitted) rest
    (trans exact (trans (cong (Grammar.spell atom ++_) bodyExact)
      (sym (++-assoc (Grammar.spell atom) (Grammar.spellBody body) rest))))

continue : ∀ atom → Grammar.Valid atom → ∀ {input suffix} → input ≡ Grammar.spell atom ++ suffix →
  Failure suffix ⊎ BodyParsed suffix → Failure input ⊎ BodyParsed input
continue atom valid exact (inj₁ failure) = inj₁ (Fault.reframe exact (Fault.prefix (Grammar.spell atom) failure))
continue atom valid exact (inj₂ result) = inj₂ (prepend atom valid exact result)

readBounded : ∀ fuel input → length input ≤ fuel → Failure input ⊎ BodyParsed input
readBounded fuel [] bound = inj₁ (Fault.end [] eofString)
readBounded zero (byte ∷ input) ()
readBounded (suc fuel) (byte ∷ input) bound with byte ≟ (# 34)
... | yes refl = inj₂ (bodyParsed [] All.[] input refl)
... | no notQuote with byte ≟ (# 92)
...   | yes refl with Escapes.parse input
...     | inj₁ failure = inj₁ (Fault.prefix ((# 92) ∷ []) (escapeFailure failure))
...     | inj₂ result = continue (Grammar.escaped (Escapes.Parsed.raw result)) (Escapes.Parsed.valid result)
        (cong ((# 92) ∷_) (Escapes.Parsed.exact result))
        (readBounded fuel (Escapes.Parsed.rest result) (escapeSuffixBound fuel result (s≤s⁻¹ bound)))
readBounded (suc fuel) (byte ∷ input) bound | no notQuote | no notSlash with 32 ≤? toℕ byte
... | no _ = inj₁ (failed controlCharacter (byte ∷ []) input refl)
... | yes large = continue (Grammar.literal byte) (large , notQuote , notSlash) refl
    (readBounded fuel input (s≤s⁻¹ bound))

readBody : ∀ input → Failure input ⊎ BodyParsed input
readBody input = readBounded (length input) input ≤-refl

record Parsed (input : List Byte) : Set where
  constructor parsed
  field
    value : Grammar.StringValue
    rest : List Byte
    exact : input ≡ Grammar.spellString (Grammar.StringValue.body value) ++ rest

finish : ∀ {input} → BodyParsed input → Failure ((# 34) ∷ input) ⊎ Parsed ((# 34) ∷ input)
finish (bodyParsed body valid rest exact) with UTF8.decode (Grammar.bodyOutput body valid)
... | inj₁ failure = inj₁ (failed (invalidUnicode failure) (Grammar.spellString body) rest (cong ((# 34) ∷_) exact))
... | inj₂ decodedValue = inj₂ (parsed (Grammar.stringValue body valid decodedValue) rest (cong ((# 34) ∷_) exact))

parse : ∀ input → Failure input ⊎ Parsed input
parse [] = inj₁ (Fault.end [] expectedQuote)
parse (first ∷ rest) with first ≟ (# 34)
... | no _ = inj₁ (failed expectedQuote [] (first ∷ rest) refl)
... | yes refl with readBody rest
...   | inj₁ failure = inj₁ (Fault.prefix ((# 34) ∷ []) failure)
...   | inj₂ result = finish result

bodyPositive : ∀ body rest → 1 ≤ length (Grammar.spellBody body ++ rest)
bodyPositive [] rest = s≤s z≤n
bodyPositive (Grammar.literal byte ∷ body) rest = s≤s z≤n
bodyPositive (Grammar.escaped raw ∷ body) rest = s≤s z≤n

oneNotZero : 1 ≤ 0 → ⊥
oneNotZero ()

BodySuccess : ∀ fuel body rest → length (Grammar.spellBody body ++ rest) ≤ fuel → Set
BodySuccess fuel body rest bound = Σ (BodyParsed (Grammar.spellBody body ++ rest)) (λ result →
  readBounded fuel (Grammar.spellBody body ++ rest) bound ≡ inj₂ result ×
  (BodyParsed.body result ≡ body × BodyParsed.rest result ≡ rest))

bodyComplete : ∀ fuel body → Grammar.ValidBody body → ∀ rest bound → BodySuccess fuel body rest bound
bodyComplete zero body valid rest bound = ⊥-elim (oneNotZero (≤-trans (bodyPositive body rest) bound))
bodyComplete (suc fuel) [] All.[] rest bound = bodyParsed [] All.[] rest refl , refl , refl , refl
bodyComplete (suc fuel) (Grammar.literal byte ∷ body) ((low , notQuote , notSlash) All.∷ valid) rest bound
  with byte ≟ (# 34)
... | yes same = ⊥-elim (notQuote same)
... | no checkedQuote with byte ≟ (# 92)
...   | yes same = ⊥-elim (notSlash same)
...   | no checkedSlash with 32 ≤? toℕ byte
...     | no rejected = ⊥-elim (rejected low)
...     | yes checkedLow with bodyComplete fuel body valid rest (s≤s⁻¹ bound)
...       | bodyParsed .body checked .rest exact , observed , refl , refl
            rewrite observed = _ , refl , refl , refl
bodyComplete (suc fuel) (Grammar.escaped raw ∷ body) (admitted All.∷ valid) rest bound
  rewrite ++-assoc (Escape.spell raw) (Grammar.spellBody body) rest
  with Escapes.parseComplete raw admitted (Grammar.spellBody body ++ rest)
... | Escapes.parsed .raw checked .(Grammar.spellBody body ++ rest) exact , observed , refl , refl
  with bodyComplete fuel body valid rest
    (escapeSuffixBound fuel (Escapes.parsed raw checked (Grammar.spellBody body ++ rest) exact) (s≤s⁻¹ bound))
...   | bodyParsed .body checkedBody .rest bodyExact , bodyObserved , refl , refl
        rewrite observed | bodyObserved = _ , refl , refl , refl

readBodyComplete : ∀ body → Grammar.ValidBody body → ∀ rest →
  Σ (BodyParsed (Grammar.spellBody body ++ rest)) (λ result →
    readBody (Grammar.spellBody body ++ rest) ≡ inj₂ result ×
    (BodyParsed.body result ≡ body × BodyParsed.rest result ≡ rest))
readBodyComplete body valid rest = bodyComplete (length (Grammar.spellBody body ++ rest)) body valid rest ≤-refl

finishComplete : ∀ {input} (body : BodyParsed input)
  (expected : UTF8.Decoded (Grammar.bodyOutput (BodyParsed.body body) (BodyParsed.valid body))) →
  Σ (Parsed ((# 34) ∷ input)) (λ result → finish body ≡ inj₂ result ×
    (Grammar.StringValue.body (Parsed.value result) ≡ BodyParsed.body body ×
      (Parsed.rest result ≡ BodyParsed.rest body ×
        map Packet.Scalar.raw (Grammar.values (Parsed.value result)) ≡ map Packet.Scalar.raw (UTF8.Decoded.values expected))))
finishComplete (bodyParsed body valid rest exact) expected with UTF8.decodeGiven expected
... | actual , observed , same rewrite observed = _ , refl , refl , refl , same

parseComplete : ∀ value rest →
  Σ (Parsed (Grammar.spellString (Grammar.StringValue.body value) ++ rest)) (λ result →
    parse (Grammar.spellString (Grammar.StringValue.body value) ++ rest) ≡ inj₂ result ×
    (Grammar.StringValue.body (Parsed.value result) ≡ Grammar.StringValue.body value ×
      (Parsed.rest result ≡ rest ×
        map Packet.Scalar.raw (Grammar.values (Parsed.value result)) ≡ map Packet.Scalar.raw (Grammar.values value))))
parseComplete (Grammar.stringValue body valid (UTF8.decoded values bytesExact)) rest
  with readBodyComplete body valid rest
... | bodyParsed .body checked .rest exact , observed , refl , refl
  with finishComplete (bodyParsed body checked rest exact)
    (UTF8.decoded values (trans (sym (Grammar.bodyOutputIndependent body valid checked)) bytesExact))
...   | result , finished , sameBody , sameRest , sameValues rewrite observed | finished =
        result , refl , sameBody , sameRest , sameValues

{-# OPTIONS --safe #-}
-- Concrete 32-bit compression. Byte framing and hash finalization are
-- deliberately separate obligations; this module does not claim to hash text.
module Mimir.SHA256Core where

open import Data.Vec using (Vec; []; _∷_; _++_; map; zipWith)
open import Data.Nat using (NonZero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Word; module Binary)
open import Mimir.BitLogic using (wordXor; wordChoose; wordMajority)
open import Mimir.WordShifts using (right; rotateRight)
import Mimir.WordAddition as Addition
import Mimir.WordEncoding as Encoding
import Mimir.SHA256Constants as Constants
import Mimir.SHA256Schedule as Schedule
import Mimir.SHA256Compression as Compression

W = Word 32

instance
  wordModulusPositive : NonZero (Binary.power 32)
  wordModulusPositive = Encoding.powerPositive 32

bigSigma0 bigSigma1 sigma0 sigma1 : W → W
bigSigma0 word = wordXor (wordXor (rotateRight 2 word) (rotateRight 13 word)) (rotateRight 22 word)
bigSigma1 word = wordXor (wordXor (rotateRight 6 word) (rotateRight 11 word)) (rotateRight 25 word)
sigma0 word = wordXor (wordXor (rotateRight 7 word) (rotateRight 18 word)) (right 3 word)
sigma1 word = wordXor (wordXor (rotateRight 17 word) (rotateRight 19 word)) (right 10 word)

module S = Schedule.Schedule W Addition.add sigma0 sigma1
module C = Compression.Compression W Addition.add Addition.associative Addition.commutative
  bigSigma0 bigSigma1 wordChoose wordMajority
open C.R public using (State; state)

fromWords : Vec W 8 → State
fromWords (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = state a b c d e f g h

toWords : State → Vec W 8
toWords (state a b c d e f g h) = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []

stateRoundTrip : ∀ stateValue → fromWords (toWords stateValue) ≡ stateValue
stateRoundTrip (state a b c d e f g h) = refl

wordsRoundTrip : ∀ words → toWords (fromWords words) ≡ words
wordsRoundTrip (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl

initial : State
initial = fromWords (map (Encoding.encode 32) Constants.initialState)

roundConstants : Vec W 64
roundConstants = map (Encoding.encode 32) Constants.roundConstants

schedule : S.Block → Vec W 64
schedule block = block ++ S.generate 48 block

addends : S.Block → Vec W 64
addends block = zipWith Addition.add (schedule block) roundConstants

compress compressGrouped : S.Block → State → State
compress block = C.compress (addends block)
compressGrouped block = C.compressGrouped (addends block)

compressionEquivalent : ∀ block stateValue → compressGrouped block stateValue ≡ compress block stateValue
compressionEquivalent block stateValue = C.compressionEquivalent (addends block) stateValue

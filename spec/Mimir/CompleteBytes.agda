{-# OPTIONS --safe #-}
-- Complete streamed bodies; chunk size and total body length do not decide
-- success. End-of-stream publishes every received byte in its original order.
module Mimir.CompleteBytes where
open import Data.List using (List; []; _∷_; _++_; concat)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Mimir.Framing using (Byte)

record Buffer : Set where
  constructor buffer
  field bytes : List Byte

data Error : Set where transport : Error
data State : Set where
  receiving complete : Buffer → State
  failed : Error → State
data Input : Set where chunk : List Byte → Input; end ioFailure : Input
begin : State
begin = receiving (buffer [])
step : State → Input → State
step (receiving before) (chunk next) = receiving (buffer (Buffer.bytes before ++ next))
step (receiving before) end = complete before
step (receiving before) ioFailure = failed transport
step (complete before) _ = complete before
step (failed error) _ = failed error

appendAll : List Byte → List (List Byte) → List Byte
appendAll before [] = before
appendAll before (part ∷ rest) = appendAll (before ++ part) rest

allBytesPreserved : ∀ before parts → appendAll before parts ≡ before ++ concat parts
allBytesPreserved before [] = sym (++-identityʳ before)
allBytesPreserved before (part ∷ rest) = trans (allBytesPreserved (before ++ part) rest) (++-assoc before part (concat rest))

noChunkRefused : ∀ before part → step (receiving before) (chunk part) ≡ receiving (buffer (Buffer.bytes before ++ part))
noChunkRefused before part = refl

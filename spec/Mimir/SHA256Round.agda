{-# OPTIONS --safe #-}
-- Round scheduling equivalence over arbitrary words with explicitly supplied,
-- proved addition laws. No cryptographic collision assumption is required.
module Mimir.SHA256Round where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

module Rounds (Word : Set) (add : Word → Word → Word)
  (associative : ∀ a b c → add (add a b) c ≡ add a (add b c))
  (commutative : ∀ a b → add a b ≡ add b a)
  (bigSigma0 bigSigma1 : Word → Word)
  (choose majority : Word → Word → Word → Word) where

  record State : Set where
    constructor state
    field a b c d e f g h : Word
  open State

  record Quad : Set where
    constructor quad
    field first second third fourth : Word

  abef cdgh : State → Quad
  abef s = quad (a s) (b s) (e s) (f s)
  cdgh s = quad (c s) (d s) (g s) (h s)

  standardT1 sourceT1 : State → Word → Word
  standardT1 s wk = add (add (add (h s) (bigSigma1 (e s))) (choose (e s) (f s) (g s))) wk
  sourceT1 s wk = add (add (add (bigSigma1 (e s)) (choose (e s) (f s) (g s))) wk) (h s)

  cycle4 : ∀ a b c d → add (add (add a b) c) d ≡ add (add (add d a) b) c
  cycle4 a b c d = trans (commutative (add (add a b) c) d)
    (trans (sym (associative d (add a b) c)) (cong (λ value → add value c) (sym (associative d a b))))

  t1Equivalent : ∀ s wk → sourceT1 s wk ≡ standardT1 s wk
  t1Equivalent s wk = cycle4 (bigSigma1 (e s)) (choose (e s) (f s) (g s)) wk (h s)

  stepWith : Word → State → State
  stepWith t1 s = state (add t1 (add (bigSigma0 (a s)) (majority (a s) (b s) (c s))))
    (a s) (b s) (c s) (add t1 (d s)) (e s) (f s) (g s)

  standard source : Word → State → State
  standard wk s = stepWith (standardT1 s wk) s
  source wk s = stepWith (sourceT1 s wk) s

  roundEquivalent : ∀ s wk → source wk s ≡ standard wk s
  roundEquivalent s wk = cong (λ t1 → stepWith t1 s) (t1Equivalent s wk)

  -- Transcription of sha256_digest_round_x2: wk0 is the fourth lane and wk1
  -- the third lane. The discarded C/D/G/H outputs are recovered by swapping
  -- the two quad roles at the next call, as in rounds4!.
  two : Quad → Quad → Word → Word → Quad
  two (quad c0 d0 g0 h0) (quad a0 b0 e0 f0) wk0 wk1 = quad a2 a1 e2 e1
    where
    x0 = add (add (add (bigSigma1 e0) (choose e0 f0 g0)) wk0) h0
    y0 = add (bigSigma0 a0) (majority a0 b0 c0)
    a1 = add x0 y0
    e1 = add x0 d0
    x1 = add (add (add (bigSigma1 e1) (choose e1 e0 f0)) wk1) g0
    y1 = add (bigSigma0 a1) (majority a1 a0 b0)
    a2 = add x1 y1
    e2 = add x1 c0

  twoSource : ∀ s wk0 wk1 → two (cdgh s) (abef s) wk0 wk1 ≡ abef (source wk1 (source wk0 s))
  twoSource (state a b c d e f g h) wk0 wk1 = refl

  twoStandard : ∀ s wk0 wk1 → two (cdgh s) (abef s) wk0 wk1 ≡ abef (standard wk1 (standard wk0 s))
  twoStandard s wk0 wk1 = trans (twoSource s wk0 wk1)
    (cong abef (trans (roundEquivalent (source wk0 s) wk1)
      (cong (standard wk1) (roundEquivalent s wk0))))

  twoRetainsOther : ∀ s wk0 wk1 → cdgh (source wk1 (source wk0 s)) ≡ abef s
  twoRetainsOther (state a b c d e f g h) wk0 wk1 = refl

  four : State → Word → Word → Word → Word → State
  four s wk0 wk1 wk2 wk3 with two (cdgh s) (abef s) wk0 wk1
  ... | firstPair with two (abef s) firstPair wk2 wk3
  ...   | secondPair = state (Quad.first secondPair) (Quad.second secondPair)
    (Quad.first firstPair) (Quad.second firstPair)
    (Quad.third secondPair) (Quad.fourth secondPair)
    (Quad.third firstPair) (Quad.fourth firstPair)

  fourSource : ∀ s wk0 wk1 wk2 wk3 →
    four s wk0 wk1 wk2 wk3 ≡ source wk3 (source wk2 (source wk1 (source wk0 s)))
  fourSource (state a b c d e f g h) wk0 wk1 wk2 wk3 = refl

  fourStandard : ∀ s wk0 wk1 wk2 wk3 →
    four s wk0 wk1 wk2 wk3 ≡ standard wk3 (standard wk2 (standard wk1 (standard wk0 s)))
  fourStandard s wk0 wk1 wk2 wk3 = trans (fourSource s wk0 wk1 wk2 wk3)
    (trans (roundEquivalent (source wk2 (source wk1 (source wk0 s))) wk3)
    (cong (standard wk3) (trans (roundEquivalent (source wk1 (source wk0 s)) wk2)
    (cong (standard wk2) (trans (roundEquivalent (source wk0 s) wk1)
      (cong (standard wk1) (roundEquivalent s wk0)))))))

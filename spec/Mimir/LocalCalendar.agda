{-# OPTIONS --safe #-}
-- Supplied local clock/calendar meaning. No timezone database, date parser
-- or formatter is implemented or proved here.
module Mimir.LocalCalendar where

open import Data.Fin using (Fin; toℕ; #_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Nat.DivMod using (_/_)
open import Data.Integer using (ℤ; +_; _+_; _*_; _≤_; _<_; _⊓_)
open import Data.Integer.DivMod using (_/ℕ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Mimir.Text using (Text)

record Local : Set where
  constructor local
  field day : ℤ; secondOfDay : Fin 86400; offsetSeconds : ℤ

data Midnight : Set where
  unavailable : Midnight
  single : ℤ → Midnight
  ambiguous : ℤ → ℤ → Midnight

earliest : Midnight → Maybe ℤ
earliest unavailable = nothing
earliest (single instant) = just instant
earliest (ambiguous first second) = just (first ⊓ second)

record Calendar : Set where
  field
    minimumDay maximumDay : ℤ
    parse : Text → Maybe ℤ
    showDay : ℤ → Text
    -- All operations use the same computer-local timezone rules. The offset
    -- formatter faithfully renders its argument; it supplies the label only.
    localAt : ℤ → Local -- UTC nanoseconds, also the stored-history time unit
    showOffset : ℤ → Text
    midnights : ℤ → Midnight -- UTC nanoseconds for the local date

  midnight : ℤ → Maybe ℤ
  midnight day = earliest (midnights day)

  field
    -- One UTC instant, local date/time and effective offset must agree.
    localMeaning : ∀ instant →
      (instant /ℕ 1000000000) + Local.offsetSeconds (localAt instant) ≡
      Local.day (localAt instant) * + 86400 + (+ toℕ (Local.secondOfDay (localAt instant)))
    shownDate : ∀ day → minimumDay ≤ day → day ≤ maximumDay → parse (showDay day) ≡ just day
    midnightRange : ∀ day instant → midnight day ≡ just instant → minimumDay ≤ day × day ≤ maximumDay
    midnightMeaning : ∀ day instant → midnight day ≡ just instant →
      Local.day (localAt instant) ≡ day × Local.secondOfDay (localAt instant) ≡ (# 0)
    consecutiveMidnights : ∀ day start end → midnight day ≡ just start → midnight (day + + 1) ≡ just end → start < end
    -- A successful interval is exactly that local date under the same zone
    -- rules. This is a supplied calendar guarantee, not a timezone proof.
    dayMembership : ∀ day start end instant → midnight day ≡ just start → midnight (day + + 1) ≡ just end →
      (((start ≤ instant) × (instant < end)) → Local.day (localAt instant) ≡ day) ×
      ((Local.day (localAt instant) ≡ day) → (start ≤ instant) × (instant < end))

-- The clock supplies one timestamp. Day, hour and displayed timezone cannot
-- be independently selected or taken from separate reads.
record Now : Set where
  constructor timeSample
  field unixSeconds : ℕ

instant : Now → ℤ
instant now = (+ Now.unixSeconds now) * + 1000000000

sample : Calendar → Now → Local
sample calendar now = Calendar.localAt calendar (instant now)

localDay : Calendar → Now → ℤ
localDay calendar now = Local.day (sample calendar now)

localHour : Calendar → Now → ℕ
localHour calendar now = toℕ (Local.secondOfDay (sample calendar now)) / 3600

localZone : Calendar → Now → Text
localZone calendar now = Calendar.showOffset calendar (Local.offsetSeconds (sample calendar now))

sampleMeansOneInstant : ∀ calendar now →
  (instant now /ℕ 1000000000) + Local.offsetSeconds (sample calendar now) ≡
  localDay calendar now * + 86400 + (+ toℕ (Local.secondOfDay (sample calendar now)))
sampleMeansOneInstant calendar now = Calendar.localMeaning calendar (instant now)

record Window (calendar : Calendar) (day : ℤ) : Set where
  constructor window
  field
    start end : ℤ
    startsAtMidnight : Calendar.midnight calendar day ≡ just start
    endsAtNextMidnight : Calendar.midnight calendar (day + + 1) ≡ just end

windowFor : ∀ calendar day → Maybe (Window calendar day)
windowFor calendar day with Calendar.midnight calendar day in startAt
  | Calendar.midnight calendar (day + + 1) in endAt
... | just start | just end = just (window start end startAt endAt)
... | _ | _ = nothing

windowLabel : ∀ {calendar day} → Window calendar day → Calendar.parse calendar (Calendar.showDay calendar day) ≡ just day
windowLabel {calendar} {day} range = Calendar.shownDate calendar day lower upper
  where
  bounds = Calendar.midnightRange calendar day (Window.start range) (Window.startsAtMidnight range)
  lower = Data.Product.proj₁ bounds
  upper = Data.Product.proj₂ bounds

windowDates : ∀ {calendar day} (range : Window calendar day) →
  Local.day (Calendar.localAt calendar (Window.start range)) ≡ day ×
  Local.day (Calendar.localAt calendar (Window.end range)) ≡ day + + 1
windowDates {calendar} {day} range =
  Data.Product.proj₁ (Calendar.midnightMeaning calendar day (Window.start range) (Window.startsAtMidnight range)) ,
  Data.Product.proj₁ (Calendar.midnightMeaning calendar (day + + 1) (Window.end range) (Window.endsAtNextMidnight range))

windowOrdered : ∀ {calendar day} (range : Window calendar day) → Window.start range < Window.end range
windowOrdered {calendar} {day} range = Calendar.consecutiveMidnights calendar day
  (Window.start range) (Window.end range) (Window.startsAtMidnight range) (Window.endsAtNextMidnight range)

windowContainsExactlyDay : ∀ {calendar day} (range : Window calendar day) instant →
  (((Window.start range ≤ instant) × (instant < Window.end range)) → Local.day (Calendar.localAt calendar instant) ≡ day) ×
  ((Local.day (Calendar.localAt calendar instant) ≡ day) → (Window.start range ≤ instant) × (instant < Window.end range))
windowContainsExactlyDay {calendar} {day} range instant = Calendar.dayMembership calendar day
  (Window.start range) (Window.end range) instant (Window.startsAtMidnight range) (Window.endsAtNextMidnight range)

ambiguousUsesEarliest : ∀ first second → earliest (ambiguous first second) ≡ just (first ⊓ second)
ambiguousUsesEarliest first second = refl

adjacentWindowsMeet : ∀ {calendar day} (first : Window calendar day) (second : Window calendar (day + + 1)) →
  Window.end first ≡ Window.start second
adjacentWindowsMeet first second = just-injective
  (trans (sym (Window.endsAtNextMidnight first)) (Window.startsAtMidnight second))

missingStartRefused : ∀ calendar day → Calendar.midnight calendar day ≡ nothing → windowFor calendar day ≡ nothing
missingStartRefused calendar day absent with windowFor calendar day
... | nothing = refl
... | just range = ⊥-elim (impossible (trans (sym absent) (Window.startsAtMidnight range)))
  where
  impossible : nothing ≡ just (Window.start range) → ⊥
  impossible ()

missingEndRefused : ∀ calendar day → Calendar.midnight calendar (day + + 1) ≡ nothing → windowFor calendar day ≡ nothing
missingEndRefused calendar day absent with windowFor calendar day
... | nothing = refl
... | just range = ⊥-elim (impossible (trans (sym absent) (Window.endsAtNextMidnight range)))
  where
  impossible : nothing ≡ just (Window.end range) → ⊥
  impossible ()

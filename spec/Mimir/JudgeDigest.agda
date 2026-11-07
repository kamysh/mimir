{-# OPTIONS --safe #-}
-- Daily database-wide digest: user-configured local boundary, calendar catch-up,
-- repeatable-read read-only query sequence, then durable notification cursor.
module Mimir.JudgeDigest where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; length; filterᵇ; replicate)
open import Data.List.Relation.Unary.Any using (Any; here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤?_)
open import Data.Integer using (ℤ; +_; _+_; _-_; _<?_; _≤?_; _≟_)
import Data.Integer as Integer
import Data.Integer.Show as IntegerShow
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.LearningHistoryWire as Ledger
import Mimir.StructuredValue as V
import Mimir.JudgeScopedTools as Fields
import Mimir.SignedMachine as Signed
import Mimir.JudgeHost as Host
import Mimir.OperationalDiagnostics as Diagnostics
import Mimir.JudgeConfiguration as Config
import Mimir.NotificationConfig as Email
import Mimir.DigestDelivery as Delivery
import Mimir.NotificationIncident as Notification
import Mimir.UnixPath as Path
import Mimir.Effects as Effects
open import Mimir.LocalCalendar public using (Calendar; Now; localDay; localHour; localZone)
import Mimir.LocalCalendar as Local
import Data.Fin
import Data.Empty

reportSecond : Config.DailyTime → ℕ
reportSecond time = Config.DailyTime.hour time Data.Nat.* 3600 Data.Nat.+ Config.DailyTime.minute time Data.Nat.* 60

-- Queue admission is remembered independently of delivery. A pending SMTP
-- call therefore cannot cause the calendar owner to enqueue the same day again.
module CalendarAdmission where
  offer : ℤ → Maybe ℤ → Maybe ℤ
  offer today nothing = just today
  offer today (just previous) with today ≟ previous
  ... | yes _ = nothing
  ... | no _ = just today

  admittedDayIsNotOfferedAgain : ∀ day → offer day (just day) ≡ nothing
  admittedDayIsNotOfferedAgain day with day ≟ day
  ... | yes _ = refl
  ... | no different = Data.Empty.⊥-elim (different refl)

record Counts : Set where
  constructor counts
  field newExperiences sourceRevisions judgeReviews : ℤ

record CountedDay (calendar : Calendar) : Set where
  constructor countedDay
  field day : ℤ; range : Local.Window calendar day; observed : Counts

countedDayLabel : ∀ {calendar} (row : CountedDay calendar) →
  Calendar.parse calendar (Calendar.showDay calendar (CountedDay.day row)) ≡ just (CountedDay.day row)
countedDayLabel row = Local.windowLabel (CountedDay.range row)

within : ℤ → ℤ → Ledger.Row → Bool
within start end reviewRow = does (start Integer.≤? Ledger.Row.createdAt reviewRow) ∧ does (Ledger.Row.createdAt reviewRow <? end)

withinMatchesDisplayedDay : ∀ calendar day (range : Local.Window calendar day) storedRow →
  within (Local.Window.start range) (Local.Window.end range) storedRow ≡ true →
  Local.Local.day (Calendar.localAt calendar (Ledger.Row.createdAt storedRow)) ≡ day
withinMatchesDisplayedDay calendar day range storedRow observed
  with Local.Window.start range Integer.≤? Ledger.Row.createdAt storedRow | Ledger.Row.createdAt storedRow <? Local.Window.end range
... | yes lower | yes upper = Data.Product.proj₁ (Local.windowContainsExactlyDay range (Ledger.Row.createdAt storedRow)) (lower , upper)
... | no different | _ with observed
...   | ()
withinMatchesDisplayedDay calendar day range storedRow observed | yes lower | no different with observed
... | ()

selectedCounts : Ledger.Database → ℤ → ℤ → Counts
selectedCounts db start end = counts
  (+ length (filterᵇ (λ reviewRow → within start end reviewRow ∧ does (Ledger.Row.revision reviewRow ≟ + 1)) (Ledger.Database.sourceRows db)))
  (+ length (filterᵇ (λ reviewRow → within start end reviewRow ∧ does (+ 1 <? Ledger.Row.revision reviewRow)) (Ledger.Database.sourceRows db)))
  (+ length (filterᵇ (λ reviewRow → within start end reviewRow ∧
    Fields.textIs (toList "mimir-judge") (Fields.get "reviewer" (Ledger.Row.payload reviewRow))) (Ledger.Database.reviewRows db)))

backlog : Ledger.Database → ℤ
backlog db = + length (filterᵇ (λ header → does (Ledger.Head.reviewedRevision header <? Ledger.Head.revision header))
  (Ledger.Database.heads db))

module I64 = Signed.Width 63
add : Counts → Counts → Counts
add first second = counts (I64.wrapValue (Counts.newExperiences first + Counts.newExperiences second))
  (I64.wrapValue (Counts.sourceRevisions first + Counts.sourceRevisions second))
  (I64.wrapValue (Counts.judgeReviews first + Counts.judgeReviews second))

number : ℤ → Text
number value = toList (IntegerShow.show value)
pad : ℕ → Text → Text
pad width value = replicate (width ∸ length value) ' ' ++ value

latestStatus : Host.Outcome → Text
latestStatus run with Host.Outcome.degraded run
... | true = toList "needs attention"
... | false with Host.Outcome.idle run
...   | true = toList "idle"
...   | false with Host.Outcome.exit run
...     | Host.success = toList "batch complete"
...     | _ = toList "unavailable"

rows : ∀ calendar → List (CountedDay calendar) → Counts → Text
rows calendar [] cumulative = []
rows calendar (countedDay day range daily ∷ remaining) cumulative = Calendar.showDay calendar day ++ toList "   " ++
  pad 15 (number (Counts.newExperiences daily)) ++ toList "  " ++
  pad 16 (number (Counts.sourceRevisions daily)) ++ toList "  " ++
  pad 13 (number (Counts.judgeReviews daily)) ++ toList "  " ++
  number (Counts.newExperiences updated) ++ toList " / " ++ number (Counts.sourceRevisions updated) ++
  toList " / " ++ number (Counts.judgeReviews updated) ++ toList "\n" ++ rows calendar remaining updated
  where updated = add cumulative daily

render : ∀ calendar → List (CountedDay calendar) → Counts → ℤ → Host.Outcome → Text → Text
render calendar daily cumulative pending run zone =
  toList "Mimir judge daily statistics\nCalendar days use this computer's local time (" ++ zone ++
  toList ").\nCounts come from the configured Mimir database.\n\nDate         New experiences  Source revisions  Judge reviews  Running totals (new / revisions / reviews)\n" ++
  rows calendar daily cumulative ++ toList "\nCurrent review backlog: " ++ number pending ++
  toList "\nLatest watcher status: " ++ latestStatus run ++
  toList "\n\nSource revisions count stored updates to experiences. They are distinct from the per-run 'corrected' status counter.\n"

data Effect : Set where
  localNow resolveState : Effect
  readReport : Path.Path → Effect
  readCursor : Email.Config → Path.Path → Effect
  connect : Config.Runtime → Effect
  beginReadOnlyRepeatable close : ℕ → Effect
  countBetween : ℕ → ℤ → ℤ → Effect
  countBacklog commit : ℕ → Effect
  send : Config.Runtime → Path.Path → Delivery.Digest → Effect

Reply : Effect → Set
Reply localNow = Now
Reply resolveState = Text ⊎ Path.Path
Reply (readReport _) = Maybe Diagnostics.R.Report
Reply (readCursor _ _) = Text ⊎ Delivery.Cursor
Reply (connect _) = Text ⊎ ℕ
Reply (beginReadOnlyRepeatable _) = Text ⊎ ⊤
Reply (close _) = ⊤
Reply (countBetween _ _ _) = Text ⊎ Counts
Reply (countBacklog _) = Text ⊎ ℤ
Reply (commit _) = Text ⊎ ⊤
Reply (send _ _ _) = Text ⊎ Notification.Outcome
open Effects.Protocol Effect Reply public

module Run (calendar : Calendar) where
  countDay : ∀ connection day → Local.Window calendar day → Script (Text ⊎ CountedDay calendar)
  countDay connection day range = ask (countBetween connection (Local.Window.start range) (Local.Window.end range)) λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ observed) → done (inj₂ (countedDay day range observed))

  -- A returned row retains the very calendar interval used by its query.
  countDayUsesItsWindow : ∀ connection day range events observed →
    Runs (countDay connection day range) events (inj₂ observed) →
    CountedDay.day observed ≡ day ×
    Local.Window.start (CountedDay.range observed) ≡ Local.Window.start range ×
    Local.Window.end (CountedDay.range observed) ≡ Local.Window.end range ×
    Any (_≡ (countBetween connection (Local.Window.start range) (Local.Window.end range) ,
      inj₂ (CountedDay.observed observed))) events
  countDayUsesItsWindow connection day range events observed (replied _ _ (inj₁ error) ())
  countDayUsesItsWindow connection day range events observed (replied _ _ (inj₂ counted) (returned _)) =
    refl , refl , refl , here refl

  next : ℤ → Text ⊎ ℤ
  next day with day <? Calendar.maximumDay calendar
  ... | yes _ = inj₂ (day + + 1)
  ... | no _ = inj₁ (toList "digest date overflow")

  first : Maybe Text → ℤ → Text ⊎ Maybe ℤ
  first nothing through = inj₂ (just through)
  first (just text) through with Calendar.parse calendar text
  ... | nothing = inj₁ (toList "invalid digest date")
  ... | just day with next day
  ...   | inj₁ error = inj₁ error
  ...   | inj₂ following with following Integer.≤? through
  ...     | yes _ = inj₂ (just following)
  ...     | no _ = inj₂ nothing

  daily : ℕ → ℕ → ℤ → Script (Text ⊎ List (CountedDay calendar))
  daily connection zero day = done (inj₂ [])
  daily connection (suc remaining) day with next day
  ... | inj₁ error = done (inj₁ error)
  ... | inj₂ following with Local.windowFor calendar day
  ...   | nothing = done (inj₁ (toList "local midnight is unavailable"))
  ...   | just range = countDay connection day range >>= λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ observed) → daily connection remaining following >>= λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ rest) → done (inj₂ (observed ∷ rest))

  unavailableDayCannotQuery : ∀ connection remaining day following → next day ≡ inj₂ following →
    Local.windowFor calendar day ≡ nothing →
    daily connection (suc remaining) day ≡ done (inj₁ (toList "local midnight is unavailable"))
  unavailableDayCannotQuery connection remaining day following nextDay absent rewrite nextDay | absent = refl

  afterBaseline : ℕ → ℤ → ℤ → Host.Outcome → Text → Reply (countBetween 0 (+ 0) (+ 0)) → Script (Text ⊎ Text)
  afterBaseline connection first through run zone (inj₁ error) = done (inj₁ error)
  afterBaseline connection first through run zone (inj₂ baseline) =
    daily connection (suc (Integer.∣ through - first ∣)) first >>= λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ observations) → ask (countBacklog connection) λ where
        (inj₁ error) → done (inj₁ error)
        (inj₂ pending) → ask (commit connection) λ where
          (inj₁ error) → done (inj₁ error)
          (inj₂ _) → done (inj₂ (render calendar observations baseline pending run zone))

  baseline : ℕ → ℤ → ℤ → Host.Outcome → Text → Script (Text ⊎ Text)
  baseline connection first through run zone with Calendar.midnight calendar first
  ... | nothing = done (inj₁ (toList "local midnight is unavailable"))
  ... | just end = ask (countBetween connection (+ 0) end) (afterBaseline connection first through run zone)

  content : ℕ → ℤ → ℤ → Host.Outcome → Text → Script (Text ⊎ Text)
  content connection first through run zone = ask (beginReadOnlyRepeatable connection) λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ _) → baseline connection first through run zone

  sent : Text ⊎ Notification.Outcome → Text ⊎ Bool
  sent (inj₁ error) = inj₁ error
  sent (inj₂ Notification.sent) = inj₂ false
  sent (inj₂ Notification.notNeeded) = inj₂ false
  sent (inj₂ Notification.disabled) = inj₂ false
  sent (inj₂ Notification.retryPending) = inj₂ true
  sent (inj₂ _) = inj₁ (toList "daily email unavailable")

  collect : Config.Runtime → Path.Path → ℤ → ℤ → Now → Host.Outcome → Script (Text ⊎ Bool)
  collect settings path first through now run = ask (connect settings) λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ connection) → content connection first through run (localZone calendar now) >>= λ where
      (inj₁ error) → ask (close connection) (λ _ → done (inj₁ error))
      (inj₂ body) → ask (readReport path) λ report →
        ask (send settings path (Delivery.digest (Calendar.showDay calendar through) (body ++ Diagnostics.summary report ++ toList "After an unresolved prerequisite, the watcher waits for a configuration correction or explicit SIGHUP retry. The running watcher prints the retry command. A retry is not confirmation that the problem is resolved.\nHelp: https://github.com/kamysh/mimir/blob/main/docs/operations.md\n")))
        (λ reply → ask (close connection) (λ _ → done (sent reply)))

  cursor : Config.Runtime → Path.Path → ℤ → Now → Host.Outcome → (Text ⊎ Delivery.Cursor) → Script (Text ⊎ Bool)
  cursor settings path through now run (inj₁ error) = done (inj₁ error)
  cursor settings path through now run (inj₂ previous) with first (Delivery.Cursor.throughDay previous) through
  ... | inj₁ error = done (inj₁ error)
  ... | inj₂ nothing = done (inj₂ false)
  ... | inj₂ (just first) with Delivery.Cursor.nextDue previous Data.Nat.≤? Now.unixSeconds now
  ...   | no _ = done (inj₂ (Delivery.Cursor.lastAttemptFailed previous))
  ...   | yes _ = collect settings path first through now run

  configured : ℤ → Now → Host.Outcome → Config.Runtime → Script (Text ⊎ Bool)
  configured through now run settings with Email.Config.enabled (Config.Runtime.email settings)
  ... | false = done (inj₂ false)
  ... | true = ask resolveState λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ path) → ask (readCursor (Config.Runtime.email settings) path) (cursor settings path through now run)

  observed : Config.Runtime → Host.Outcome → Now → Script (Text ⊎ Bool)
  observed settings run now with Config.Judge.dailyReportTime (Config.Runtime.judge settings)
  ... | nothing = done (inj₂ false)
  ... | just time with Calendar.deliveryBoundary calendar (localDay calendar now) (reportSecond time)
  ...   | nothing = done (inj₁ (toList "local delivery time is unavailable; inspect the computer clock and configured time"))
  ...   | just boundary with boundary Integer.≤? Local.instant now
  ...     | no _ = done (inj₂ false)
  ...     | yes _ with Calendar.minimumDay calendar <? localDay calendar now
  ...       | no _ = done (inj₂ false)
  ...       | yes _ = configured (localDay calendar now - + 1) now run settings

  tick : Config.Runtime → Host.Outcome → Script (Text ⊎ Bool)
  tick settings run = ask localNow (observed settings run)

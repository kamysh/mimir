# Local calendar days in daily statistics

The report uses the computer's local calendar. It counts from the beginning
of the displayed day up to, but not including, the beginning of the next day.
It does not add 24 hours to a UTC timestamp to find the next boundary. A clock
change can make that interval shorter or longer.

[LocalCalendar](../spec/Mimir/LocalCalendar.agda) states the accepted clock and
calendar guarantees. One sampled timestamp determines the local date, time of
day and effective UTC offset. The calendar must relate those values to the
same instant. The clock's seconds are converted to the UTC nanoseconds used
by stored history, public timestamps and query boundaries. The report's
timezone label formats that sampled offset; it does
not turn historical queries into queries with a fixed offset.

The timezone library supplies the possible UTC instants for each local
midnight. A single result is used directly. An ambiguous midnight uses the
earlier instant. An unavailable midnight makes the day unavailable. The
specification accepts these library guarantees; it does not implement a
timezone database, calendar parser or formatter.

Each successful day has a `Window` containing both midnight results and the
equations identifying their dates. General laws establish that the window is
ordered, its displayed date parses back to the same day, and adjacent windows
meet at the same boundary. Missing either midnight refuses the window.
The supplied calendar also must make a successful midnight interval exactly
the requested local date. Under that guarantee, `withinMatchesDisplayedDay`
proves that a stored row admitted by the query's time filter belongs to the
displayed date. No native calendar instance is claimed by these safe proofs.

[JudgeDigest](../spec/Mimir/JudgeDigest.agda) stores that window with the day's
observed counts. Its query uses the window's exact start and end. The
`countDayUsesItsWindow` law connects a successful returned row to the actual
query event, including its date, both boundaries and returned counts. The
`unavailableDayCannotQuery` law preserves the existing unavailable-midnight
error without issuing a count query for that day.

[JudgeDigestSnapshot](../spec/Mimir/JudgeDigestSnapshot.agda) connects the
window, displayed date and selected counts to the same retained read-only
database snapshot. New experiences still count stored source revision 1;
source revisions still count later stored versions; judge reviews still count
rows attributed to the judge. The backlog and running-total rules are
unchanged. Source revisions remain distinct from a batch's corrected counter.

The 09:00 local scheduling threshold, calendar catch-up, overflow refusal,
notification cursor and error handling remain in the digest protocol. This
change concerns the Agda contract and its proofs; it changes no installed
binary, timezone setting, database record or scheduled service.

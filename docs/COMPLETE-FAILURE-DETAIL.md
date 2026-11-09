# Complete private failure explanations

Private failure reports and retained rejection details keep the complete error
explanation, including line breaks and the full error chain. The former
512-character cuts no longer remove repair instructions at the end.

The already-structured correction sent to the calling agent stays in its
existing path. Source captures stay separate in private diagnostics; this change
does not append those captures to model requests or notification mail.

Failure classification and control flow are unchanged. Public notification
labels and operational logging have separate restriction-removal work in #108
and #109. No new quota, timeout or dependency is introduced.

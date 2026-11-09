# Complete judge notification facts

Failure and recovery messages include every affected review ID. Recovery messages
include each review's available confirmation information. There is no five-review
selection or omitted-count substitute.

Project labels and unknown reason codes retain their full ordinary text. The
existing removal of control characters keeps these labels on one line; it applies
no length limit. Legacy reason codes still receive their established descriptions.

The selected facts and existing message format remain the same. Private source
captures, backend replies and full private failure details are not copied into
notifications. This change does not send mail or change its delivery settings.

The existing `JudgeNotification` model describes all affected IDs and full
labels. Its project-label law applies to every length of ordinary text. Native
tests exercise the actual failure-message builder and recovery formatter with
long Unicode names, long reason codes and both confirmed and unverified IDs
beyond the former fifth position.

This addresses #224, part of #108. Other diagnostic and logging restrictions are
tracked separately.

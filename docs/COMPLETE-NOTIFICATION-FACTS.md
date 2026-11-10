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

Notification hostnames now use the operating system's complete `uname` nodename
field, rather than a Mimir-selected 256-byte buffer. The field's capacity belongs
to the platform ABI; Mimir does not choose another hostname length allowance.
Every nonempty UTF-8 hostname is retained, including Unicode, punctuation and
whitespace. An unavailable, empty or undecodable OS observation retains the
existing explicit `unknown-host` fallback; no replacement machine name is chosen.

The subject and body keep the original hostname. Lettre encodes display headers,
including embedded line breaks, so hostname text cannot introduce another email
header. The daily Message-ID uses the hexadecimal representation of every UTF-8
hostname byte because that header has stricter syntax. It is deterministic for
the same date and hostname, and neither strips characters nor truncates the
identifier. No new dependency, subprocess, timeout or OS configuration is added.

`SMTPProtocol.computerPreservesName` applies to every nonempty decoded hostname.
Focused native tests cover names beyond the former buffer size at the decoder
boundary, complete Unicode MIME display/body and digest identity, and encoded
line breaks. The long decoder input does not claim that every OS accepts a
hostname of that length. This is part of the existing #160 restrictions audit.

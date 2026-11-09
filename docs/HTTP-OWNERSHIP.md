# HTTP request ownership

Embedding and judge requests last until their response finishes, an actual
network error occurs, or their owner cancels them. No Mimir deadline, retry
allowance or redirect-count ceiling decides when work is abandoned.

Removing a visible timeout is insufficient. The pinned Reqwest 0.12.28 client
otherwise chooses a 30-second TCP user timeout on Linux, Android and Fuchsia,
keepalive probes starting after 15 seconds at 15-second intervals with three
probes, and a 90-second idle-pool expiry. These are library defaults, not
user-approved Mimir policy. Embedding, model-download and judge clients clear
them through the supported absence settings and disable automatic retries.
The blocking download client also explicitly disables its overall timeout.

For example, a temporarily stalled peer must not lose a request merely because
30 seconds passed while data remained unacknowledged. The owner still has an
explicit cancellation path; removing a deadline does not detach the work.

Hosted embedding and model-download redirects keep their existing follow
behavior without a hop allowance. Judge API redirects remain disabled, as
before. Configured accounts, models and endpoints, certificate verification,
and HTTP error reporting are unchanged. This policy does not override a
remote server or the operating system's own connection behavior.

The local checks follow more than ten redirects, hold a response until its
owner cancels, and verify that the connection closes. They use explicit events,
not a long wait intended to outlast a removed timeout. Existing worker tests
check cancellation and process cleanup separately. No provider account, model
download or live configuration is used.

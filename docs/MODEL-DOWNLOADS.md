# Model download ownership

A model download has no application deadline or redirect-count ceiling. A slow
server may finish its response, and redirects may reach their final target.
The blocking HTTP client's timeout is explicitly disabled, so removing the old
ten-minute setting does not activate a library default timeout.

The embedding call owns its local worker. Explicit cancellation stops that
worker, reaps it and removes its owned partial download. Completed cached files
and another worker's partial files are preserved. Removing a timer does not
remove this cancellation path.

The controlled local HTTP test follows twelve redirects and holds the final
body until the test releases it. It uses channels, with no sleep or arbitrary
test delay. It checks complete publication after release. The source explicitly
disables the timeout; the test does not spend ten minutes waiting for the old
deadline. Worker cancellation tests cover termination and cleanup separately.

This covers #206, the model-download part of #107. Mail networking remains in
#110/#180. No model download, account, installed binary or live configuration
change is needed for verification.

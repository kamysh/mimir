# gen — access token rotation

## Current (v2)

The access token has been **rotated**. The previous token `tok_A3mK9` is now
**revoked** and will be rejected. The current token is `tok_R7vX2`:

    ./gen --token tok_R7vX2

## Previous (v1, revoked)

`tok_A3mK9` used to be the access token. It no longer works — calls using it
fail with an opaque error.

# Database credentials and TLS

This contract governs every database connection made by Mimir: normal queries,
startup migrations, background tasks, and (where present) listeners, advisory
locks, preparation and cancellation.

## Credentials

- `database.password` is optional. A configured value wins, including an empty
  string. Otherwise use nonempty `PGPASSWORD`, then a password-file lookup.
- Password-file selection is `database.pgpassfile`, then `PGPASSFILE`, then
  `$HOME/.pgpass`. An explicitly selected unavailable file does not cause a
  fallback to a different file.
- Config and environment passwords are literal decoded values. TOML quoting
  applies to config strings; password-file escaping does not.
- File entries use `host:port:database:user:password`. The first matching entry
  wins. Only a raw `*` field is a wildcard in the first four fields.
  Backslash quotes the next character in every field. Quotes, spaces and Unicode
  are literal; leading and trailing password spaces are preserved.
- Comments start with `#` in column one. Blank or incomplete entries are skipped.
  Strip line endings, not whitespace. An unescaped colon ends the password field.
- On Unix, only regular password files without group/world permissions are used.
- Credentials are passed through typed driver setters. Debug output and parse
  errors must not expose passwords. Files written by configuration commands
  retain owner-only permissions.
- Database setup scripts use the same file grammar and PGPASSWORD fallback
  precedence, and quote passwords as SQL values and names as SQL identifiers.
  They never print credentials or pass the password in a process argument.

## TLS

`disable` never negotiates TLS. `prefer` tries TLS and permits plaintext only
when the server declines TLS; handshake/certificate failures never trigger a
plaintext retry. `require` requires encryption without certificate validation.
`verify-ca` requires encryption and a trusted certificate chain but does not
check the hostname. `verify-full` additionally checks the hostname.
Muninn's existing `allow` mode tries plaintext first and may retry with TLS
when PostgreSQL rejects the plaintext connection.

An explicit `ssl_root_cert` PEM bundle replaces system trust; without it,
verification modes use system trust. `ssl_client_cert` is a PEM certificate
chain and `ssl_client_key` its unencrypted PKCS#8 PEM private key. Both must be
supplied together. TLS certificate settings with `disable` are errors.
Invalid files, certificate/key mismatches and verification failures produce
errors, without silently ignoring settings or retrying in plaintext.

## Configuration example

Add these optional keys to your existing `[database]` section:

```toml
[database]
host = "db.example.net"
port = 5432
dbname = "mimir"
user = "mimir"
# Choose a password source; omit both to use environment/default password file.
# password = "a literal password with spaces"
# pgpassfile = "/home/me/.config/mimir/pgpass"
ssl_mode = "verify-full"
ssl_root_cert = "/home/me/certs/server-ca.pem"
# For client-certificate authentication, supply both:
# ssl_client_cert = "/home/me/certs/client-chain.pem"
# ssl_client_key = "/home/me/certs/client-key.pem"
```

Paths are literal: use absolute paths, without `~` or environment-variable
substitution. Protect config/password files with `chmod 600`. In TOML basic
strings, escape backslashes and double quotes; single-quoted TOML literal strings
preserve backslashes. These TOML rules are separate from password-file escaping.
The setup script reads environment/password-file credentials, not application TOML.

## Verification

```sh
cargo build -p mimir-core --example connection_probe
python3 tests/database-connections.py target/debug/examples/connection_probe
```

This requires Docker and OpenSSL. It uses uniquely named disposable postgres-ai
containers, generated test certificates and isolated config files. Complete logs
remain in the printed `/var/tmp` artifact directory; containers are removed.

## Proof and test boundary

Startup uses Kryzhen 2.0.3 validation and ledger APIs with a `public` migration
target. A compatibility executor retains `public,ag_catalog` while running
historical SQL, whose AGE operators need that search path. Each migration body
and its ledger entries commit in one transaction. The real-server matrix checks
fresh startup, upgrading the pre-schema-tracking Kryzhen ledger, importing the
historical sqlx receipt, and repeat startup. It checks preservation of existing
migration records and application data; migration SQL and checksums remain
unchanged. This does not cover every historical ledger state: an existing but
incomplete schema-association table requires investigation and a verified manual
repair, not replaying SQL whose effects are already present.

`Mimir.Connection` proves source precedence, mandatory-TLS plaintext refusal,
CA-only hostname independence and uniform policy across abstract connection
paths. These are policy laws, not a proof of the Rust implementation or TLS
library. Runtime tests must verify credential parsing, source precedence,
diagnostic redaction, real TLS/authentication, and every connection path.

#!/usr/bin/env python3
"""Real authentication/TLS tests; only disposable labelled containers are used.

Usage: python3 tests/database-connections.py /path/to/connection_probe
Requires Docker, openssl, and the postgres-ai image (override PG_TEST_IMAGE).
Complete subprocess output is retained in the printed artifact directory.
"""
import importlib.util
import json
import os
from pathlib import Path
import re
import secrets
import shutil
import subprocess
import sys
import tempfile

REPO = Path(__file__).resolve().parents[1]
APP = "mimir" if (REPO / "mimir-setup").exists() else "muninn"
PROBE = str(Path(sys.argv[1]).resolve())
ROOT = Path(tempfile.mkdtemp(prefix=f"{APP}-connection-tests-", dir="/tmp"))
print(f"Artifacts: {ROOT}", flush=True)
IMAGE = os.environ.get("PG_TEST_IMAGE", "sha256:79fb863620098b1e443338075bb65f6775130cbcb381f115d4272719256e334d")
ENV = {k: v for k, v in os.environ.items() if not k.startswith("PG")}
COUNT = 0
CONTAINERS = []
runner_spec = importlib.util.spec_from_file_location("connection_command_owner", REPO / "scripts/test-isolated.py")
runner = importlib.util.module_from_spec(runner_spec)
runner_spec.loader.exec_module(runner)
COMMANDS = runner.Run(ROOT)
FINAL_POSTGRES_START = "MIMIR_CONNECTION_POSTGRES_FINAL_START"


def run(args, *, env=None, data=None, check=True, until=None):
    global COUNT
    # Keep the connection campaign's environment while reusing the maintained
    # command owner's complete capture, interruption and readiness handling.
    code, output = COMMANDS.command("connection", args, env=ENV if env is None else env,
                                    input=data, check=False, until=until)
    COUNT = COMMANDS.count
    error = (ROOT / f"{COUNT:03}-connection.stderr").read_text()
    result = subprocess.CompletedProcess(args, code, output, error)
    if check and result.returncode and until is None:
        raise AssertionError(f"command {COUNT} failed; see retained output")
    return result


def certificate(name, ca=None, extensions=None):
    key = ROOT / f"{name}.key"
    csr = ROOT / f"{name}.csr"
    crt = ROOT / f"{name}.crt"
    run(["openssl", "req", "-new", "-newkey", "rsa:2048", "-nodes", "-keyout", str(key),
         "-out", str(csr), "-subj", f"/CN={name}"])
    args = ["openssl", "x509", "-req", "-in", str(csr), "-out", str(crt), "-days", "1"]
    if ca:
        args += ["-CA", str(ROOT / f"{ca}.crt"), "-CAkey", str(ROOT / f"{ca}.key"), "-CAcreateserial"]
    else:
        args += ["-signkey", str(key)]
    if extensions:
        ext = ROOT / f"{name}.ext"
        ext.write_text(extensions)
        args += ["-extfile", str(ext)]
    run(args)
    # Disposable fixture keys; copied to mode 0600 inside the container.
    key.chmod(0o644)


def start(tls, tls_only=False):
    name = f"{APP}-connection-{secrets.token_hex(6)}"
    hba = "hostssl all certuser all cert clientcert=verify-full\n" if tls else ""
    hba += ("hostnossl all all all reject\n" if tls_only else "")
    hba += "host all all all scram-sha-256\n"
    config = ROOT / f"{name}.hba"
    config.write_text("local all all trust\n" + hba)
    config.chmod(0o644)
    script = """
set -eu
initdb -D /var/lib/postgresql/data --username=postgres --auth-local=trust --auth-host=scram-sha-256
cp /fixture/HBA /var/lib/postgresql/data/pg_hba.conf
cp /fixture/server.key /var/lib/postgresql/data/server.key
chmod 600 /var/lib/postgresql/data/server.key
printf '%s\\n' 'FINAL_START' >&2
exec postgres -D /var/lib/postgresql/data -c lc_messages=C -c listen_addresses='*' -c shared_preload_libraries=age \
 -c unix_socket_directories=/var/lib/postgresql/data -c search_path=public,ag_catalog \
 -c ssl=TLS -c ssl_cert_file=/fixture/server.crt -c ssl_key_file=/var/lib/postgresql/data/server.key \
 -c ssl_ca_file=/fixture/ca.crt
""".replace("HBA", config.name).replace("TLS", "on" if tls else "off").replace("FINAL_START", FINAL_POSTGRES_START)
    run(["docker", "create", "--name", name, "--label", "connection-test=" + str(ROOT),
         "--user", "999:999",
         "--publish", "127.0.0.1::5432", "--mount", f"type=bind,src={ROOT},dst=/fixture,readonly",
         "--env", "PGHOST=/var/lib/postgresql/data", "--entrypoint", "/bin/bash", IMAGE, "-c", script])
    CONTAINERS.append(name)
    run(["docker", "start", name])
    run(["docker", "logs", "--follow", name],
        until=(FINAL_POSTGRES_START, runner.POSTGRES_READY))
    run(["docker", "exec", name, "pg_isready", "--timeout=0", "-U", "postgres"])
    port = int(run(["docker", "port", name, "5432/tcp"]).stdout.strip().rsplit(":", 1)[1])
    sql(name, "CREATE EXTENSION age; CREATE EXTENSION vector; CREATE EXTENSION pgcrypto;")
    return name, port


def sql(name, statement):
    return run(["docker", "exec", "-i", name, "psql", "-X", "-U", "postgres", "-v", "ON_ERROR_STOP=1"], data=statement)


def escaped(value):
    return value.replace("\\", "\\\\").replace(":", "\\:")


def current_migration_names(directory):
    names = []
    for path in sorted(directory.glob("*.sql")):
        lines = path.read_text().splitlines()
        assert lines and lines[0].strip() == "-- #!migration", f"missing migration header: {path}"
        found = []
        terminated = False
        for line in lines[1:]:
            assert line.lstrip().startswith("--"), f"unterminated migration header: {path}"
            match = re.fullmatch(r'\s*--\s*name:\s*(.+)\s*[,;]\s*', line)
            if match:
                name = json.loads(match.group(1))
                assert isinstance(name, str) and name, f"invalid migration name: {path}"
                found.append(name)
            if line.rstrip().endswith(";"):
                terminated = True
                break
        assert terminated and len(found) == 1, f"expected one migration name: {path}"
        names.extend(found)
    assert names and len(names) == len(set(names)), "missing or repeated source migration names"
    return sorted(names)


def check_migration_schemas(query, source_names):
    actual_names = sorted(json.loads(query(
        "SELECT COALESCE(json_agg(name), '[]'::json) FROM mallard.applied_migrations;")))
    assert actual_names == source_names, f"migration ledger names differ: expected {source_names!r}, got {actual_names!r}"
    expected = sorted((name, "public") for name in source_names)
    actual = sorted(tuple(row) for row in json.loads(query(
        "SELECT COALESCE(json_agg(json_build_array(migration_name,schema)), '[]'::json) "
        "FROM mallard.applied_migration_schemas;")))
    assert actual == expected, f"migration schema owners differ: expected {expected!r}, got {actual!r}"


def password_file(name, port, password, user="tester", database="postgres"):
    path = ROOT / name
    path.write_text("# ignored\ninvalid\nwrong:*:*:*:wrong\n" +
                    ":".join(map(escaped, ["127.0.0.1", str(port), database, user, password])) +
                    "\r\n*:*:*:*:wrong\n")
    path.chmod(0o600)
    return str(path)


PASSED = 0


def probe(label, port, fields=None, env=None, ok=True, ssl=False, path="query", user="tester", database="postgres"):
    global PASSED
    values = dict(host="127.0.0.1", port=port, dbname=database, user=user, ssl_mode="disable")
    values.update(fields or {})
    cfg = ROOT / "config.toml"
    cfg.write_text("config_version = 1\n[logging]\ndirectory = " + json.dumps(str(ROOT / "logs")) +
                   "\n[database]\n" + "".join(f"{k} = {json.dumps(v, ensure_ascii=False)}\n" for k, v in values.items()))
    cfg.chmod(0o600)
    result = run([PROBE, str(cfg), path], env={**ENV, "PGPASSFILE": str(ROOT / "absent"), **(env or {})}, check=False)
    assert (result.returncode == 0) == ok, f"{label}: unexpected result, command {COUNT}"
    if ok:
        assert f"ssl={str(ssl).lower()}" in result.stdout, f"{label}: wrong transport"
    assert SECRET not in result.stdout + result.stderr, f"{label}: password exposed"
    PASSED += 1
    print("PASS " + label, flush=True)


SECRET = "  'quoted\" : slash\\ пароль $()  "
try:
    certificate("ca", extensions="basicConstraints=critical,CA:TRUE\nkeyUsage=critical,keyCertSign,cRLSign\n")
    certificate("otherca", extensions="basicConstraints=critical,CA:TRUE\nkeyUsage=critical,keyCertSign,cRLSign\n")
    certificate("server", "ca", "subjectAltName=DNS:localhost\nextendedKeyUsage=serverAuth\n")
    certificate("certuser", "ca", "extendedKeyUsage=clientAuth\n")
    # Mounted directory must be searchable by the container's UID. Generated
    # keys are test-only; no real credentials or configuration enter this tree.
    ROOT.chmod(0o755)
    plain, port = start(False)
    sql(plain, "CREATE ROLE tester LOGIN PASSWORD '" + SECRET.replace("'", "''") + "';")
    file = password_file("passwords", port, SECRET)
    probe("literal config password beats environment and file", port, {"password": SECRET, "pgpassfile": "/absent"}, {"PGPASSWORD": "wrong"})
    probe("environment beats file", port, {"pgpassfile": "/absent"}, {"PGPASSWORD": SECRET})
    probe("configured file beats environment file", port, {"pgpassfile": file}, {"PGPASSFILE": "/absent", "PGPASSWORD": ""})
    probe("PGPASSFILE with escapes and CRLF", port, env={"PGPASSFILE": file})
    probe("explicit missing file does not fall back", port, {"pgpassfile": "/absent"}, {"PGPASSFILE": file}, ok=False)
    probe("empty configured password overrides environment", port, {"password": ""}, {"PGPASSWORD": SECRET}, ok=False)
    Path(file).chmod(0o644)
    probe("insecure password file ignored", port, {"pgpassfile": file}, ok=False)
    Path(file).chmod(0o600)
    probe("prefer accepts non-TLS server", port, {"password": SECRET, "ssl_mode": "prefer"})
    for mode in ["require", "verify-ca", "verify-full"]:
        probe(mode + " refuses non-TLS server", port, {"password": SECRET, "ssl_mode": mode}, ok=False)
    # Real setup script creates and updates a role using decoded credentials.
    role, database = 'test\'"role:slash\\', 'test\'"db:slash\\'
    setup_file = password_file("setup-passwords", port, SECRET, role, database)
    setup = ["bash", str(REPO / f"{APP}-setup/create-db-user.sh"), "--container", plain,
             "--host", "127.0.0.1", "--port", str(port), "--user", role, "--db", database]
    run(setup, env={**ENV, "PGPASSFILE": setup_file})
    probe("setup file grammar and SQL quoting", port, {"password": SECRET}, user=role, database=database)
    run(setup, env={**ENV, "PGPASSWORD": SECRET, "PGPASSFILE": "/absent"})
    probe("setup PGPASSWORD and idempotence", port, {"password": SECRET}, user=role, database=database)

    # Exercise the actual Mimir startup migration path on a fresh DB, then
    # reconstruct the pre-schema-tracking Kryzhen and sqlx history formats.
    migration_db = "mimir_connection_migrations"
    run(["bash", str(REPO / "mimir-setup/create-db-user.sh"), "--container", plain,
         "--host", "127.0.0.1", "--port", str(port), "--user", "tester", "--db", migration_db],
        env={**ENV, "PGPASSWORD": SECRET})
    def migration_sql(statement):
        return run(["docker", "exec", "-i", plain, "psql", "-X", "-tA", "-U", "postgres",
                    "-d", migration_db, "-v", "ON_ERROR_STOP=1"], data=statement).stdout.strip()
    def ledger():
        return migration_sql("SELECT json_agg(row_to_json(m) ORDER BY name) FROM mallard.applied_migrations m;")
    expected_migrations = current_migration_names(REPO / "crates/core/migrations")
    probe("fresh migration with Kryzhen 2", port, {"password": SECRET}, path="migrate", database=migration_db)
    before = ledger()
    check_migration_schemas(migration_sql, expected_migrations)
    migration_sql("CREATE TABLE public.upgrade_sentinel(value text); INSERT INTO public.upgrade_sentinel VALUES ('preserved');")
    migration_sql("DROP TABLE mallard.applied_migration_schemas; DROP TABLE mallard.migrator_version; "
                  "DROP INDEX mallard.applied_migrations_name_key;")
    probe("upgrade existing Kryzhen history", port, {"password": SECRET}, path="migrate", database=migration_db)
    assert ledger() == before, "upgrade replayed or changed canonical migration history"
    assert migration_sql("SELECT value FROM public.upgrade_sentinel;") == "preserved"
    check_migration_schemas(migration_sql, expected_migrations)
    probe("migration upgrade is idempotent", port, {"password": SECRET}, path="migrate", database=migration_db)
    assert ledger() == before
    check_migration_schemas(migration_sql, expected_migrations)
    receipt = json.loads((REPO / "crates/core/migrations/.kryzhen-import-receipt.json").read_text())
    imported = receipt['migrations']
    names = ','.join("'" + row['kryzhen_name'].replace("'", "''") + "'" for row in imported)
    migration_sql("CREATE TABLE public._sqlx_migrations(version bigint PRIMARY KEY, description text NOT NULL, "
                  "installed_on timestamptz NOT NULL DEFAULT now(), success boolean NOT NULL, checksum bytea NOT NULL, execution_time bigint NOT NULL);"
                  f"DELETE FROM mallard.applied_migration_schemas WHERE migration_name IN ({names});"
                  f"DELETE FROM mallard.applied_migrations WHERE name IN ({names});")
    for row in imported:
        migration_sql("INSERT INTO public._sqlx_migrations(version,description,success,checksum,execution_time) VALUES ("
                      f"{row['version']},'{row['sqlx_description']}',true,decode('{row['sqlx_checksum_hex']}','hex'),0);")
    probe("import historical sqlx receipt with Kryzhen 2", port, {"password": SECRET}, path="migrate", database=migration_db)
    assert migration_sql("SELECT to_regclass('public._sqlx_migrations') IS NULL;") == "t"
    check_migration_schemas(migration_sql, expected_migrations)
    before = ledger()
    probe("sqlx import is idempotent", port, {"password": SECRET}, path="migrate", database=migration_db)
    assert ledger() == before
    check_migration_schemas(migration_sql, expected_migrations)
    migration_sql("UPDATE mallard.applied_migrations SET checksum=decode(repeat('00',32),'hex') "
                  "WHERE name=(SELECT name FROM mallard.applied_migrations ORDER BY name LIMIT 1);")
    tampered = ledger()
    probe("changed migration checksum is rejected", port, {"password": SECRET}, path="migrate", database=migration_db, ok=False)
    assert ledger() == tampered, "failed validation changed migration history"
    assert migration_sql("SELECT value FROM public.upgrade_sentinel;") == "preserved"

    secure, tls_port = start(True, tls_only=True)
    sql(secure, "CREATE ROLE tester LOGIN PASSWORD '" + SECRET.replace("'", "''") + "'; CREATE ROLE certuser LOGIN;")
    ca = str(ROOT / "ca.crt")
    base = dict(password=SECRET, ssl_mode="require")
    probe("require encrypted", tls_port, base, ssl=True)
    probe("prefer negotiates TLS", tls_port, {**base, "ssl_mode": "prefer"}, ssl=True)
    if APP == "muninn":
        probe("allow retries TLS after plaintext rejection", tls_port, {**base, "ssl_mode": "allow"}, ssl=True)
        probe("allow prefers plaintext", port, {**base, "ssl_mode": "allow"})
    probe("verify-ca ignores hostname but validates trust", tls_port, {**base, "ssl_mode": "verify-ca", "ssl_root_cert": ca}, ssl=True)
    probe("verify-full rejects wrong hostname", tls_port, {**base, "ssl_mode": "verify-full", "ssl_root_cert": ca}, ok=False)
    full = {**base, "host": "localhost", "ssl_mode": "verify-full", "ssl_root_cert": ca}
    probe("verify-full checks trusted hostname", tls_port, full, ssl=True)
    for mode in ["verify-ca", "verify-full"]:
        probe(mode + " rejects untrusted CA", tls_port, {**full, "ssl_mode": mode, "ssl_root_cert": str(ROOT / "otherca.crt")}, ok=False)
    bundle = ROOT / "bundle.crt"
    bundle.write_text((ROOT / "otherca.crt").read_text() + (ROOT / "ca.crt").read_text())
    probe("multiple root certificates", tls_port, {**full, "ssl_root_cert": str(bundle)}, ssl=True)
    identity = {**full, "ssl_client_cert": str(ROOT / "certuser.crt"), "ssl_client_key": str(ROOT / "certuser.key")}
    identity.pop("password")
    probe("mutual TLS client identity", tls_port, identity, ssl=True, user="certuser")
    probe("missing client identity rejected by server", tls_port, full, ok=False, user="certuser")
    probe("partial client identity rejected", tls_port, {**full, "ssl_client_cert": str(ROOT / "certuser.crt")}, ok=False)
    probe("mismatched client key rejected", tls_port, {**identity, "ssl_client_key": str(ROOT / "server.key")}, ok=False, user="certuser")
    probe("disabled TLS with certificate options rejected", port, {"password": SECRET, "ssl_root_cert": ca}, ok=False)
    if APP == "muninn":
        for path in ["listener", "lock", "preparation"]:
            probe(path + " including cancellation uses TLS", tls_port, full, ssl=True, path=path)
            probe(path + " supports plaintext", port, {"password": SECRET}, path=path)
    print(f"PASS: {PASSED} real connection checks", flush=True)
finally:
    for name in CONTAINERS:
        result = run(["docker", "inspect", "--format", '{{index .Config.Labels "connection-test"}}', name])
        assert result.stdout.strip() == str(ROOT), "cleanup identity mismatch"
        run(["docker", "logs", name], check=False)
        run(["docker", "rm", "-f", "--volumes", name])
    # Keep complete logs; generated test-only keys/config are not needed later.
    for pattern in ["*.key", "*.csr", "*.srl", "config.toml", "*passwords"]:
        for entry in ROOT.glob(pattern):
            entry.unlink()
    ROOT.chmod(0o700)

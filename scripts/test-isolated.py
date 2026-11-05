#!/usr/bin/env python3
"""Run release checks with a private home and an owned, disposable PostgreSQL container."""
import argparse
import json
import os
from pathlib import Path
import secrets
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time

REPO = Path(__file__).resolve().parents[1]
IMAGE = "sha256:79fb863620098b1e443338075bb65f6775130cbcb381f115d4272719256e334d"
LABEL = "mimir.isolated-test"


def isolated_environment(root, inherited):
    # Build tooling may use its dependency cache; application state and credentials
    # come exclusively from this run. API keys and deployment overrides are absent.
    allowed = ("PATH", "LANG", "LC_ALL", "SSL_CERT_FILE", "NIX_SSL_CERT_FILE",
               "LD_LIBRARY_PATH", "LIBRARY_PATH", "PKG_CONFIG_PATH", "PKG_CONFIG_LIBDIR",
               "OPENSSL_DIR", "OPENSSL_LIB_DIR", "OPENSSL_INCLUDE_DIR", "RUST_SRC_PATH",
               "NIX_CFLAGS_COMPILE", "NIX_LDFLAGS", "NIX_CC", "NIX_BINTOOLS")
    env = {key: inherited[key] for key in allowed if key in inherited}
    env["CARGO_HOME"] = inherited.get("CARGO_HOME", str(Path.home() / ".cargo"))
    env.update({"HOME": str(root / "home"), "XDG_CONFIG_HOME": str(root / "config"),
                "XDG_STATE_HOME": str(root / "state"), "XDG_CACHE_HOME": str(root / "cache"),
                "TMPDIR": str(root / "scratch"), "CARGO_TARGET_DIR": str(root / "target"),
                "MIMIR_EVAL_TARGET_DIR": str(root / "eval-target"),
                "CARGO_BUILD_JOBS": "4", "CI": "true", "PYTHONDONTWRITEBYTECODE": "1"})
    for key in ("HOME", "XDG_CONFIG_HOME", "XDG_STATE_HOME", "XDG_CACHE_HOME", "TMPDIR"):
        Path(env[key]).mkdir(mode=0o700)
    return env


class Run:
    def __init__(self, root):
        self.root = root
        self.env = isolated_environment(root, os.environ)
        self.count = 0
        self.container = None
        self.token = secrets.token_hex(16)
        guards = root / "bin"
        guards.mkdir(mode=0o700)
        for name in ("mimir", "mimir-mcp"):
            path = guards / name
            path.write_text("#!/bin/sh\nexec " + shlex.quote(str(root / "target/debug" / name)) + ' "$@"\n')
            path.chmod(0o700)
        for name in ("codex", "claude"):
            path = guards / name
            path.write_text('#!/bin/sh\necho "Live model harness forbidden in release tests" >&2\nexit 78\n')
            path.chmod(0o700)
        self.env["PATH"] = str(guards) + os.pathsep + self.env["PATH"]

    def command(self, name, argv, *, env=None, input=None, cwd=REPO, check=True):
        self.count += 1
        stem = self.root / f"{self.count:03}-{name}"
        print(f"Check: {name}; log: {stem}.log", flush=True)
        (stem.with_suffix(".command.json")).write_text(json.dumps(argv) + "\n")
        process = None
        try:
            with stem.with_suffix(".stdout").open("w") as output, stem.with_suffix(".stderr").open("w") as error:
                process = subprocess.Popen(argv, cwd=cwd, env=self.env if env is None else env,
                    stdin=subprocess.PIPE if input is not None else subprocess.DEVNULL,
                    text=True, stdout=output, stderr=error, start_new_session=True)
                try:
                    process.communicate(input)
                except BaseException:
                    # Cancel only this check's owned process group, allowing the
                    # judge's stop handlers to reap their own MCP/model children.
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                    raise
        finally:
            stem.with_suffix(".exit").write_text(str(process.returncode if process else 127) + "\n")
            with stem.with_suffix(".log").open("w") as combined:
                for suffix in (".stdout", ".stderr"):
                    combined.write(suffix + ":\n")
                    with stem.with_suffix(suffix).open() as stream:
                        shutil.copyfileobj(stream, combined)
        if check and process.returncode:
            raise RuntimeError(f"{name} failed ({process.returncode}); full log: {stem}.log")
        return process.returncode, stem.with_suffix(".stdout").read_text()

    def fixture(self):
        name = "mimir-test-" + self.token[:16]
        script = """set -eu
initdb -D /var/lib/postgresql/data --username=postgres --auth-local=trust --auth-host=scram-sha-256
printf 'local all all trust\\nhost all postgres all reject\\nhost all all all scram-sha-256\\n' > /var/lib/postgresql/data/pg_hba.conf
exec postgres -D /var/lib/postgresql/data -c listen_addresses='*' -c shared_preload_libraries=age -c search_path=public,ag_catalog -c unix_socket_directories=/var/lib/postgresql/data
"""
        _, output = self.command("create-database-container", [
            "docker", "create", "--name", name, "--label", LABEL + "=" + self.token,
            "--user", "999:999", "--memory", "1g", "--cpus", "2", "--tmpfs",
            "/var/lib/postgresql/data:rw,size=512m,uid=999,gid=999,mode=0700",
            "--publish", "127.0.0.1::5432", "--env", "PGHOST=/var/lib/postgresql/data",
            "--entrypoint", "/bin/bash", IMAGE, "-c", script])
        self.container = output.strip()
        if len(self.container) != 64 or not all(c in "0123456789abcdef" for c in self.container):
            raise RuntimeError("Docker did not return a container identity")
        self.command("start-database-container", ["docker", "start", self.container])
        for attempt in range(60):
            code, _ = self.command("database-ready", ["docker", "exec", self.container,
                                      "pg_isready", "-U", "postgres"], check=False)
            if code == 0:
                break
            time.sleep(0.5)
        else:
            raise RuntimeError("isolated PostgreSQL did not become ready")
        _, output = self.command("database-port", ["docker", "port", self.container, "5432/tcp"])
        address, port = output.strip().rsplit(":", 1)
        if address != "127.0.0.1":
            raise RuntimeError("test PostgreSQL must bind loopback only")
        port = int(port)
        database = "mimir_learning_test_" + self.token[:16]
        user = "mimir_test_" + self.token[:16]
        password = secrets.token_hex(32)
        passfile = self.root / "test.pgpass"
        passfile.write_text(f"127.0.0.1:{port}:{database}:{user}:{password}\n")
        passfile.chmod(0o600)
        self.env.update({"MIMIR_HOST": "127.0.0.1", "MIMIR_PORT": str(port),
                         "MIMIR_DBNAME": database, "MIMIR_USER": user, "PGPASSFILE": str(passfile)})
        self.command("database-role-and-extensions", ["bash", str(REPO / "mimir-setup/create-db-user.sh"),
            "--container", self.container, "--host", "127.0.0.1", "--port", str(port),
            "--user", user, "--db", database])
        binary = self.root / "target/debug/mimir"
        mcp = self.root / "target/debug/mimir-mcp"
        manifest = {"root": str(self.root), "token": self.token, "container": self.container,
                    "database": database, "user": user, "port": port,
                    "mimir": str(binary), "mcp": str(mcp)}
        (self.root / "fixture.json").write_text(json.dumps(manifest, indent=2) + "\n")
        self.env.update({"MIMIR_TEST_ROOT": str(self.root), "MIMIR_TEST_TOKEN": self.token,
            "MIMIR_CONFIG": str(self.root / "config.toml"),
            "MIMIR_TEST_CONFIG": str(self.root / "config.toml"),
            "MIMIR_TEST_MIMIR": str(binary), "MIMIR_TEST_MCP": str(mcp)})
        text = 'config_version = 1\n[logging]\ndirectory = ' + json.dumps(str(self.root / "logs")) + '\n[database]\n'
        for key, value in {"host": "127.0.0.1", "port": port, "dbname": database,
                           "user": user, "pgpassfile": str(passfile), "ssl_mode": "disable"}.items():
            text += key + " = " + json.dumps(value) + "\n"
        (self.root / "database.toml").write_text(text)
        text += '\n[judge]\nbatch_size = 1\nmcp_command = ' + json.dumps(str(mcp))
        text += '\n[llm]\nbackend = "command"\nmodel = "fixture"\ncommand = "/bin/true"\n'
        text += '[email]\nenabled = false\n'
        (self.root / "config.toml").write_text(text)
        self.command("fixture-contract", ["python3", "tests/support/fixture.py", "check"])

    def cleanup(self):
        if not self.container:
            return
        self.command("database-final-logs", ["docker", "logs", self.container], check=False)
        _, raw = self.command("database-ownership", ["docker", "inspect", self.container])
        info = json.loads(raw)[0]
        if info["Id"] != self.container or info["Config"]["Labels"].get(LABEL) != self.token:
            raise RuntimeError("refusing cleanup of a container this run does not own")
        self.command("remove-owned-database", ["docker", "rm", "--force", self.container])
        self.container = None

    def checks(self, selected):
        self.command("isolation-regressions", ["python3", "-m", "unittest", "discover", "-s", "tests", "-p", "test_isolated_runner.py"])
        if selected in ("all", "format"):
            self.command("format", ["cargo", "fmt", "--all", "--", "--check"])
        if selected in ("all", "lint"):
            self.command("lint", ["cargo", "clippy", "--workspace", "--all-targets", "--locked", "--offline", "--", "-D", "warnings"])
        if selected in ("all", "workspace", "fixtures"):
            self.fixture()
            self.command("build-snapshot-binaries", ["cargo", "build", "--workspace", "--locked", "--offline"])
            self.command("initialize-test-schema", [self.env["MIMIR_TEST_MIMIR"], "stats"])
        if selected in ("all", "workspace"):
            self.command("workspace-tests", ["cargo", "test", "--workspace", "--all-targets", "--locked", "--offline", "--", "--test-threads=1"])
            self.command("documentation-tests", ["cargo", "test", "--workspace", "--doc", "--locked", "--offline"])
        if selected in ("all", "fixtures"):
            self.command("judge-adapter-fixtures", ["bash", "tests/judge-adapters.sh"])
            self.command("evaluator-tests", ["cargo", "test", "--manifest-path", "tests/eval/Cargo.toml", "--locked", "--offline"])
            self.command("learning-comparator-fixture", ["bash", "tests/eval/learning-compare-fixture.sh"])
        if selected in ("all", "formal"):
            self.command("aggregate-formal-specification", ["agda", "Mimir.agda"], cwd=REPO / "spec")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", choices=("all", "format", "lint", "workspace", "formal", "fixtures"), default="all")
    args = parser.parse_args()
    os.umask(0o077)
    # nix develop may point TMPDIR at its short-lived shell directory. Retain
    # command evidence after that shell exits, including failed executions.
    root = Path(tempfile.mkdtemp(prefix="mimir-tests-", dir="/tmp")).resolve()
    print(f"Isolated test artifacts: {root}", flush=True)
    run = Run(root)
    status = 1
    def interrupted(signum, _frame):
        raise InterruptedError(f"interrupted by signal {signum}")
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, interrupted)
    try:
        run.checks(args.check)
        status = 0
    except (OSError, ValueError, KeyError, RuntimeError, InterruptedError) as error:
        print(str(error), file=sys.stderr)
    finally:
        try:
            run.cleanup()
        except (OSError, ValueError, RuntimeError) as error:
            print(f"Fixture cleanup failed: {error}", file=sys.stderr)
            status = 1
        (root / "result.json").write_text(json.dumps({"check": args.check, "exit_code": status,
             "container_removed": run.container is None}, indent=2) + "\n")
    return status


if __name__ == "__main__":
    sys.exit(main())

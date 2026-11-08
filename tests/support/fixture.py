"""The private connection contract shared by isolated test fixtures."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time
import tomllib


def validate(env=None):
    env = os.environ if env is None else env
    root = Path(env["MIMIR_TEST_ROOT"])
    if not root.is_absolute() or root.is_symlink() or root.stat().st_mode & 0o077:
        raise ValueError("test root must be a private absolute directory")
    manifest = root / "fixture.json"
    data = json.loads(manifest.read_text())
    if data["token"] != env["MIMIR_TEST_TOKEN"] or data["root"] != str(root):
        raise ValueError("fixture ownership mismatch")
    if not data["database"].startswith("mimir_learning_test_"):
        raise ValueError("isolated test database required")
    if not data["user"].startswith("mimir_test_") or not 0 < data["port"] < 65536:
        raise ValueError("invalid isolated test connection")
    expected = {
        "MIMIR_HOST": "127.0.0.1", "MIMIR_PORT": str(data["port"]),
        "MIMIR_DBNAME": data["database"], "MIMIR_USER": data["user"],
        "MIMIR_CONFIG": str(root / "config.toml"),
        "MIMIR_TEST_CONFIG": str(root / "config.toml"),
        "PGPASSFILE": str(root / "test.pgpass"),
        "MIMIR_TEST_MIMIR": data["mimir"], "MIMIR_TEST_MCP": data["mcp"],
    }
    if any(env.get(key) != value for key, value in expected.items()):
        raise ValueError("connection/configuration differs from the isolated fixture")
    if any(env.get(key) for key in ("PGPASSWORD", "PGSERVICE", "PGSERVICEFILE", "DATABASE_URL")):
        raise ValueError("inherited database settings are forbidden")
    for name in ("config.toml", "database.toml", "test.pgpass"):
        path = root / name
        if path.is_symlink() or path.stat().st_mode & 0o077:
            raise ValueError("fixture files must be private regular files")
    config = tomllib.loads((root / "config.toml").read_text())
    db = config["database"]
    if config.get("config_version") != 1 or any(db.get(key) != value for key, value in {
        "host": "127.0.0.1", "port": data["port"], "dbname": data["database"],
        "user": data["user"], "pgpassfile": str(root / "test.pgpass"),
    }.items()) or "password" in db:
        raise ValueError("fixture configuration does not match its connection contract")
    return data


def cancel(data, args):
    root = Path(data["root"])
    command = args.argv[1:] if args.argv[:1] == ["--"] else args.argv
    if not command or command[0] != data["mimir"]:
        raise ValueError("cancellation must use the fixture's own binary")
    for path in (args.ready, args.report):
        if not path.is_absolute() or not path.parent.resolve().is_relative_to(root):
            raise ValueError("cancellation evidence must stay in the test root")
    stderr = args.report.with_suffix(".stderr")
    with args.report.open("xb") as output, stderr.open("xb") as error:
        process = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=output, stderr=error)
        try:
            deadline = time.monotonic() + 60
            while not args.ready.exists() or (args.stderr_ready and args.stderr_ready not in stderr.read_text()):
                if process.poll() is not None:
                    raise RuntimeError(f"judge exited before fixture readiness; inspect {stderr}")
                if time.monotonic() >= deadline:
                    raise RuntimeError(f"fixture readiness deadline exceeded; inspect {stderr}")
                time.sleep(0.05)
            process.terminate()
            if process.wait(timeout=10) != 0:
                raise RuntimeError(f"judge did not stop cleanly; inspect {stderr}")
        finally:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
            args.report.with_suffix(".exit").write_text(str(process.returncode) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="operation", required=True)
    sub.add_parser("check")
    cancellation = sub.add_parser("cancel")
    cancellation.add_argument("--ready", type=Path, required=True)
    cancellation.add_argument("--report", type=Path, required=True)
    cancellation.add_argument("--stderr-ready")
    cancellation.add_argument("argv", nargs=argparse.REMAINDER)
    config = sub.add_parser("config")
    config.add_argument("path", type=Path)
    config.add_argument("--backend", required=True)
    config.add_argument("--model", default="fixture-model")
    config.add_argument("--project")
    config.add_argument("--command")
    args = parser.parse_args()
    data = validate()
    if args.operation == "check":
        return
    if args.operation == "cancel":
        return cancel(data, args)
    root = Path(data["root"])
    if args.command and args.backend != "command":
        raise ValueError("only the command backend accepts a custom command")
    if not args.path.is_absolute() or not args.path.parent.resolve().is_relative_to(root):
        raise ValueError("generated configuration must stay in the isolated test root")
    text = (root / "database.toml").read_text()
    text += f'\n[judge]\nmcp_command = {json.dumps(data["mcp"])}\n'
    if args.project:
        text += f'project = {json.dumps(args.project)}\n'
    text += f'\n[llm]\nbackend = {json.dumps(args.backend)}\nmodel = {json.dumps(args.model)}\n'
    if args.backend == "codex":
        text += 'reasoning_effort = "high"\n'
    if args.command:
        text += f'command = {json.dumps(args.command)}\n'
    text += '\n[email]\nenabled = false\n'
    with open(args.path, "x", opener=lambda path, flags: os.open(path, flags, 0o600)) as output:
        output.write(text)


if __name__ == "__main__":
    main()

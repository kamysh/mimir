"""The private connection contract shared by isolated test fixtures."""
import argparse
import asyncio
import json
import os
from pathlib import Path
import subprocess
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
    return asyncio.run(cancel_owned(command, args))


async def cancel_owned(command, args):
    """Readiness is an event; shutdown allowances remain a separate concern."""
    loop = asyncio.get_running_loop()
    ready = loop.create_future()
    readers = set()
    server = None
    process = None
    stderr_task = None
    exited = None
    env = dict(os.environ)

    async def announcement(reader, writer):
        task = asyncio.current_task()
        readers.add(task)
        try:
            message = await reader.readexactly(len(b"ready\n"))
            extra = await reader.read(1)
            if message != b"ready\n" or extra:
                raise RuntimeError("fixture sent an invalid readiness event")
            if not ready.done():
                ready.set_result(None)
        except (asyncio.IncompleteReadError, OSError, RuntimeError) as error:
            if not ready.done():
                ready.set_exception(RuntimeError(f"fixture readiness event failed: {error}"))
        finally:
            writer.close()
            await writer.wait_closed()
            readers.discard(task)

    stderr = args.report.with_suffix(".stderr")
    with args.report.open("xb") as output, stderr.open("xb") as error:
        try:
            if args.stderr_ready:
                env.pop("MIMIR_JUDGE_FIXTURE_READY_ADDR", None)
            else:
                server = await asyncio.start_server(announcement, "127.0.0.1", 0)
                address = server.sockets[0].getsockname()
                env["MIMIR_JUDGE_FIXTURE_READY_ADDR"] = f"{address[0]}:{address[1]}"
                env["MIMIR_JUDGE_FIXTURE_READY_FILE"] = str(args.ready)
            process = await asyncio.create_subprocess_exec(*command, env=env,
                stdin=subprocess.DEVNULL, stdout=output, stderr=asyncio.subprocess.PIPE)

            async def capture_stderr():
                marker = args.stderr_ready.encode() if args.stderr_ready else None
                suffix = b""
                while chunk := await process.stderr.read(65536):
                    error.write(chunk)
                    error.flush()
                    if marker and not ready.done():
                        combined = suffix + chunk
                        if marker in combined:
                            ready.set_result(None)
                        # Only matching context is reduced; every byte was
                        # already stored above, including final shutdown text.
                        suffix = combined[-len(marker):]
                if marker and not ready.done():
                    ready.set_exception(RuntimeError(f"stderr closed before fixture readiness; inspect {stderr}"))

            stderr_task = asyncio.create_task(capture_stderr())
            exited = asyncio.create_task(process.wait())
            done, _ = await asyncio.wait((ready, exited), return_when=asyncio.FIRST_COMPLETED)
            if ready not in done:
                raise RuntimeError(f"judge exited before fixture readiness; inspect {stderr}")
            await ready
            if not args.ready.exists():
                raise RuntimeError(f"readiness event has no owned evidence file: {args.ready}")
            if exited.done():
                raise RuntimeError(f"judge exited before fixture cancellation; inspect {stderr}")
            process.terminate()
            if await asyncio.wait_for(asyncio.shield(exited), timeout=10) != 0:
                raise RuntimeError(f"judge did not stop cleanly; inspect {stderr}")
        finally:
            if process is not None and process.returncode is None:
                try:
                    process.terminate()
                except ProcessLookupError:
                    pass
                try:
                    await asyncio.wait_for(asyncio.shield(exited), timeout=10)
                except asyncio.TimeoutError:
                    process.kill()
                    await exited
            if stderr_task is not None:
                await stderr_task
            if server is not None:
                server.close()
                await server.wait_closed()
            for task in list(readers):
                task.cancel()
            if readers:
                await asyncio.gather(*readers, return_exceptions=True)
            if not ready.done():
                ready.cancel()
            elif not ready.cancelled():
                ready.exception()
            args.report.with_suffix(".exit").write_text(str(process.returncode if process else 127) + "\n")


def rpc(data, args):
    root = Path(data["root"])
    for path in (args.config, args.request, args.report):
        if not path.is_absolute() or not path.parent.resolve().is_relative_to(root):
            raise ValueError("RPC configuration and evidence must stay in the isolated test root")
    selected = tomllib.loads(args.config.read_text())
    database = tomllib.loads((root / "database.toml").read_text())["database"]
    if selected.get("database") != database:
        raise ValueError("RPC configuration differs from the isolated database")
    try:
        request = json.loads(args.request.read_bytes())
    except (ValueError, UnicodeError):
        request = None  # Malformed frames still need the server's parse diagnostic.
    if isinstance(request, dict) and "id" not in request:
        raise ValueError("fixture RPC expects a request with an id; add id: 1 to await a response, rather than sending a notification")
    return asyncio.run(rpc_owned(data, args))


async def rpc_owned(data, args):
    """One fixture exchange owns stdin until its complete response arrives."""
    env = {**os.environ, "MIMIR_CONFIG": str(args.config)}
    process = None
    with args.report.with_suffix(".stdout").open("xb") as output, args.report.with_suffix(".stderr").open("xb") as error:
        try:
            process = await asyncio.create_subprocess_exec(data["mcp"], env=env,
                stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE, stderr=error)
            request = args.request.read_bytes()
            try:
                decoded = json.loads(request)
                expected_id = decoded.get("id") if isinstance(decoded, dict) else None
            except (ValueError, UnicodeError):
                expected_id = None
            process.stdin.write(request if request.endswith(b"\n") else request+b"\n")
            await process.stdin.drain()
            pending = b""
            received = False
            while not received:
                chunk = await process.stdout.read(65536)
                if not chunk:
                    raise RuntimeError(f"MCP exited before its fixture response; inspect {args.report}")
                output.write(chunk)
                output.flush()
                pending += chunk
                while b"\n" in pending:
                    line, pending = pending.split(b"\n", 1)
                    response = json.loads(line)
                    if isinstance(response, dict) and "id" in response and ("result" in response or "error" in response):
                        if response["id"] != expected_id and not (response["id"] is None and "error" in response):
                            raise RuntimeError(f"MCP returned a different request id; inspect {args.report}")
                        received = True
        finally:
            if process is not None:
                process.stdin.close()
                try:
                    await process.stdin.wait_closed()
                except (BrokenPipeError, ConnectionResetError):
                    pass
                while chunk := await process.stdout.read(65536):
                    output.write(chunk)
                    output.flush()
                await process.wait()
            args.report.with_suffix(".exit").write_text(str(process.returncode if process else 127)+"\n")
    if process.returncode:
        raise RuntimeError(f"MCP fixture failed ({process.returncode}); inspect {args.report}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="operation", required=True)
    sub.add_parser("check")
    cancellation = sub.add_parser("cancel")
    cancellation.add_argument("--ready", type=Path, required=True)
    cancellation.add_argument("--report", type=Path, required=True)
    cancellation.add_argument("--stderr-ready")
    cancellation.add_argument("argv", nargs=argparse.REMAINDER)
    exchange = sub.add_parser("rpc")
    exchange.add_argument("--config", type=Path, required=True)
    exchange.add_argument("--request", type=Path, required=True)
    exchange.add_argument("--report", type=Path, required=True)
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
    if args.operation == "rpc":
        return rpc(data, args)
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

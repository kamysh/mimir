"""Regression checks for rejecting deployment settings before opening a connection."""
import importlib.util
import ast
import json
import os
from pathlib import Path
import re
import tempfile
import sys
import socket
import subprocess
import unittest
from types import SimpleNamespace
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


runner = load("isolated_runner", REPO / "scripts/test-isolated.py")
fixture = load("fixture_contract", REPO / "tests/support/fixture.py")


class IsolationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.data = {"root": str(self.root), "token": "owned-fixture", "port": 43217,
                     "database": "mimir_learning_test_owned", "user": "mimir_test_owned",
                     "mimir": str(self.root / "target/debug/mimir"),
                     "mcp": str(self.root / "target/debug/mimir-mcp")}
        (self.root / "fixture.json").write_text(json.dumps(self.data))
        self.env = {"MIMIR_TEST_ROOT": str(self.root), "MIMIR_TEST_TOKEN": self.data["token"],
                    "MIMIR_HOST": "127.0.0.1", "MIMIR_PORT": "43217",
                    "MIMIR_DBNAME": self.data["database"], "MIMIR_USER": self.data["user"],
                    "MIMIR_CONFIG": str(self.root / "config.toml"),
                    "MIMIR_TEST_CONFIG": str(self.root / "config.toml"),
                    "PGPASSFILE": str(self.root / "test.pgpass"),
                    "MIMIR_TEST_MIMIR": self.data["mimir"], "MIMIR_TEST_MCP": self.data["mcp"]}
        database = dict(host="127.0.0.1", port=43217, dbname=self.data["database"],
                        user=self.data["user"], pgpassfile=self.env["PGPASSFILE"])
        self.config = 'config_version = 1\n[database]\n' + ''.join(
            f'{key} = {json.dumps(value)}\n' for key, value in database.items())
        for name, text in (("config.toml", self.config), ("database.toml", self.config),
                           ("test.pgpass", "fixture-only")):
            path = self.root / name
            path.write_text(text)
            path.chmod(0o600)

    def test_valid_owned_fixture(self):
        self.assertEqual(fixture.validate(self.env), self.data)

    def test_generated_judge_config_uses_the_current_schema_without_retired_budgets(self):
        output = self.root / "generated.toml"
        argv = ["fixture.py", "config", str(output), "--backend", "codex", "--model", "fixture-a"]
        with patch.dict(os.environ, self.env, clear=True), patch("sys.argv", argv):
            fixture.main()
        config = fixture.tomllib.loads(output.read_text())
        self.assertEqual(config["config_version"], 1)
        self.assertEqual(config["database"]["port"], 43217)
        self.assertEqual(config["llm"], dict(backend="codex", model="fixture-a", reasoning_effort="high"))
        self.assertFalse(config["email"]["enabled"])

    def test_missing_fixture_does_not_fall_back(self):
        with self.assertRaises(KeyError):
            fixture.validate({"MIMIR_CONFIG": "/deployment/config.toml"})

    def test_harness_config_refuses_custom_command_settings(self):
        for backend in ("codex", "claude-code"):
            argv = ["fixture.py", "config", str(self.root / "invalid.toml"),
                    "--backend", backend, "--command", "/fixture/custom"]
            with self.subTest(backend=backend), patch.dict(os.environ, self.env, clear=True), patch("sys.argv", argv):
                with self.assertRaises(ValueError):
                    fixture.main()

    def test_cancellation_waits_for_fixture_readiness_before_signalling(self):
        binary = Path(self.data["mimir"])
        binary.parent.mkdir(parents=True)
        binary.write_text('#!' + sys.executable + '\n' +
            'import os,signal,sys\nfrom pathlib import Path\n' +
            'signal.signal(signal.SIGTERM, lambda *_: exit(0))\n' +
            'Path(os.environ["MIMIR_JUDGE_FIXTURE_READY_FILE"]).write_text("ready")\n' +
            'print("fixture waiting", file=sys.stderr, flush=True)\n' +
            'signal.pause()\n')
        binary.chmod(0o700)
        ready = self.root / "child.ready"
        report = self.root / "cancel.json"
        env = {**self.env, "MIMIR_JUDGE_FIXTURE_READY_FILE": str(ready)}
        argv = ["fixture.py", "cancel", "--ready", str(ready), "--stderr-ready", "fixture waiting", "--report", str(report), "--", str(binary)]
        with patch.dict(os.environ, env, clear=True), patch("sys.argv", argv):
            fixture.main()
        self.assertTrue(ready.exists())
        self.assertEqual(report.read_bytes(), b"")
        self.assertEqual(report.with_suffix(".exit").read_text(), "0\n")
        self.assertIn("fixture waiting", report.with_suffix(".stderr").read_text())

    def cancellation_binary(self, source):
        binary = Path(self.data["mimir"])
        binary.parent.mkdir(parents=True)
        binary.write_text('#!' + sys.executable + '\n' + source)
        binary.chmod(0o700)
        return binary

    def cancellation_args(self, binary, name="event-cancel"):
        return SimpleNamespace(argv=[str(binary)], ready=self.root/(name+".ready"),
                               report=self.root/(name+".out"), stderr_ready=None)

    def test_cancellation_observes_network_readiness_and_keeps_complete_shutdown_output(self):
        binary = self.cancellation_binary(
            'import os,signal,socket,sys\nfrom pathlib import Path\n'
            'def stopped(*_):\n'
            '    print("after-ready", flush=True)\n'
            '    sys.stderr.write("x"*70000+"complete-shutdown\\n"); sys.stderr.flush()\n'
            '    sys.exit(0)\n'
            'signal.signal(signal.SIGTERM, stopped)\n'
            'Path(os.environ["MIMIR_JUDGE_FIXTURE_READY_FILE"]).write_text("ready")\n'
            'host,port=os.environ["MIMIR_JUDGE_FIXTURE_READY_ADDR"].split(":")\n'
            'with socket.create_connection((host,int(port))) as event: event.sendall(b"ready\\n")\n'
            'signal.pause()\n')
        args = self.cancellation_args(binary)
        with patch.dict(os.environ, self.env, clear=True):
            fixture.cancel(self.data, args)
        self.assertEqual(args.report.read_text(), "after-ready\n")
        self.assertEqual(args.report.with_suffix(".stderr").read_text(), "x"*70000+"complete-shutdown\n")
        self.assertEqual(args.report.with_suffix(".exit").read_text(), "0\n")

    def test_premature_fixture_exit_is_reported_without_readiness_polling(self):
        binary = self.cancellation_binary('import sys\nprint("not ready",file=sys.stderr)\nsys.exit(7)\n')
        args = self.cancellation_args(binary)
        with patch.dict(os.environ, self.env, clear=True):
            with self.assertRaisesRegex(RuntimeError, "before fixture readiness"):
                fixture.cancel(self.data, args)
        self.assertEqual(args.report.with_suffix(".stderr").read_text(), "not ready\n")
        self.assertEqual(args.report.with_suffix(".exit").read_text(), "7\n")

    def test_readiness_event_requires_its_owned_evidence_file(self):
        binary = self.cancellation_binary(
            'import os,signal,socket,sys\n'
            'signal.signal(signal.SIGTERM,lambda *_:sys.exit(0))\n'
            'host,port=os.environ["MIMIR_JUDGE_FIXTURE_READY_ADDR"].split(":")\n'
            'with socket.create_connection((host,int(port))) as event: event.sendall(b"ready\\n")\n'
            'signal.pause()\n')
        args = self.cancellation_args(binary)
        with patch.dict(os.environ, self.env, clear=True):
            with self.assertRaisesRegex(RuntimeError, "no owned evidence file"):
                fixture.cancel(self.data, args)
        self.assertEqual(args.report.with_suffix(".exit").read_text(), "0\n")

    def test_invalid_readiness_event_is_diagnostic_and_reaps_the_fixture(self):
        binary = self.cancellation_binary(
            'import os,signal,socket,sys\n'
            'signal.signal(signal.SIGTERM,lambda *_:sys.exit(0))\n'
            'host,port=os.environ["MIMIR_JUDGE_FIXTURE_READY_ADDR"].split(":")\n'
            'with socket.create_connection((host,int(port))) as event: event.sendall(b"wrong\\n")\n'
            'signal.pause()\n')
        args = self.cancellation_args(binary)
        with patch.dict(os.environ, self.env, clear=True):
            with self.assertRaisesRegex(RuntimeError, "invalid readiness event"):
                fixture.cancel(self.data, args)
        self.assertEqual(args.report.with_suffix(".exit").read_text(), "0\n")

    def rpc_fixture(self, source):
        binary = Path(self.data["mcp"])
        binary.parent.mkdir(parents=True)
        binary.write_text('#!' + sys.executable + '\n' + source)
        binary.chmod(0o700)
        request = self.root/"call.request"
        request.write_text(json.dumps({"jsonrpc":"2.0","id":1,"method":"tools/list"})+"\n")
        return SimpleNamespace(config=self.root/"config.toml", request=request, report=self.root/"call")

    def test_rpc_keeps_stdin_open_until_reply_and_preserves_complete_output(self):
        args = self.rpc_fixture(
            'import json,os,sys\nfrom pathlib import Path\n'
            'request=json.loads(sys.stdin.readline())\n'
            'os.set_blocking(0,False)\n'
            'try:\n'
            '    early=os.read(0,1)\n'
            'except BlockingIOError:\n'
            '    early=None\n'
            'os.set_blocking(0,True)\n'
            'if early is not None: sys.exit(7)\n'
            'Path(os.environ["MIMIR_TEST_ROOT"],"stdin-open").write_text("yes")\n'
            'print(json.dumps({"jsonrpc":"2.0","id":request["id"],"result":"z"*70000}),flush=True)\n'
            'sys.stdin.read()\n'
            'sys.stderr.write("shutdown:"+"e"*70000);sys.stderr.flush()\n')
        with patch.dict(os.environ, self.env, clear=True):
            fixture.rpc(self.data,args)
        self.assertEqual((self.root/"stdin-open").read_text(),"yes")
        response=json.loads(args.report.with_suffix(".stdout").read_text())
        self.assertEqual(response["result"],"z"*70000)
        self.assertEqual(args.report.with_suffix(".stderr").read_text(),"shutdown:"+"e"*70000)
        self.assertEqual(args.report.with_suffix(".exit").read_text(),"0\n")

    def test_rpc_reports_mismatched_reply_and_waits_for_stdin_cleanup(self):
        args=self.rpc_fixture('import json,sys\nsys.stdin.readline()\nprint(json.dumps({"jsonrpc":"2.0","id":9,"result":{}}),flush=True)\nsys.stdin.read()\n')
        with patch.dict(os.environ,self.env,clear=True):
            with self.assertRaisesRegex(RuntimeError,"different request id"):
                fixture.rpc(self.data,args)
        self.assertEqual(args.report.with_suffix(".exit").read_text(),"0\n")

    def test_rpc_refuses_another_database_before_starting_mcp(self):
        args=self.rpc_fixture('from pathlib import Path\nPath("must-not-run").write_text("started")\n')
        args.config=self.root/"foreign.toml"
        args.config.write_text(self.config.replace('43217','5450'))
        with patch.dict(os.environ,self.env,clear=True):
            with self.assertRaisesRegex(ValueError,"differs from the isolated database"):
                fixture.rpc(self.data,args)
        self.assertFalse(args.report.with_suffix(".stdout").exists())

    def test_rpc_explains_missing_request_id_before_starting_mcp(self):
        args=self.rpc_fixture('raise RuntimeError("must not start")\n')
        args.request.write_text(json.dumps({"jsonrpc":"2.0","method":"tools/list"}))
        with patch.dict(os.environ,self.env,clear=True):
            with self.assertRaisesRegex(ValueError,"request with an id"):
                fixture.rpc(self.data,args)
        self.assertFalse(args.report.with_suffix(".stdout").exists())

    def test_rpc_preserves_server_parse_diagnostic_for_malformed_frame(self):
        args=self.rpc_fixture('import json,sys\nsys.stdin.readline()\nprint(json.dumps({"jsonrpc":"2.0","id":None,"error":{"code":-32700,"message":"malformed JSON"}}),flush=True)\nsys.stdin.read()\n')
        args.request.write_text('{broken JSON\n')
        with patch.dict(os.environ,self.env,clear=True):
            fixture.rpc(self.data,args)
        response=json.loads(args.report.with_suffix(".stdout").read_text())
        self.assertEqual(response["error"]["code"],-32700)
        self.assertIsNone(response["id"])

    def test_connection_and_config_overrides_are_refused(self):
        for key, value in {"MIMIR_HOST": "deployment", "MIMIR_PORT": "5450",
                           "MIMIR_DBNAME": "mimir", "MIMIR_USER": "mimir",
                           "MIMIR_CONFIG": "/deployment/config.toml",
                           "PGPASSFILE": "/deployment/.pgpass",
                           "MIMIR_TEST_MCP": "/deployment/bin/mimir-mcp"}.items():
            with self.subTest(key=key), self.assertRaises(ValueError):
                fixture.validate({**self.env, key: value})

    def test_foreign_owner_and_database_are_refused(self):
        for key, value in (("token", "foreign"), ("database", "mimir")):
            (self.root / "fixture.json").write_text(json.dumps({**self.data, key: value}))
            with self.subTest(key=key), self.assertRaises(ValueError):
                fixture.validate(self.env)

    def test_inherited_database_credentials_are_refused(self):
        for key in ("PGPASSWORD", "PGSERVICE", "PGSERVICEFILE", "DATABASE_URL"):
            with self.subTest(key=key), self.assertRaises(ValueError):
                fixture.validate({**self.env, key: "deployment"})

    def test_config_version_and_connection_are_checked(self):
        for text in (self.config.replace('config_version = 1\n', ''),
                     self.config.replace('43217', '5450'), self.config + 'password = "deployment"\n'):
            (self.root / "config.toml").write_text(text)
            with self.subTest(text=text), self.assertRaises(ValueError):
                fixture.validate(self.env)

    def test_symlink_and_public_credentials_are_refused(self):
        path = self.root / "test.pgpass"
        path.chmod(0o644)
        with self.assertRaises(ValueError):
            fixture.validate(self.env)
        path.unlink()
        path.symlink_to("/deployment/.pgpass")
        with self.assertRaises(ValueError):
            fixture.validate(self.env)

    def test_environment_excludes_deployment_and_provider_secrets(self):
        child = self.root / "environment"
        child.mkdir()
        inherited = {"PATH": "/tools", "HOME": "/deployment", "MIMIR_CONFIG": "/deployment/config",
                     "PGPASSFILE": "/deployment/passwords", "PGPASSWORD": "secret",
                     "OPENAI_API_KEY": "secret", "ANTHROPIC_API_KEY": "secret",
                     "XDG_STATE_HOME": "/deployment/state", "MIMIR_STEP5_TEST_CONFIG": "/old/config"}
        env = runner.isolated_environment(child, inherited)
        for key in ("MIMIR_CONFIG", "PGPASSFILE", "PGPASSWORD", "OPENAI_API_KEY",
                    "ANTHROPIC_API_KEY", "MIMIR_STEP5_TEST_CONFIG"):
            self.assertNotIn(key, env)
        for key in ("HOME", "XDG_CONFIG_HOME", "XDG_STATE_HOME", "XDG_CACHE_HOME", "TMPDIR"):
            self.assertTrue(Path(env[key]).is_relative_to(child))

    def test_cleanup_refuses_a_container_without_its_ownership_label(self):
        child = self.root / "cleanup"
        child.mkdir()
        run = runner.Run(child)
        run.container = "a" * 64
        info = [{"Id": run.container, "Config": {"Labels": {runner.LABEL: "another-run"}}}]
        with patch.object(run, "command", return_value=(0, json.dumps(info))) as command:
            with self.assertRaises(RuntimeError):
                run.cleanup()
        self.assertFalse(any("rm" in call.args[1] for call in command.call_args_list))

    def owned_run(self, name):
        child = self.root / name
        child.mkdir(mode=0o700)
        return runner.Run(child)

    def test_interrupted_command_waits_for_owner_to_reap_its_separate_child_group(self):
        run=self.owned_run("owned-stop")
        child_source=(
            'import signal,sys\n'
            'def stopped(*_):\n'
            '    print("child done",flush=True);sys.exit(0)\n'
            'signal.signal(signal.SIGTERM,stopped)\n'
            'print("child ready",flush=True)\n'
            'signal.pause()\n')
        marker=run.root/"owner-completed.json"
        source=(
            'import json,os,signal,subprocess,sys\nfrom pathlib import Path\n'
            f'child=subprocess.Popen([sys.executable,"-c",{child_source!r}],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True)\n'
            'separate=os.getpgid(child.pid)!=os.getpgrp()\n'
            'def stopped(*_):\n'
            '    os.killpg(child.pid,signal.SIGTERM)\n'
            '    out,err=child.communicate()\n'
            '    sys.stdout.write(out);sys.stdout.flush()\n'
            '    sys.stderr.write(err+"owner cleanup diagnostics\\n");sys.stderr.flush()\n'
            f'    Path({str(marker)!r}).write_text(json.dumps({{"child_status":child.returncode,"separate_group":separate}}))\n'
            '    print("owner done",flush=True);sys.exit(0)\n'
            'signal.signal(signal.SIGTERM,stopped)\n'
            'assert child.stdout.readline()=="child ready\\n"\n'
            f'os.kill({os.getpid()},signal.SIGUSR1)\n'
            'signal.pause()\n')

        def interrupted(*_):
            raise InterruptedError("owned cancellation requested")

        prior=runner.signal.signal(runner.signal.SIGUSR1,interrupted)
        try:
            with self.assertRaisesRegex(InterruptedError,"owned cancellation requested"):
                run.command("owned-stop",[sys.executable,"-c",source])
        finally:
            runner.signal.signal(runner.signal.SIGUSR1,prior)
        self.assertEqual(json.loads(marker.read_text()),{"child_status":0,"separate_group":True})
        self.assertEqual((run.root/"001-owned-stop.exit").read_text(),"0\n")
        self.assertEqual((run.root/"001-owned-stop.stdout").read_text(),"child done\nowner done\n")
        self.assertEqual((run.root/"001-owned-stop.stderr").read_text(),"owner cleanup diagnostics\n")

    def test_readiness_ignores_bootstrap_and_preserves_both_output_streams(self):
        run = self.owned_run("readiness")
        script = (
            'import signal,sys\n'
            'print("bootstrap: database system is ready to accept connections", flush=True)\n'
            'print("bootstrap stopped", file=sys.stderr, flush=True)\n'
            'print("MIMIR_ISOLATED_POSTGRES_FINAL_START", flush=True)\n'
            'print("final: database system is ready to accept connections", file=sys.stderr, flush=True)\n'
            'signal.pause()\n'
        )
        code, output = run.command("ready", [sys.executable, "-c", script],
                                   until=(runner.FINAL_POSTGRES_START, runner.POSTGRES_READY))
        self.assertEqual(code, -runner.signal.SIGKILL)
        self.assertIn("bootstrap stopped", output)
        self.assertIn("final: database system is ready", output)
        events = json.loads((run.root / "001-ready.events.json").read_text())
        self.assertEqual(events["observed"], [runner.FINAL_POSTGRES_START, runner.POSTGRES_READY])
        self.assertTrue(events["completed"])
        self.assertIn(output, (run.root / "001-ready.log").read_text())

    def test_bootstrap_readiness_without_final_server_is_not_success(self):
        run = self.owned_run("bootstrap-only")
        script = 'import sys; print("database system is ready to accept connections"); sys.exit(7)'
        with self.assertRaisesRegex(RuntimeError, "expected readiness event"):
            run.command("ready", [sys.executable, "-c", script],
                        until=(runner.FINAL_POSTGRES_START, runner.POSTGRES_READY))
        self.assertEqual((run.root / "001-ready.exit").read_text(), "7\n")
        events = json.loads((run.root / "001-ready.events.json").read_text())
        self.assertFalse(events["completed"])
        self.assertEqual(events["observed"], [])
        self.assertIn("database system is ready", (run.root / "001-ready.log").read_text())

    def test_final_server_failure_retains_diagnostic_and_actual_exit(self):
        run = self.owned_run("final-failure")
        script = ('import sys\nprint("MIMIR_ISOLATED_POSTGRES_FINAL_START", flush=True)\n'
                  'print("final server refused its owned data directory", file=sys.stderr, flush=True)\n'
                  'sys.exit(9)\n')
        with self.assertRaisesRegex(RuntimeError, "expected readiness event"):
            run.command("ready", [sys.executable, "-c", script],
                        until=(runner.FINAL_POSTGRES_START, runner.POSTGRES_READY))
        self.assertEqual((run.root / "001-ready.exit").read_text(), "9\n")
        events = json.loads((run.root / "001-ready.events.json").read_text())
        self.assertEqual(events["observed"], [runner.FINAL_POSTGRES_START])
        self.assertIn("refused its owned data directory", (run.root / "001-ready.log").read_text())

    def test_listener_records_queued_connections_before_stop(self):
        attempts = []
        stop_reader, stop_writer = socket.socketpair()
        with socket.socket() as listener, stop_reader, stop_writer:
            listener.bind(("127.0.0.1", 0))
            listener.listen()
            with socket.create_connection(listener.getsockname()), socket.create_connection(listener.getsockname()):
                stop_writer.sendall(b"stop")
                runner.observe_connections(listener, stop_reader, attempts)
        self.assertEqual(attempts, [True, True])

    def test_guard_listener_stops_on_event_and_refuses_any_connection(self):
        for connects in (False, True):
            with self.subTest(connects=connects):
                run = self.owned_run("guard-" + str(connects))
                binary = run.root / "target/debug/deps/store_integration-controlled"
                binary.parent.mkdir(parents=True)
                binary.write_text('#!' + sys.executable + '\n'
                    'import os,socket,sys\n' +
                    ('with socket.create_connection(("127.0.0.1", int(os.environ["MIMIR_PORT"]))) as client: client.recv(1)\n' if connects else '') +
                    'print("MIMIR_PORT does not match this test fixture")\nsys.exit(101)\n')
                binary.chmod(0o700)
                if connects:
                    with self.assertRaisesRegex(RuntimeError, "before networking"):
                        run.guard_regression()
                else:
                    run.guard_regression()
                receipt = json.loads((run.root / "connection-guard.json").read_text())
                self.assertEqual(receipt["rejected_before_connect"], not connects)
                self.assertEqual(receipt["connection_attempts"], int(connects))
                self.assertEqual(receipt["listener_errors"], [])

    def assert_unrestricted_private_container(self, arguments):
        for option in ("--memory", "--memory-swap", "--cpus", "--cpu-quota", "--tmpfs", "--storage-opt"):
            self.assertNotIn(option, arguments)
        self.assertIn("127.0.0.1::5432", arguments)
        self.assertIn("--user", arguments)
        self.assertEqual(arguments[arguments.index("--user") + 1], "999:999")
        self.assertIn("--label", arguments)

    def test_release_fixture_keeps_guards_without_resource_quotas(self):
        child = self.root / "resource-fixture"
        child.mkdir(mode=0o700)
        run = runner.Run(child)
        calls = []
        events = []

        def command(name, arguments, **kwargs):
            calls.append(arguments)
            if name == "database-start-events":
                events.append(kwargs["until"])
            if name == "create-database-container":
                return 0, "a" * 64
            if name == "database-port":
                return 0, "127.0.0.1:43217\n"
            if name == "database-ownership":
                return 0, json.dumps([{"Id": run.container, "Config": {"Labels": {runner.LABEL: run.token}}}])
            return 0, ""

        prior_mask = os.umask(0o077)
        try:
            with patch.object(run, "command", side_effect=command):
                run.fixture()
                fixture.validate(run.env)
                container = run.container
                run.cleanup()
        finally:
            os.umask(prior_mask)
        create = next(args for args in calls if args[:2] == ["docker", "create"])
        self.assert_unrestricted_private_container(create)
        self.assertIn(runner.LABEL + "=" + run.token, create)
        removed = next(args for args in calls if args[:2] == ["docker", "rm"])
        self.assertIn("--volumes", removed)
        self.assertEqual(removed[-1], container)
        self.assertNotIn("CARGO_BUILD_JOBS", run.env)
        self.assertEqual(events, [(runner.FINAL_POSTGRES_START, runner.POSTGRES_READY)])
        ready = next(args for args in calls if "pg_isready" in args)
        self.assertIn("--timeout=0", ready)
        entrypoint = create[-1]
        self.assertLess(entrypoint.index(runner.FINAL_POSTGRES_START), entrypoint.index("exec postgres"))
        self.assertIn("-c lc_messages=C", entrypoint)

    def test_connection_fixture_has_no_resource_quota(self):
        # Load the actual argument-generating function without executing the
        # script's live TLS campaign or its module-level setup.
        path = REPO / "tests/database-connections.py"
        definition = next(node for node in ast.parse(path.read_text()).body
                          if isinstance(node, ast.FunctionDef) and node.name == "start")
        child = self.root / "connection-resource-fixture"
        child.mkdir()
        calls = []

        def command(arguments, **kwargs):
            calls.append(arguments)
            return SimpleNamespace(returncode=0, stdout="127.0.0.1:43217\n")

        context = {"APP": "mimir", "ROOT": child, "IMAGE": "fixture-image", "CONTAINERS": [],
                   "secrets": runner.secrets, "runner": runner,
                   "FINAL_POSTGRES_START": "MIMIR_CONNECTION_POSTGRES_FINAL_START",
                   "run": command, "sql": lambda *args: None}
        exec(compile(ast.Module(body=[definition], type_ignores=[]), str(path), "exec"), context)
        for tls in (False, True):
            context["start"](tls)
        created = [args for args in calls if args[:2] == ["docker", "create"]]
        self.assertEqual(len(created), 2)
        for arguments in created:
            self.assert_unrestricted_private_container(arguments)
            self.assertIn("connection-test=" + str(child), arguments)
            self.assertIn(f"type=bind,src={child},dst=/fixture,readonly", arguments)
            self.assertIn("-c lc_messages=C", arguments[-1])
            self.assertLess(arguments[-1].index(context["FINAL_POSTGRES_START"]), arguments[-1].index("exec postgres"))
        probes = [args for args in calls if "pg_isready" in args]
        self.assertEqual(len(probes), 2)
        self.assertTrue(all("--timeout=0" in args for args in probes))
        self.assertEqual(len([args for args in calls if args[:3] == ["docker", "logs", "--follow"]]), 2)

    def connection_command(self, name):
        path = REPO / "tests/database-connections.py"
        definition = next(node for node in ast.parse(path.read_text()).body
                          if isinstance(node, ast.FunctionDef) and node.name == "run")
        owner = self.owned_run(name)
        context = {"COMMANDS": owner, "ROOT": owner.root, "ENV": dict(os.environ),
                   "COUNT": 0, "subprocess": subprocess}
        exec(compile(ast.Module(body=[definition], type_ignores=[]), str(path), "exec"), context)
        return owner, context["run"]

    def test_connection_command_keeps_complete_output_and_failure_status(self):
        owner, command = self.connection_command("connection-capture")
        args = [sys.executable, "-c", 'import sys; print("o"*70000); print("e"*70000,file=sys.stderr); sys.exit(7)']
        result = command(args, check=False)
        self.assertEqual(result.returncode, 7)
        self.assertEqual(result.stdout, "o"*70000+"\n")
        self.assertEqual(result.stderr, "e"*70000+"\n")
        self.assertEqual((owner.root/"001-connection.stdout").read_text(), result.stdout)
        self.assertEqual((owner.root/"001-connection.stderr").read_text(), result.stderr)
        self.assertEqual((owner.root/"001-connection.exit").read_text(), "7\n")
        with self.assertRaisesRegex(AssertionError, "command 2 failed"):
            command(args)
        self.assertEqual((owner.root/"002-connection.exit").read_text(), "7\n")

    def test_connection_readiness_joins_its_log_reader(self):
        owner, command = self.connection_command("connection-readiness")
        marker = "MIMIR_CONNECTION_POSTGRES_FINAL_START"
        source = ('import signal,sys\n'
                  f'print({marker!r},flush=True)\n'
                  f'print({runner.POSTGRES_READY!r},file=sys.stderr,flush=True)\n'
                  'signal.pause()\n')
        result = command([sys.executable, "-c", source], until=(marker, runner.POSTGRES_READY))
        self.assertEqual(result.returncode, -runner.signal.SIGKILL)
        events = json.loads((owner.root/"001-connection.events.json").read_text())
        self.assertTrue(events["completed"])
        self.assertEqual(events["observed"], [marker, runner.POSTGRES_READY])
        self.assertIn(runner.POSTGRES_READY, result.stdout)

    def test_migration_schema_check_requires_exact_current_names_and_owners(self):
        path = REPO / "tests/database-connections.py"
        definition = next(node for node in ast.parse(path.read_text()).body
                          if isinstance(node, ast.FunctionDef) and node.name == "check_migration_schemas")
        context = {"json": json}
        exec(compile(ast.Module(body=[definition], type_ignores=[]), str(path), "exec"), context)
        check = context["check_migration_schemas"]
        names = ["initial", "recent"]
        def query(rows, ledger=names):
            return lambda sql: json.dumps(rows if "applied_migration_schemas" in sql else ledger)
        check(query([["recent", "public"], ["initial", "public"]]), names)
        for rows in ([], [["initial", "public"]],
                     [["initial", "public"], ["unexpected", "public"]],
                     [["initial", "public"], ["recent", "other"]],
                     [["initial", "public"], ["recent", "public"], ["recent", "public"]]):
            with self.subTest(rows=rows), self.assertRaisesRegex(AssertionError, "migration schema owners differ"):
                check(query(rows), names)
        with self.assertRaisesRegex(AssertionError, "migration ledger names differ"):
            check(query([["initial", "public"], ["recent", "public"]], ["initial"]), names)

    def test_migration_names_come_from_current_source_headers(self):
        path = REPO / "tests/database-connections.py"
        definition = next(node for node in ast.parse(path.read_text()).body
                          if isinstance(node, ast.FunctionDef) and node.name == "current_migration_names")
        context = {"json": json, "re": re}
        exec(compile(ast.Module(body=[definition], type_ignores=[]), str(path), "exec"), context)
        directory = self.root/"migration-source"
        directory.mkdir()
        first = directory/"001_initial.sql"
        first.write_text('-- #!migration\n-- name: "initial",\n-- description: "first";\nSELECT 1;\n')
        read = context["current_migration_names"]
        self.assertEqual(read(directory), ["initial"])
        later = directory/"002_later.sql"
        later.write_text('-- #!migration\n-- name: "newer",\n-- description: "later";\nSELECT 2;\n')
        self.assertEqual(read(directory), ["initial", "newer"])
        later.write_text('-- #!migration\n-- name: "initial",\n-- description: "duplicate";\nSELECT 2;\n')
        with self.assertRaisesRegex(AssertionError, "repeated source migration names"):
            read(directory)
        later.write_text('-- #!migration\n-- name: "unterminated",\nSELECT 2;\n')
        with self.assertRaisesRegex(AssertionError, "unterminated migration header"):
            read(directory)


if __name__ == "__main__":
    unittest.main()

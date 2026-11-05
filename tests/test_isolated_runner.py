"""Regression checks for rejecting deployment settings before opening a connection."""
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
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


if __name__ == "__main__":
    unittest.main()

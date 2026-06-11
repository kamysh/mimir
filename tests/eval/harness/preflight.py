#!/usr/bin/env python3
"""Version-skew guard / pre-flight (IMPLEMENTATION_PLAN.md §8 step 0, T3.1).

Belief 14f83426 (the version-skew trap): running `cargo test -p mimir-core`
against the live mimir DB applies ANY new migration via `sqlx::migrate!`
(MimirService::connect runs migrations on connect). If a migration file is newer
than the INSTALLED `mimir`/`mimir-mcp` binary, the installed CLI then fails on
EVERY command with "migration N was previously applied but is missing in the
resolved migrations" — its embedded migration set is older than the DB's
`_sqlx_migrations` head. Data is not lost, but the harness is silently broken:
the seeder (`mimir-mcp`) and cleanup (`mimir forget`) cannot run, and any belief
already read is suspect.

This module records, into `runs/env.json`:
  * the `mimir` binary version (`mimir --version`),
  * the binary's EXPECTED migration head — the max numeric prefix among the
    migration files the binary was built from (`sqlx::migrate!()` embeds
    `crates/core/migrations/*.sql`; the head is `max(prefix)`),
  * the live DB's APPLIED migration head — `max(version)` of `_sqlx_migrations`.

It REFUSES to proceed (exit non-zero / ok=False) when expected != applied. The
common failure is DB-ahead (a stray `cargo test` / `sqlx migrate` moved the head
past the installed binary); we also flag binary-ahead (a never-applied migration)
because the seeder would then write against a schema the DB lacks.

Connection params for the DB head query are read from the mimir config.toml
(`~/.config/mimir/config.toml` by default — the SAME file the live CLI uses), so
the head we read is the head the CLI talks to. The password comes from `~/.pgpass`
(PGPASSFILE), exactly like the CLI; no password is ever read into env.json.
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

HERE = Path(__file__).resolve().parent
REPO = HERE.parent

# The mimir source tree whose `crates/core/migrations` is what `sqlx::migrate!()`
# embeds into the binary. Overridable via config["mimir_src"] or $MIMIR_SRC for
# CI / a relocated checkout. The default matches this machine's layout.
DEFAULT_MIMIR_SRC = Path("/home/kamysh/Work/balovstvo/mimir")

_MIGRATION_RE = re.compile(r"^(\d+)_.*\.sql$")


# ---------------------------------------------------------------------------
# Binary side
# ---------------------------------------------------------------------------

def mimir_version(mimir_bin: str) -> Optional[str]:
    """`mimir --version` -> e.g. 'mimir 0.3.0'. None if the binary won't run
    (which is itself a skew symptom worth surfacing)."""
    try:
        r = subprocess.run([mimir_bin, "--version"], capture_output=True,
                           text=True, timeout=30)
    except (FileNotFoundError, subprocess.SubprocessError):
        return None
    if r.returncode != 0:
        return None
    return r.stdout.strip() or None


def migrations_dir(cfg: dict) -> Path:
    src = cfg.get("mimir_src") or os.environ.get("MIMIR_SRC") or str(DEFAULT_MIMIR_SRC)
    return Path(src) / "crates" / "core" / "migrations"


def binary_expected_head(cfg: dict) -> tuple[Optional[int], list[str]]:
    """The migration head the INSTALLED binary expects = max numeric prefix of the
    migration files it was built from. Returns (head, sorted_filenames).

    Honest scope: we cannot introspect the embedded set out of a stripped release
    binary, so we read it from the source checkout the binary was built from
    (cfg['mimir_src']). If that tree is absent we return (None, []) and the
    pre-flight reports head_source='unavailable' rather than guessing."""
    mdir = migrations_dir(cfg)
    if not mdir.is_dir():
        return None, []
    versions: list[int] = []
    names: list[str] = []
    for p in sorted(mdir.iterdir()):
        m = _MIGRATION_RE.match(p.name)
        if m:
            versions.append(int(m.group(1)))
            names.append(p.name)
    if not versions:
        return None, names
    return max(versions), names


# ---------------------------------------------------------------------------
# DB side
# ---------------------------------------------------------------------------

def _mimir_config_path() -> Path:
    return Path(os.environ.get("MIMIR_CONFIG",
                               os.path.expanduser("~/.config/mimir/config.toml")))


def db_params() -> dict:
    """Read host/port/dbname/user from the live mimir config.toml — the same file
    the CLI uses. Defaults match a stock install (localhost:5450/mimir/mimir)."""
    params = {"host": "localhost", "port": "5450", "dbname": "mimir", "user": "mimir"}
    path = _mimir_config_path()
    if not path.is_file():
        return params
    in_db = False
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if line.startswith("#") or not line:
            continue
        if line.startswith("["):
            in_db = line == "[database]"
            continue
        if not in_db:
            continue
        m = re.match(r'(\w+)\s*=\s*"?([^"#]+?)"?\s*(?:#.*)?$', line)
        if m and m.group(1) in params:
            params[m.group(1)] = m.group(2).strip()
    return params


def db_applied_head(params: Optional[dict] = None) -> tuple[Optional[int], str]:
    """`max(version)` from `_sqlx_migrations` on the live DB. Returns (head, note).

    head is None when the DB is unreachable or has no migrations table — both are
    surfaced (a missing table means an un-migrated DB, also a skew). The query is
    read-only. Password via PGPASSFILE (~/.pgpass), exactly like the CLI."""
    if params is None:
        params = db_params()
    psql = shutil.which("psql")
    if not psql:
        return None, "psql-not-found"
    env = dict(os.environ)
    env.setdefault("PGPASSFILE", os.path.expanduser("~/.pgpass"))
    try:
        r = subprocess.run(
            [psql, "-h", params["host"], "-p", str(params["port"]),
             "-U", params["user"], "-d", params["dbname"], "-tAc",
             "SELECT max(version) FROM _sqlx_migrations;"],
            capture_output=True, text=True, timeout=30, env=env)
    except subprocess.SubprocessError as e:
        return None, f"psql-error:{e}"
    out = r.stdout.strip()
    if r.returncode != 0:
        return None, f"psql-rc={r.returncode}:{r.stderr.strip()[:200]}"
    if out == "" or out.lower() == "null":
        return None, "no-migrations-applied"
    try:
        return int(out), "ok"
    except ValueError:
        return None, f"unparseable:{out!r}"


# ---------------------------------------------------------------------------
# The guard
# ---------------------------------------------------------------------------

def check(cfg: dict) -> dict:
    """Gather binary/DB facts and decide whether the harness may proceed.

    Returns a dict suitable for writing to runs/env.json. The `ok` key is the
    gate: True iff binary version is readable, the expected head is known, the DB
    head is readable, and expected == applied."""
    version = mimir_version(cfg.get("mimir_bin", "mimir"))
    expected_head, migration_files = binary_expected_head(cfg)
    params = db_params()
    applied_head, db_note = db_applied_head(params)

    reasons: list[str] = []
    if version is None:
        reasons.append("mimir --version failed (binary missing or itself skewed)")
    if expected_head is None:
        reasons.append(
            f"cannot determine binary's expected migration head from "
            f"{migrations_dir(cfg)} (set cfg['mimir_src'] / $MIMIR_SRC)")
    if applied_head is None:
        reasons.append(f"cannot read DB migration head ({db_note})")
    if (expected_head is not None and applied_head is not None
            and expected_head != applied_head):
        if applied_head > expected_head:
            rel = "DB-ahead"
            hint = ("A stray cargo-test/sqlx-migrate moved the DB head past the "
                    "installed binary; rebuild+install mimir to catch up.")
        else:
            rel = "binary-ahead"
            hint = ("A new migration has not been applied; the seeder would write "
                    "against a schema the DB lacks.")
        reasons.append(
            f"VERSION SKEW ({rel}): binary expects migration head "
            f"{expected_head} but live DB is at {applied_head}. {hint}")

    ok = not reasons
    return {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "mimir_version": version,
        "binary_expected_migration_head": expected_head,
        "db_applied_migration_head": applied_head,
        "db_head_note": db_note,
        "migration_files": migration_files,
        "migrations_dir": str(migrations_dir(cfg)),
        "db": {k: params[k] for k in ("host", "port", "dbname", "user")},
        "ok": ok,
        "reasons": reasons,
    }


def write_env(cfg: dict, out_dir: Path) -> dict:
    """Run check(), persist it to <out_dir>/env.json, return the report."""
    report = check(cfg)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "env.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def format_report(report: dict) -> str:
    lines = [
        "--- version-skew pre-flight (§8 step 0) ---",
        f"mimir_version              : {report['mimir_version']}",
        f"binary expected head       : {report['binary_expected_migration_head']}",
        f"DB applied head            : {report['db_applied_migration_head']} "
        f"({report['db_head_note']})",
        f"DB                         : "
        f"{report['db']['user']}@{report['db']['host']}:{report['db']['port']}/"
        f"{report['db']['dbname']}",
    ]
    if report["ok"]:
        lines.append("PREFLIGHT_OK")
    else:
        lines.append("PREFLIGHT_FAILED — refusing to proceed:")
        for r in report["reasons"]:
            lines.append(f"  - {r}")
    return "\n".join(lines) + "\n"

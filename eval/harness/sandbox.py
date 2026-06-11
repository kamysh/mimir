#!/usr/bin/env python3
"""Isolation layer for mimir-eval (IMPLEMENTATION_PLAN.md §3).

Runs the actor command (`claude -p ...`) inside a bubblewrap namespace sandbox so
that the live mimir graph is PROVABLY unreachable AND no user hooks fire —
regardless of how the actor's shell re-orders PATH.

Threat model (§3.1) and the structural defenses (§3.2):

  1. CLI leak (THE one that mattered — control agents ran `mimir query` to fetch
     seeded answers) — `mimir`/`mimir-mcp` live in ~/.local/bin and Bash is an
     allowed tool. KILLED:
       a. `--tmpfs <LOCAL_BIN_PARENT>` masks the directory the binaries live in;
          inside the sandbox they do not exist on disk. PATH order is irrelevant
          because the file is gone (verified: ~/.local/bin first on PATH still
          resolves to `command not found`).
       b. the sandboxed ~/.config/mimir/config.toml points at a dead DB; mimir
          reads its DSN ONLY from that file.
       c. no postgres client (psql) is on the sandbox PATH, so even the raw DB
          protocol has no tool to speak it.
     The actor SHARES the host network (it needs the Anthropic API). The DB port
     at 127.0.0.1:5450 is therefore reachable, but with no mimir/mimir-mcp/psql
     and a dead-DB config there is no actual channel to the seeded graph. We do
     NOT pursue full network isolation — it adds no validity to the eval and a
     severed net namespace also blocks the API the actor depends on.
  2. PATH re-add (the shell snapshot re-exports ~/.local/bin) — defeated by (1a):
     the tmpfs mask wins over any PATH the snapshot sets.
  3. Hook-injection leak — the user's ~/.claude/settings.json has a live
     UserPromptSubmit -> `mimir hook prompt` hook plus muninn-gate PreToolUse
     hooks. KILLED by pointing CLAUDE_CONFIG_DIR at a sandbox dir whose
     settings.json is `{"hooks": {}}`; the real ~/.claude is never read.

Important resolution detail discovered while building this (and pinned here):
`~/.nix-profile` is a symlink chain that passes THROUGH `~/.local/state/...`.
Masking the whole `~/.local` therefore breaks the symlink that makes `claude`
and `python3` reachable. We mask ONLY the parent of the mimir binaries
(`~/.local/bin`) by tmpfs, and we put the REAL /nix/store bin dirs for `claude`
and `python3` directly on PATH (resolved at build time), so they stay reachable
via paths that do not pass through the masked tree. /nix is ro-bound whole, so
the entire claude closure is present.
"""
from __future__ import annotations

import json
import os
import re
import shlex
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


# ---------------------------------------------------------------------------
# Path resolution (done once; the results are what get pinned into the command)
# ---------------------------------------------------------------------------

def _resolve(binary: str) -> Optional[str]:
    """Absolute, symlink-followed path of `binary`, or None if not on PATH."""
    p = shutil.which(binary)
    if not p:
        return None
    return os.path.realpath(p)


def _bin_dir(binary: str) -> Optional[str]:
    real = _resolve(binary)
    return os.path.dirname(real) if real else None


def resolve_runtime() -> dict:
    """Resolve every real bin dir / store path the sandbox needs, ONCE.

    Returns a dict the launcher pins into the bwrap command. Raises if a
    mandatory tool (claude, bash, the coreutils that tasks need) is missing.
    """
    claude_dir = _bin_dir("claude")
    if not claude_dir:
        raise RuntimeError(
            "cannot resolve `claude` on PATH; sandbox cannot run the actor")

    # Tools the tasks (and claude's own bundled shell calls) need INSIDE the
    # sandbox. We resolve each to its real /nix/store bin dir so PATH does not
    # pass through any masked tree.
    needed = ["bash", "python3", "env", "sh"]
    bin_dirs: list[str] = [claude_dir]
    for tool in needed:
        d = _bin_dir(tool)
        if d and d not in bin_dirs:
            bin_dirs.append(d)

    # coreutils / common userland — best effort; tasks use these heavily.
    for tool in ("ls", "cat", "grep", "sed", "awk", "git", "node",
                 "rg", "find", "head", "tail", "chmod", "mkdir"):
        d = _bin_dir(tool)
        if d and d not in bin_dirs:
            bin_dirs.append(d)

    bash = _resolve("bash")
    if not bash:
        raise RuntimeError("cannot resolve `bash` on PATH")

    bwrap = _resolve("bwrap")
    if not bwrap:
        raise RuntimeError(
            "cannot resolve `bwrap` on PATH; the namespace sandbox is unavailable")

    return {
        "claude_dir": claude_dir,
        "bin_dirs": bin_dirs,
        "bash": bash,
        "bwrap": bwrap,
    }


# Directory that holds the mimir CLI binaries; masking its parent's `bin` is the
# load-bearing leak-kill. We mask the *whole* ~/.local by tmpfs (it is cheap and
# also masks ~/.local/state/nix/profiles, the symlink target — harmless because
# we never resolve through it; claude/python3 are pinned by real store path).
def _local_mask_dir(home: str) -> str:
    return os.path.join(home, ".local")


# ---------------------------------------------------------------------------
# Sandbox spec
# ---------------------------------------------------------------------------

@dataclass
class SandboxSpec:
    """Everything the launcher needs to wrap one actor command."""
    workdir: str                      # the ONLY writable task dir (bind-mounted)
    home: str = field(default_factory=lambda: os.path.expanduser("~"))
    assets_dir: str = field(
        default_factory=lambda: str(Path(__file__).resolve().parent.parent / "sandbox"))
    bwrap_bin: str = "bwrap"
    extra_ro_binds: tuple = ()        # additional (src,dst) ro-binds if a task needs them
    share_net: bool = False           # reserved for the DE-SCOPED mimir_agentic arm
                                      # (see harness/arms.py); no arm sets it today
    config_dir_name: str = ".claude-eval"  # sandbox CLAUDE_CONFIG_DIR (under HOME)
    forward_credentials: bool = True  # ro-bind the host's Claude creds into the
                                      # sandbox config dir so the actor can auth
                                      # (the real ~/.claude is masked by the HOME
                                      # bind). Without this the actor is "Not
                                      # logged in" and every trial errors out.
    credentials_src: Optional[str] = None  # default: ~/.claude/.credentials.json


def _pinned_path(runtime: dict) -> str:
    """PATH containing ONLY the resolved real bin dirs + /usr/bin + /bin, with
    NO ~/.local/bin and NO ~/bin (the symlink farm that re-adds mimir)."""
    dirs = list(runtime["bin_dirs"]) + ["/usr/bin", "/bin"]
    seen, out = set(), []
    for d in dirs:
        if d and d not in seen:
            seen.add(d)
            out.append(d)
    return os.pathsep.join(out)


def _materialise_config_dir(spec: SandboxSpec, sandbox_home: str) -> str:
    """Create the sandbox CLAUDE_CONFIG_DIR with EMPTY hooks settings inside the
    per-run sandbox HOME, and return its in-sandbox path."""
    cfg_dir = os.path.join(sandbox_home, spec.config_dir_name)
    os.makedirs(cfg_dir, exist_ok=True)
    src = os.path.join(spec.assets_dir, "settings.json")
    with open(src) as f:
        settings = json.load(f)
    # Hard-assert the asset really is empty-hooks; never trust a stale file.
    if settings.get("hooks") != {}:
        raise RuntimeError(
            f"sandbox/settings.json must have empty hooks, got: {settings!r}")
    with open(os.path.join(cfg_dir, "settings.json"), "w") as f:
        json.dump(settings, f)
    return os.path.join(spec.home, spec.config_dir_name)


def _materialise_profile(spec: SandboxSpec, sandbox_home: str,
                         pinned_path: str, cfg_dir: str) -> None:
    """Write the §3.3 defense-in-depth shell profile into the sandbox HOME.

    The asset `sandbox/profile` carries @PINNED_PATH@/@CLAUDE_CONFIG_DIR@ tokens;
    we substitute the resolved values and drop the result as BOTH ~/.profile and
    ~/.bashrc inside the sandbox HOME, so any login/interactive shell the actor
    spawns re-pins PATH WITHOUT a mimir dir — on top of the bwrap --setenv that
    already pins it for the actor process itself. Under bwrap the binary is also
    tmpfs-masked, so this is belt-and-suspenders, not the primary defense.

    Hard-asserts no @TOKEN@ survives substitution, so a future token added to the
    asset can never slip through unsubstituted (the original B0.2 bug class)."""
    src = os.path.join(spec.assets_dir, "profile")
    text = Path(src).read_text()
    text = (text.replace("@PINNED_PATH@", pinned_path)
                .replace("@CLAUDE_CONFIG_DIR@", cfg_dir))
    leftover = re.findall(r"@[A-Z_]+@", text)
    if leftover:
        raise RuntimeError(
            f"sandbox/profile has unsubstituted tokens {sorted(set(leftover))}; "
            "_materialise_profile must handle every @TOKEN@")
    for name in (".profile", ".bashrc"):
        Path(sandbox_home, name).write_text(text)


def build_command(cmd: list, spec: SandboxSpec, runtime: dict,
                  sandbox_home: str) -> list:
    """Return the full argv: bwrap flags (§3.2) + `--` + the actor `cmd`.

    `sandbox_home` is a fresh host dir bind-mounted over the real HOME so the
    actor gets a clean home with our settings/config and nothing of the user's.
    """
    pinned_path = _pinned_path(runtime)
    cfg_dir = _materialise_config_dir(spec, sandbox_home)
    _materialise_profile(spec, sandbox_home, pinned_path, cfg_dir)
    dead_db = os.path.join(spec.assets_dir, "mimir-config.toml")
    # DNS fix: on NixOS /etc/resolv.conf is a symlink chain ending in
    # /run/systemd/resolve/stub-resolv.conf, which is under no tree we bind, so
    # inside the sandbox the symlink dangles and DNS silently fails (the actor
    # then hangs forever resolving the API host). We COPY the resolved file's
    # CONTENTS into a sandbox-owned file and bind that at the chain's endpoint, so
    # the existing /etc symlink resolves and we do not depend on systemd's live
    # runtime file. The stub resolver (127.0.0.53) is reachable over shared net.
    host_resolv = os.path.realpath("/etc/resolv.conf")
    resolv_copy = os.path.join(sandbox_home, "resolv.conf")
    try:
        shutil.copyfile(host_resolv, resolv_copy)
    except OSError:
        resolv_copy = None
    mimir_cfg_dst = os.path.join(spec.home, ".config", "mimir", "config.toml")

    bwrap_bin = runtime.get("bwrap") or spec.bwrap_bin
    bw = [
        bwrap_bin,
        # Read-only system trees. /nix carries the entire claude closure.
        "--ro-bind", "/usr", "/usr",
        "--ro-bind", "/nix", "/nix",
        "--ro-bind-try", "/bin", "/bin",
        "--ro-bind-try", "/lib", "/lib",
        "--ro-bind-try", "/lib64", "/lib64",
        "--ro-bind-try", "/etc", "/etc",
        "--ro-bind-try", "/run/current-system", "/run/current-system",
        # Kernel interfaces claude/node need.
        "--proc", "/proc",
        "--dev", "/dev",
        "--tmpfs", "/tmp",
        # The fresh HOME, then the ONLY writable task dir on top.
        "--bind", sandbox_home, spec.home,
        "--bind", spec.workdir, spec.workdir,
        # MASK the mimir binary directory: ~/.local becomes empty tmpfs.
        "--tmpfs", _local_mask_dir(spec.home),
        # Dead-DB mimir config (third leak-kill layer). Must come AFTER the HOME
        # bind so it lands on top.
        "--ro-bind", dead_db, mimir_cfg_dst,
    ]
    # DNS fix (see above): bind our COPY at the symlink chain's endpoint so
    # /etc/resolv.conf resolves. bwrap creates the parent dirs. Mounting over the
    # dangling /etc/resolv.conf directly fails because /etc is ro-bound.
    if resolv_copy:
        bw += ["--ro-bind-try", resolv_copy, host_resolv]

    # Auth: ro-bind the host's Claude credentials into the sandbox config dir
    # (CLAUDE_CONFIG_DIR/.credentials.json) so the actor can authenticate. The
    # real ~/.claude is masked by the HOME bind, and there is no API-key env var
    # on this host, so without this the actor is "Not logged in" and every trial
    # errors out. Read-only, same inode — no plaintext copy is written. This does
    # NOT re-open the hook leak: only .credentials.json is exposed, while
    # settings.json (hooks) stays the empty-hooks asset.
    if spec.forward_credentials:
        creds_src = spec.credentials_src or os.path.join(
            os.path.expanduser("~"), ".claude", ".credentials.json")
        if not os.path.isfile(creds_src):
            raise RuntimeError(
                f"forward_credentials is set but no credential file at {creds_src}; "
                "the sandboxed actor would be 'Not logged in'. Set "
                "SandboxSpec.credentials_src, or an ANTHROPIC_API_KEY env var and "
                "disable forward_credentials.")
        bw += ["--ro-bind", creds_src, os.path.join(cfg_dir, ".credentials.json")]

    for src, dst in spec.extra_ro_binds:
        bw += ["--ro-bind", src, dst]

    # NOTE: the actor SHARES the host network (no --unshare-net). It needs the
    # network to reach the Anthropic API, and the cheat channel we actually guard
    # is the `mimir` CLI — which is killed by the ~/.local tmpfs mask above (the
    # binary is gone regardless of PATH). The DB port at 127.0.0.1:5450 staying
    # technically open is harmless: there is no mimir/mimir-mcp/psql in the
    # sandbox to query it, and the mimir config points at a dead DB. We do NOT
    # attempt full network isolation here — it adds no validity to the eval.
    bw += [
        "--unshare-pid",
        "--die-with-parent",
        "--new-session",
        "--chdir", spec.workdir,
        "--setenv", "PATH", pinned_path,
        "--setenv", "HOME", spec.home,
        "--setenv", "CLAUDE_CONFIG_DIR", cfg_dir,
        # Pin mimir's DSN file explicitly too, in case a future binary honours it.
        "--setenv", "MIMIR_CONFIG", mimir_cfg_dst,
        # Keep API auth + terminal sanity; everything else is dropped.
        "--setenv", "TERM", os.environ.get("TERM", "xterm"),
    ]
    # Forward ONLY the credentials the actor legitimately needs (the API key).
    # Never forward anything that points back at the live graph.
    for key in ("ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN",
                "CLAUDE_CODE_OAUTH_TOKEN", "ANTHROPIC_BASE_URL",
                "ANTHROPIC_MODEL", "LANG", "LC_ALL"):
        val = os.environ.get(key)
        if val:
            bw += ["--setenv", key, val]

    return bw + ["--"] + list(cmd)


def _prepare_sandbox_home(spec: SandboxSpec) -> str:
    """Create the fresh per-run HOME skeleton on the host: .config/mimir exists
    (so the ro-bind target is present) but no user state leaks in."""
    sandbox_home = tempfile.mkdtemp(prefix="mimir-eval-home-")
    os.makedirs(os.path.join(sandbox_home, ".config", "mimir"), exist_ok=True)
    # The ro-bind needs a destination file to exist under the bound HOME.
    open(os.path.join(sandbox_home, ".config", "mimir", "config.toml"),
         "w").close()
    return sandbox_home


# ---------------------------------------------------------------------------
# Public entry points
# ---------------------------------------------------------------------------

def run(cmd: list, workdir: str, *, timeout: Optional[float] = None,
        spec: Optional[SandboxSpec] = None,
        runtime: Optional[dict] = None,
        capture_output: bool = True,
        share_net: bool = False) -> subprocess.CompletedProcess:
    """Run `cmd` inside the isolation sandbox with `workdir` as the cwd and the
    only writable path. Mirrors subprocess.run's return/timeout semantics so the
    runner can drop it in place of its old raw subprocess.run(...)."""
    if spec is None:
        spec = SandboxSpec(workdir=str(workdir), share_net=share_net)
    if runtime is None:
        runtime = resolve_runtime()
    sandbox_home = _prepare_sandbox_home(spec)
    try:
        argv = build_command(cmd, spec, runtime, sandbox_home)
        return subprocess.run(
            argv,
            capture_output=capture_output,
            text=True,
            timeout=timeout,
            # The actor MUST NOT inherit the parent's mimir-reachable env; bwrap
            # --setenv pins what it gets, but we also start from a clean env so
            # nothing (e.g. a stray PATH) slips through bwrap's inheritance.
            env={"PATH": "/usr/bin:/bin"},
        )
    finally:
        shutil.rmtree(sandbox_home, ignore_errors=True)


def preview(cmd: list, workdir: str, *,
            spec: Optional[SandboxSpec] = None,
            runtime: Optional[dict] = None) -> str:
    """Return the bwrap argv as a copy-pasteable shell string (for --dry-run / QA).
    Uses a throwaway sandbox HOME so the string is realistic but creates nothing
    that outlives the call."""
    if spec is None:
        spec = SandboxSpec(workdir=str(workdir))
    if runtime is None:
        runtime = resolve_runtime()
    sandbox_home = _prepare_sandbox_home(spec)
    try:
        argv = build_command(cmd, spec, runtime, sandbox_home)
        return " ".join(shlex.quote(a) for a in argv)
    finally:
        shutil.rmtree(sandbox_home, ignore_errors=True)


# ---------------------------------------------------------------------------
# CLI: self-probe. `python -m harness.sandbox --probe` runs the offline
# isolation probe (no claude, no API) and exits non-zero if any leak is open.
# ---------------------------------------------------------------------------

_PROBE_SCRIPT = r'''
set -u
fail=0
echo "=== mimir CLI reachability ==="
if command -v mimir >/dev/null 2>&1; then
  echo "LEAK: mimir resolved to $(command -v mimir)"; fail=1
else
  echo "ok: mimir not found"
fi
if command -v mimir-mcp >/dev/null 2>&1; then
  echo "LEAK: mimir-mcp resolved to $(command -v mimir-mcp)"; fail=1
else
  echo "ok: mimir-mcp not found"
fi
echo "=== required tools present ==="
for t in claude bash python3; do
  if command -v "$t" >/dev/null 2>&1; then echo "ok: $t -> $(command -v $t)";
  else echo "MISSING: $t"; fail=1; fi
done
echo "=== postgres client (a raw DB channel would need one) ==="
if command -v psql >/dev/null 2>&1; then
  echo "LEAK: psql resolved to $(command -v psql)"; fail=1
else
  echo "ok: psql not found"
fi
echo "=== live DB port (shared net -> open; informational, no client to use it) ==="
if timeout 3 bash -c 'exec 3<>/dev/tcp/127.0.0.1/5450' 2>/dev/null; then
  echo "info: DB port 5450 open"
else
  echo "info: DB port 5450 closed"
fi
echo "=== CLAUDE_CONFIG_DIR hooks ==="
if [ -f "$CLAUDE_CONFIG_DIR/settings.json" ]; then
  echo "ok: settings.json -> $CLAUDE_CONFIG_DIR/settings.json"
  cat "$CLAUDE_CONFIG_DIR/settings.json"
else
  echo "MISSING: sandbox settings.json"; fail=1
fi
echo "PROBE_RESULT=$fail"
exit $fail
'''


def _main() -> int:
    import argparse
    ap = argparse.ArgumentParser(description="mimir-eval isolation sandbox")
    ap.add_argument("--probe", action="store_true",
                    help="run the OFFLINE leak probe inside the sandbox (no claude/API)")
    ap.add_argument("--preview", action="store_true",
                    help="print the bwrap argv for a sample claude command")
    args = ap.parse_args()

    runtime = resolve_runtime()
    workdir = tempfile.mkdtemp(prefix="mimir-eval-probe-wd-")
    try:
        if args.preview:
            print(preview([runtime["bash"], "-c", "true"], workdir, runtime=runtime))
            return 0
        # default: probe
        proc = run([runtime["bash"], "-c", _PROBE_SCRIPT], workdir,
                   timeout=60, runtime=runtime)
        print(proc.stdout, end="")
        if proc.stderr:
            print("--- stderr ---", proc.stderr, sep="\n", end="")
        return proc.returncode
    finally:
        shutil.rmtree(workdir, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(_main())

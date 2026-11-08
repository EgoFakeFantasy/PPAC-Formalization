"""Prepare the pinned original slice and run the real unprivileged Comparator.

The Linux run must be launched by systemd with NoNewPrivileges and blocked network syscalls.
ABI 8 or newer is required; unavailable optional ABI 9/10 network features
are covered by the outer network filter, not silently left accessible. This program never substitutes a fake sandbox.
"""
from __future__ import annotations

import argparse
import ctypes
import platform
import errno
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import socket
import subprocess
import sys

from source_hash import POLICY, source_sha256

ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / "docs/ORIGINAL_COMPARATOR_LOCK.json").read_text(encoding="utf-8"))


def git_head(path: Path) -> str:
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8", newline="\n")


def prepare(source: Path, project: Path) -> None:
    source, project = source.resolve(), project.resolve()
    source_lock = json.loads((ROOT / "docs/SOURCE_LOCK.json").read_text(encoding="utf-8"))
    if git_head(source) != LOCK["openai_commit"] or source_lock["openai_commit"] != LOCK["openai_commit"]:
        raise RuntimeError("Original source pin mismatch")
    if subprocess.check_output(["git", "-C", str(source), "status", "--porcelain"], text=True).strip():
        raise RuntimeError("Original source checkout is not clean")
    if project.exists():
        raise FileExistsError("Refusing to reuse or overwrite an existing original project")
    config_name = "ComparatorChallenges/PartitionConsistency.json"
    config = json.loads((source / "lean" / config_name).read_text(encoding="utf-8"))
    if config != LOCK["comparator_config"]:
        raise RuntimeError("Original Comparator question/config changed")
    toolchain = (source / "lean/lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != LOCK["lean_toolchain"]:
        raise RuntimeError("Original Lean toolchain changed")
    manifest = json.loads((source / "lean/lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != LOCK["mathlib_commit"]:
        raise RuntimeError("Original mathlib pin changed")
    names = [*source_lock["files"], "lean/ComparatorChallenges/PartitionConsistency.lean",
             "lean/" + config_name, "lean/lean-toolchain"]
    if len(names) != 78 or len(names) != len(set(names)):
        raise RuntimeError("Original proof/challenge closure changed")
    # Validate every input before writing any project file.
    for name in names:
        rel = PurePosixPath(name)
        if rel.parts[0] != "lean" or ".." in rel.parts:
            raise RuntimeError("Source path escaped the original Lean slice")
        expected = source_lock["files"].get(name)
        if expected is not None and source_sha256(source / name) != expected:
            raise RuntimeError("Pinned proof source changed: " + name)
    project.mkdir(parents=True)
    copied = {}
    for name in names:
        rel = str(PurePosixPath(name).relative_to("lean"))
        dest = project / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / name, dest)
        if dest.read_bytes() != (source / name).read_bytes():
            raise RuntimeError("Source copy is not byte-identical: " + name)
        copied[rel] = hashlib.sha256(dest.read_bytes()).hexdigest()
    # Reuse the already accepted minimal original baseline: only mathlib is
    # needed by the unchanged 75 proof modules and the original challenge.
    lakefile = '''name = "ppac_source_baseline"
version = "0.1.0"
defaultTargets = ["OAI.SetTheory.PartitionConsistency.Main"]
[leanOptions]
autoImplicit = false
[[lean_lib]]
name = "OAI"
[[lean_lib]]
name = "ComparatorChallenges"
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "''' + LOCK["mathlib_commit"] + '"\n'
    (project / "lakefile.toml").write_text(lakefile, encoding="utf-8", newline="\n")
    write_json(project / "comparator-inputs.json", {
        "source_hash_policy": POLICY, "lock": LOCK, "source_copies": copied,
        "trusted_minimal_lakefile_sha256": hashlib.sha256(lakefile.encode()).hexdigest(),
        "solution_precompiled_at_preparation": False,
        "scope": "Original external Comparator only; final object Con remains unproved.",
    })
    print("PASS: 78 byte-identical original inputs; pinned minimal 4.34.1 project prepared")


def check_inputs(project: Path) -> dict:
    data = json.loads((project / "comparator-inputs.json").read_text(encoding="utf-8"))
    if data["lock"] != LOCK:
        raise RuntimeError("Comparator lock changed after preparation")
    for name, digest in data["source_copies"].items():
        if hashlib.sha256((project / name).read_bytes()).hexdigest() != digest:
            raise RuntimeError("Original input changed: " + name)
    if hashlib.sha256((project / "lakefile.toml").read_bytes()).hexdigest() != data["trusted_minimal_lakefile_sha256"]:
        raise RuntimeError("Trusted original build configuration changed")
    return data


def require_supported_abi(abi: int) -> int:
    if abi < 8:
        raise RuntimeError(f"Landlock ABI {abi} is below required ABI 8; refusing fallback")
    return abi


def check_process_status(text: str) -> None:
    status = dict(line.split(":", 1) for line in text.splitlines() if ":" in line)
    if status.get("NoNewPrivs", "").strip() != "1" or int(status.get("CapEff", "1").strip(), 16) != 0:
        raise RuntimeError("Required unprivileged NoNewPrivileges guard is absent")


def check_network_denial(factory=None) -> None:
    factory = socket.socket if factory is None else factory
    for family, kind in [(socket.AF_UNIX, socket.SOCK_STREAM),
                         (socket.AF_INET, socket.SOCK_STREAM), (socket.AF_INET, socket.SOCK_DGRAM),
                         (socket.AF_INET6, socket.SOCK_STREAM), (socket.AF_INET6, socket.SOCK_DGRAM)]:
        try:
            sock = factory(family, kind)
        except OSError as error:
            if error.errno not in (errno.EAFNOSUPPORT, errno.EPERM, errno.EACCES):
                raise
        else:
            sock.close()
            raise RuntimeError(f"Network restriction absent for family={family}, kind={kind}")


def sandbox_preflight(landrun: Path, output: Path) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    if sys.platform != "linux" or os.geteuid() == 0:
        raise RuntimeError("Real Comparator acceptance requires unprivileged Linux")
    if platform.machine() != "x86_64":
        raise RuntimeError("Pinned Landlock ABI probe supports the actual x86_64 runner only")
    check_process_status(Path("/proc/self/status").read_text())
    check_network_denial()
    libc = ctypes.CDLL(None, use_errno=True)
    libc.syscall.restype = ctypes.c_long
    # Linux x86_64 landlock_create_ruleset(NULL, 0, VERSION).
    abi = require_supported_abi(libc.syscall(444, None, 0, 1))
    if git_head(landrun.parent) != LOCK["landrun_commit"]:
        raise RuntimeError("Pinned real landrun repository mismatch")
    # Match official Comparator Main.buildLandrunArgs. ABI>=8 preserves all
    # requested filesystem rights (through V5) and IPC scopes (V6). The V9
    # pathname-socket and V10 UDP controls are superseded by the mandatory
    # systemd network syscall filter. No ABI<8/no-Landlock fallback is accepted.
    args = [str(landrun), "--best-effort", "--ro", "/", "--rox", "/usr", "-ldd", "-add-exec", "--"]
    subprocess.run([*args, "/usr/bin/true"], check=True)
    original = output / "landlock-existing-probe"
    created = output / "landlock-created-probe"
    renamed = output / "landlock-renamed-probe"
    original.write_text("unchanged guard probe\n", encoding="utf-8")
    for probe in (created, renamed):
        if probe.exists():
            raise RuntimeError("Stale sandbox probe path: " + str(probe))
    operations = {
        "create": f"open({str(created)!r}, 'w').close()",
        "overwrite": f"open({str(original)!r}, 'w').write('changed')",
        "truncate": f"import os; os.truncate({str(original)!r}, 0)",
        "rename": f"import os; os.rename({str(original)!r}, {str(renamed)!r})",
        "unlink": f"import os; os.unlink({str(original)!r})",
    }
    denial_logs = []
    for operation, code in operations.items():
        result = subprocess.run([*args, sys.executable, "-c", code], capture_output=True, text=True,
                                env={**os.environ, "LC_ALL": "C"})
        denial_logs.append(f"[{operation}] exit={result.returncode}\n{result.stdout}{result.stderr}")
        if result.returncode == 0 or "Permission denied" not in result.stderr:
            raise RuntimeError("Real Landlock denial was not verified: " + operation)
        if created.exists() or renamed.exists() or original.read_text() != "unchanged guard probe\n":
            raise RuntimeError("Sandbox probe modified a forbidden file: " + operation)
    (output / "landlock-denial.log").write_text("\n".join(denial_logs), encoding="utf-8")
    original.unlink()
    guards = {"landlock_abi": abi, "minimum_abi": 8, "unprivileged": True,
              "NoNewPrivileges": True, "AF_UNIX_TCP_UDP_socket_creation_denied": True,
              "real_landrun_positive_execution": True,
              "real_filesystem_denials": list(operations),
              "official_best_effort_invocation_with_fail_closed_abi_floor": True}
    write_json(output / "sandbox-guards.json", guards)
    print(f"PASS: Landlock ABI {abi}; real execution, five filesystem denials and network denial")
    return guards


def run(project: Path, comparator: Path, landrun: Path, exporter: Path, output: Path) -> None:
    guards = sandbox_preflight(landrun, output)
    data = check_inputs(project)
    for path, key in [(comparator.parents[3], "comparator_commit"),
                      (exporter.parents[3], "lean4export_commit"), (landrun.parent, "landrun_commit")]:
        if git_head(path) != LOCK[key]:
            raise RuntimeError("Comparator tool pin mismatch: " + key)
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    if not version.startswith("Lean (version 4.34.1,"):
        raise RuntimeError("Comparator toolchain mismatch: " + version)
    env = {**os.environ, "COMPARATOR_LANDRUN": str(landrun), "COMPARATOR_LEAN4EXPORT": str(exporter),
           "LEAN_NUM_THREADS": "1"}
    env.pop("COMPARATOR_NANODA", None)
    command = ["lake", "env", str(comparator), "ComparatorChallenges/PartitionConsistency.json"]
    marker = False
    with (output / "comparator.log").open("w", encoding="utf-8", newline="\n") as log:
        process = subprocess.Popen(command, cwd=project, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True)
        assert process.stdout is not None
        for line in process.stdout:
            log.write(line)
            print(line, end="", flush=True)
            marker |= "Your solution is okay!" in line
        code = process.wait()
    check_inputs(project)
    if code != 0 or not marker:
        raise RuntimeError(f"Original Comparator did not accept: exit={code}, success_marker={marker}")
    write_json(output / "acceptance.json", {
        "status": "accepted", "command": command, "exit_code": code, "lean_version": version,
        "unprivileged": True, "NoNewPrivileges": True, "AF_UNIX_denied": True,
        "sandbox_guards": guards,
        "input_hashes_unchanged": len(data["source_copies"]), "lock": LOCK,
        "comparator_log_sha256": hashlib.sha256((output / "comparator.log").read_bytes()).hexdigest(),
        "scope": "Original external Comparator passed; nativeZF internal Con is NOT proved by this run.",
    })
    print("PASS: original Comparator accepted under verified real sandbox guards")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="mode", required=True)
    prep = commands.add_parser("prepare")
    prep.add_argument("--source", type=Path, required=True)
    prep.add_argument("--project", type=Path, required=True)
    execute = commands.add_parser("run")
    for name in ("project", "comparator", "landrun", "exporter", "output"):
        execute.add_argument("--" + name, type=lambda p: Path(p).resolve(), required=True)
    guard = commands.add_parser("guard")
    guard.add_argument("--landrun", type=lambda p: Path(p).resolve(), required=True)
    guard.add_argument("--output", type=lambda p: Path(p).resolve(), required=True)
    args = parser.parse_args()
    if args.mode == "prepare":
        prepare(args.source, args.project)
    elif args.mode == "guard":
        sandbox_preflight(args.landrun, args.output)
    else:
        run(args.project, args.comparator, args.landrun, args.exporter, args.output)


if __name__ == "__main__":
    main()

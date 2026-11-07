"""Check the exact source/dependency inputs of a fresh local or CI checkout."""
import json
import subprocess
from pathlib import Path
from source_hash import POLICY, source_sha256

ROOT = Path(__file__).resolve().parents[1]


def check_repo(path: Path, expected: str) -> str:
    if not (path / ".git").exists():
        raise RuntimeError(f"Missing pinned repository {path}; follow README setup before verification")
    actual = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
    if actual != expected:
        raise RuntimeError(f"Pinned revision mismatch for {path.name}: {actual}, expected {expected}")
    if subprocess.check_output(["git", "-C", str(path), "status", "--porcelain"], text=True).strip():
        raise RuntimeError(f"Pinned source repository has tracked/untracked changes: {path}")
    return actual


def main() -> None:
    lock = json.loads((ROOT / "docs/SOURCE_LOCK.json").read_text(encoding="utf-8"))
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    native = next(p for p in manifest["packages"] if p["name"] == "YesMetaZFC")
    package = ROOT / manifest["packagesDir"] / "YesMetaZFC"
    if not package.exists():
        raise RuntimeError("YesMetaZFC is not materialized; run `lake update` before the source audit")
    pins = {
        "YesMetaZFC": check_repo(package, native["rev"]),
        "L_donor": check_repo(ROOT.parent / "yesmetazfc-analytic-comprehension", lock["companion_reuse"]["native_internal_L"]["commit"]),
        "OpenAI": check_repo(ROOT.parent / "openai-math-ppac-source", lock["openai_commit"]),
    }
    for name, expected in lock["files"].items():
        path = ROOT.parent / "openai-math-ppac-source" / name
        if source_sha256(path) != expected:
            raise RuntimeError(f"Pinned OpenAI source changed: {name}")
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)
    result = {"source_hash_policy": POLICY, "clean_pins": pins, "source_hashes_verified": len(lock["files"])}
    (out / "ci-inputs.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"PASS: all three pinned clean repositories and {len(lock['files'])} source hashes; {POLICY}")


if __name__ == "__main__":
    main()

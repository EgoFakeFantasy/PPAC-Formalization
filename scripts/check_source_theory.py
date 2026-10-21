"""Compare all nine source ZF constructors against the pinned OpenAI excerpt."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main():
    lock = json.loads((ROOT / "docs/SOURCE_THEORY_LOCK.json").read_text(encoding="utf-8"))
    provenance = json.loads((ROOT / "docs/SOURCE_LOCK.json").read_text(encoding="utf-8"))
    if lock["openai_commit"] != provenance["openai_commit"] or lock["source_sha256"] != provenance["files"][lock["source_path"]]:
        raise RuntimeError("Source ZF provenance disagrees with SOURCE_LOCK")
    ref = ROOT / "third_party/openai/PartitionConsistency.zf-axioms.txt"
    if hashlib.sha256(ref.read_bytes()).hexdigest() != lock["excerpt_sha256"]:
        raise RuntimeError("Pinned source ZF excerpt changed")
    expected = ref.read_text(encoding="utf-8").strip()
    actual = (ROOT / "PPAC/Migration/SourceTheory.lean").read_text(encoding="utf-8-sig")
    actual = actual[actual.index("inductive IsZFAxiom :"):actual.index("def ZF :")].strip()
    if expected != actual or sum(line.startswith("  | ") for line in actual.splitlines()) != 9:
        raise RuntimeError("Source ZF constructors differ from pinned excerpt")
    print("PASS: all 9 source ZF constructors match the pinned excerpt, including full parameter schemas")

if __name__ == "__main__":
    main()

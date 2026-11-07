"""Check that all 19 input rules match the pinned OpenAI excerpt."""
from pathlib import Path
from source_hash import source_sha256
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
def main():
    lock = json.loads((ROOT / "docs/SOURCE_RULES_LOCK.json").read_text(encoding="utf-8"))
    ref = ROOT / "third_party/openai/PartitionConsistency.rules.txt"
    if source_sha256(ref) != lock["rules_excerpt_sha256"]:
        raise RuntimeError("Pinned source rules excerpt changed")
    expected = ref.read_text(encoding="utf-8")
    replacements = [
        ("ℕ", "Nat"), ("Set (Formula n)", "Context n"),
        ("p ∈ Γ", "Γ p"), ("Γ ⊆ Δ", "(∀ q, Γ q → Δ q)"),
        ("insert p Γ", "Context.add p Γ"), ("insert p.neg Γ", "Context.add p.neg Γ"),
        ("insert q Γ", "Context.add q Γ"),
        ("Formula.raise \'\' Γ", "Context.image Formula.raise Γ"),
        ("Formula.rename r \'\' Γ", "Context.image (Formula.rename r) Γ"),
        ("insert p (Context.image", "Context.add p (Context.image"),
    ]
    for old, new in replacements:
        expected = expected.replace(old, new)
    actual = (ROOT / "PPAC/Migration/SourceDerivation.lean").read_text(encoding="utf-8-sig")
    actual = actual[actual.index("inductive Derives :"):actual.index("abbrev Theory :=")]
    if expected.strip() != actual.strip():
        raise RuntimeError("Adapted source calculus differs from the pinned 19 rules")
    print("PASS: all 19 source rules match the pinned excerpt")
if __name__ == "__main__":
    main()

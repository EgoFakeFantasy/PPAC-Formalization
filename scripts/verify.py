"""Rebuild and check the explicitly enumerated Lean declaration audit."""
from __future__ import annotations

import os
import sys
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
COMMANDS: list[dict] = []


def strip_comments(text: str) -> str:
    """Remove Lean line/nested block comments, preserving line boundaries."""
    result: list[str] = []
    i, depth = 0, 0
    while i < len(text):
        pair = text[i:i + 2]
        if pair == "/-":
            depth += 1
            result.append(" ")
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                result.append("\n")
            i += 1
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise RuntimeError("Unterminated block comment")
    return "".join(result)


def run(command: list[str], log: str) -> str:
    result = subprocess.run(command, cwd=ROOT, env={**os.environ, "LEAN_NUM_THREADS": "1"}, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
    (OUT / log).write_text(result.stdout, encoding="utf-8", newline="\n")
    COMMANDS.append({"command": command, "exit_code": result.returncode, "log": log})
    (OUT / "commands.json").write_text(json.dumps(COMMANDS, indent=2) + "\n", encoding="utf-8")
    if result.returncode:
        raise RuntimeError(f"{' '.join(command)} failed; see verification/{log}")
    return result.stdout


def main() -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / "summary.json").unlink(missing_ok=True)
    sources = sorted([ROOT / "PPAC.lean", ROOT / "Audit.lean", ROOT / "Check.lean", ROOT / "CheckStep2.lean", ROOT / "CheckStep3.lean", *ROOT.glob("PPAC/**/*.lean")])
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide)\b")
    for path in sources:
        if forbidden.search(strip_comments(path.read_text(encoding="utf-8-sig"))):
            raise RuntimeError(f"Forbidden token in {path.relative_to(ROOT)}")
    audit_source = strip_comments((ROOT / "Audit.lean").read_text(encoding="utf-8-sig"))
    expected = re.findall(r"^#print axioms (\S+)", audit_source, re.MULTILINE)
    if not expected or len(expected) != len(set(expected)):
        raise RuntimeError("Empty or duplicate audit declarations")
    run([sys.executable, "scripts/check_source_rules.py"], "source-rules.log")
    run([sys.executable, "scripts/check_source_theory.py"], "source-theory.log")
    version = run(["lake", "env", "lean", "--version"], "lean-version.log").strip()
    build = run(["lake", "--no-cache", "--wfail", "build"], "build.log")
    run(["lake", "env", "lean", "--trust=0", "Check.lean"], "check.log")
    run(["lake", "env", "lean", "--trust=0", "CheckStep2.lean"], "step2-check.log")
    run(["lake", "env", "lean", "--trust=0", "CheckStep3.lean"], "step3-check.log")
    audit = run(["lake", "env", "lean", "--trust=0", "Audit.lean"], "audit.log")
    footprints: dict[str, list[str]] = {}
    for name, empty, dependencies in re.findall(
            r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", audit):
        if name in footprints:
            raise RuntimeError(f"Duplicate audit output: {name}")
        footprints[name] = [] if empty.startswith("does not") else [x.strip() for x in dependencies.split(",")]
    if set(footprints) != set(expected):
        raise RuntimeError("Audit output does not match the enumerated declarations")
    allowed = {"propext", "Quot.sound"}
    inherited = set(json.loads((ROOT / "docs/TRUST_BASELINE.json").read_text(encoding="utf-8"))["native_certificate_axioms"])
    contracts = {x for x in footprints if x.startswith("PPAC.Migration.target_derives_")} | {
        "PPAC.Migration.consistent_ZF_of_target", "PPAC.Migration.no_AC_of_target_consistent"}
    for name, dependencies in footprints.items():
        extra = set(dependencies) - allowed
        expected_extra = inherited if name in contracts else ({"Classical.choice"} if name.startswith("PPAC.Migration.Translation.") else set())
        is_step2 = any(name.startswith("PPAC.Migration." + prefix) for prefix in
            ["Syntax.", "Compile.", "FiniteSupport.", "TheoryTransport."])
        is_step3_logic = any(name.startswith("PPAC.Migration." + prefix) for prefix in
            ["Normalization.", "Reverse.", "Presentation.", "FormulaEquivalence.", "ProjectSyntax.", "ProjectNormalization."])
        if name.startswith(("PPAC.Migration.ZFEquivalence.", "PPAC.Migration.SeparationSyntax.")):
            if not set(dependencies) <= allowed | {"Classical.choice"} | inherited:
                raise RuntimeError(f"Unexpected fixed-ZF axiom dependency: {name}: {dependencies}")
            continue
        if is_step2 or is_step3_logic:
            if not set(dependencies) <= allowed | {"Classical.choice"}:
                raise RuntimeError(f"Unexpected syntax/transport axiom dependency: {name}: {dependencies}")
            continue
        if extra != expected_extra:
            raise RuntimeError(f"Unexpected axiom dependency: {name}: {dependencies}")
    hashed = sources + sorted(ROOT.glob("third_party/openai/*.txt")) + [ROOT / x for x in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "scripts/verify.py", "scripts/check_source_rules.py", "scripts/check_source_theory.py", "docs/SOURCE_THEORY_LOCK.json", "docs/SOURCE_RULES_LOCK.json", "docs/TRUST_BASELINE.json"]]
    summary = {
        "lean_version": version,
        "build_passed": True,
        "audit_passed": True,
        "check_passed": True,
        "step2_check_passed": True,
        "step3_check_passed": True,
        "source_ZF_axiom_constructors": 9,
        "source_ZF_matches_pinned_excerpt": True,
        "native_formula_normalization_object_equivalence": True,
        "fixed_ZF_axioms_with_bidirectional_derivations": ["extensionality", "emptySet", "pairing", "union", "powerSet", "infinity", "foundation"],
        "all_source_Separation_instances_transported": True,
        "all_native_Project_Separation_instances_reverse_transported": False,
        "full_ZF_equivalence_proved": False,
        "reverse_native_to_source_derivation_compiler_proved": False,
        "choice_presentations_equivalent_proved": False,
        "source_rule_count": 19,
        "source_rules_match_pinned_excerpt": True,
        "object_Con_theorem_proved": False,
        "trust_level": 0,
        "original_openai_build_run": False,
        "relative_consistency_proved": False,
        "audited_declarations": len(footprints),
        "declarations_without_axioms": sum(not value for value in footprints.values()),
        "declarations_with_allowed_axioms": sum(bool(value) for value in footprints.values()),
        "allowed_standard_axioms": sorted(allowed | {"Classical.choice"}),
        "semantic_bridge_choice_origin": "Lean core Fin.lastCases_castSucc; proof-only, not object AC or extracted data",
        "inherited_native_certificate_axioms": sorted(inherited),
        "standard_axiom_only": False,
        "new_custom_axioms": [],
        "warning_lines": sum("warning:" in line for item in COMMANDS for line in (OUT / item["log"]).read_text(encoding="utf-8").splitlines()),
        "scope": "Steps 1-2 and step 3a: full reverse syntax, original-kernel normalization and presentation replay; all seven fixed ZF axioms in both directions and all source Separation instances. Full ZF/AC equivalences, reverse source-calculus compiler and internal Con proof remain pending.",
        "footprints": footprints,
        "sha256": {str(path.relative_to(ROOT)).replace("\\", "/"): hashlib.sha256(path.read_bytes()).hexdigest() for path in hashed},
    }
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    print(f"PASS: {len(footprints)} audited declarations; "
          f"{summary['declarations_without_axioms']} without axioms; "
          f"{summary['declarations_with_allowed_axioms']} with recorded dependencies; "
          f"{summary['warning_lines']} warning lines; inherited native certificate axioms recorded.")


if __name__ == "__main__":
    main()

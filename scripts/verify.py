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
    sources = sorted([ROOT / "PPAC.lean", ROOT / "Audit.lean", ROOT / "Check.lean", ROOT / "CheckStep2.lean", ROOT / "CheckStep3.lean", ROOT / "CheckStep4.lean", *ROOT.glob("PPAC/**/*.lean")])
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
    run(["lake", "env", "lean", "--trust=0", "CheckStep4.lean"], "step4-check.log")
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
    choice_baseline = json.loads((ROOT / "docs/CHOICE_TRUST_BASELINE.json").read_text(encoding="utf-8"))
    inherited_choice = set(choice_baseline["additional_active_inherited_certificate_axioms"])
    if inherited_choice != {"YesMetaZFC.SetTheory.Axioms.choice._native.native_decide.ax_1"}:
        raise RuntimeError("Unexpected native-choice certificate baseline")
    choice_source = ROOT / choice_baseline["source_file"]
    if hashlib.sha256(choice_source.read_bytes()).hexdigest() != choice_baseline["source_sha256"]:
        raise RuntimeError("Native-choice original source hash changed")
    contracts = {x for x in footprints if x.startswith("PPAC.Migration.target_derives_")} | {
        "PPAC.Migration.consistent_ZF_of_target", "PPAC.Migration.no_AC_of_target_consistent"}
    for name, dependencies in footprints.items():
        extra = set(dependencies) - allowed
        expected_extra = inherited if name in contracts else ({"Classical.choice"} if name.startswith("PPAC.Migration.Translation.") else set())
        is_step2 = any(name.startswith("PPAC.Migration." + prefix) for prefix in
            ["Syntax.", "Compile.", "FiniteSupport.", "TheoryTransport."])
        is_step3_logic = any(name.startswith("PPAC.Migration." + prefix) for prefix in
            ["Normalization.", "Reverse.", "Presentation.", "FormulaEquivalence.", "ProjectSyntax.", "ProjectNormalization.", "ProjectDecode.", "SeparationReverse.", "SourceAlgebra.", "SourceLogic.", "SourcePropositional.", "SourceQuantifiers.", "ReverseSubstitution.", "ReverseLogicalAxioms.", "ReverseCompile.", "MinimalPredicates.", "MinimalLogic.", "MinimalInstances.", "BoundedMinimal.", "BoundedInduction.", "PairSyntax.", "UnorderedPairLogic.", "OrderedPairExistence.", "OrderedPairElimination.", "OrderedPairWitnesses.", "OrderedPairLogic.", "ObjectPairs.", "GraphSyntax.", "GraphLogic.", "GraphProperties.", "SingletonGraphLogic.", "SingletonMap.", "ObjectGraphs.", "InsertSyntax.", "InsertLogic.", "InsertExistence.", "GraphInsertEdges.", "GraphInsertEntries.", "GraphInsertValues.", "GraphInsertFunction.", "GraphInsertSyntax.", "GraphInsertExistence.", "ObjectGraphInsert.", "RestrictionSyntax.", "RestrictionEdges.", "RestrictionFunction.", "RestrictionAlgebra.", "RestrictionExistence.", "ObjectRestriction.", "GraphDomainSyntax.", "GraphDomainBound.", "GraphDomainExistence.", "GraphDomainAlgebra.", "GraphFamilySyntax.", "GraphFamilyEdges.", "GraphFamilyValues.", "GraphFamilyEntries.", "GraphFamilyFunction.", "GraphFamilyExistence.", "GraphFamilyEmpty.", "ObjectGraphFamily.", "OmegaSyntax.", "OmegaUniversal.", "OmegaCut.", "OmegaExistence.", "OmegaAlgebra.", "OmegaInductionSyntax.", "OmegaInductionCut.", "OmegaInduction.", "ObjectOmega.", "OmegaStructureSyntax.", "ObjectIrreflexivity.", "OmegaElementary.", "OmegaStructureInduction.", "OmegaStructureAlgebra.", "ObjectOmegaStructure.", "GraphPointwiseSyntax.", "GraphPointwiseEntries.", "GraphPointwise.", "GraphPointwiseDomain.", "ObjectGraphPointwise.", "IterationSyntax.", "IterationValues.", "IterationStep.", "IterationInduction.", "IterationCompatibility.", "ObjectIterationUniqueness.", "FiniteIterationSyntax.", "IterationBase.", "IterationBaseExistence.", "IterationExtensionAlgebra.", "IterationExtension.", "IterationExtensionExistence.", "IterationExistence.", "FiniteIterationUniqueness.", "ObjectFiniteIteration.", "IterationContext.", "IterationValueSyntax.", "IterationValueExistence.", "IterationValueUniqueness.", "IterationValueCollection.", "IterationValueStep.", "IterationRangeSyntax.", "IterationRangeSeed.", "IterationRangeClosed.", "TransitiveCoverSyntax.", "TransitiveCoverLogic.", "TransitiveCoverExistence.", "ObjectTransitiveCover.", "SetInductionSyntax.", "SetInductionLogic.", "SetInduction.", "GlobalMinimalSyntax.", "GlobalMinimal.", "OrdinalSyntax.", "OrdinalFoundation.", "OrdinalTransitivity.", "OrdinalRestriction.", "OrdinalEmpty.", "OrdinalSuccessor.", "ObjectOrdinalBasic.", "OrdinalDifference.", "OrdinalInitialSegment.", "OrdinalComparison.", "OrdinalTrichotomy.", "ObjectOrdinalComparison.", "OrdinalFamilySyntax.", "OrdinalFamilyOrder.", "UnionUpperBounds.", "OrdinalUnion.", "OrdinalStrictBound.", "ObjectOrdinalUnion.", "OrdinalRecursionSyntax.", "RestrictionHistory.", "OrdinalRecursionRestriction.", "OrdinalRecursionDeterminism.", "OrdinalRecursionHistory.", "OrdinalRecursionValues.", "OrdinalRecursionCompatibility.", "ObjectOrdinalRecursion.", "GraphInsertRestriction.", "OrdinalRecursionTotal.", "GraphInsertElimination.", "OrdinalRecursionExtensionAlgebra.", "OrdinalRecursionExtension.", "OrdinalRecursionSuccessorSyntax.", "OrdinalRecursionSuccessorExistence.", "OrdinalRecursionSuccessorUnique.", "ObjectOrdinalRecursionSuccessor.", "OrdinalRecursionContext.", "OrdinalRecursionFamilySyntax.", "OrdinalRecursionCollection.", "OrdinalRecursionFamilyMembers.", "OrdinalRecursionFamilyCompatibility.", "GraphFamilyRestriction.", "OrdinalRecursionUnionFunction.", "OrdinalRecursionUnion.", "OrdinalRecursionExistenceSyntax.", "OrdinalRecursionExistence.", "OrdinalRecursionUnique.", "ObjectTransfiniteRecursion.", "ObjectTransfiniteRecursionIdentity.", "PowerSetSyntax.", "PowerSetLogic.", "PowerValueSyntax.", "PowerValueLogic.", "PowerValueCollection.", "PowerUnionSyntax.", "PowerUnionOperation.", "ObjectPowerUnion.", "HierarchyRecursion.", "HierarchyLayerSyntax.", "HierarchyLayerExistence.", "HierarchyLayerUnique.", "ObjectCumulativeHierarchy.", "PowerUnionEmpty.", "HierarchyLayerZero.", "HierarchyHistory.", "HierarchyMemberSyntax.", "PowerUnionMembership.", "HierarchyMemberTransfer.", "HierarchyMembership.", "HierarchyAlgebra.", "HierarchySuccessor.", "ObjectHierarchyAlgebra.", "HierarchyClosedInstances.", "HierarchyLimitSyntax.", "HierarchyLimitMembership.", "HierarchyFamilySyntax.", "HierarchyLayerCollection.", "HierarchyFamilyUnion.", "ObjectHierarchyLimit.", "OrdinalLeastSyntax.", "OrdinalLeastLogic.", "OrdinalLeastExistence.", "ObjectOrdinalLeast.", "LayerCoverSyntax.", "LayerRankSyntax.", "LayerCoverClosedInstances.", "LayerRankCollection.", "LayerRankBound.", "LayerCoverInduction.", "LayerCoverMembership.", "ObjectRankCover.", "WitnessRankSyntax.", "WitnessRankFibers.", "WitnessRankCollection.", "WitnessRankBounds.", "CollectionFromReplacement.", "ReverseZFReplay.", "ChoiceSyntax.", "GraphRangeSyntax.", "GraphRangeCollection.", "ChoiceLogic.", "ChoiceSelectorPoints.", "GraphChoiceToSelector.", "ObjectGraphChoiceSelector.", "TaggedRowSyntax.", "TaggedRowExistence.", "TaggedRowLogic.", "TaggedFamilySyntax.", "TaggedFamilyContext.", "TaggedFamilyCollection.", "TaggedFamilyLogic.", "SelectedPairSyntax.", "SelectedPairFiber.", "SelectedGraphLogic.", "SelectedGraphChoice.", "SelectorChoiceToGraph.", "ObjectSelectorGraphChoice.", "ChoiceNativeBridge.", "Internal.", "ReplacementPredicates.", "ExactImage.", "ReplacementInstances.", "ReplacementFromCollection."])
        if name.startswith("PPAC.Migration.ChoiceNativeBridge.") or name == "YesMetaZFC.SetTheory.Axioms.choice":
            if not set(dependencies) <= allowed | {"Classical.choice"} | inherited | inherited_choice:
                raise RuntimeError(f"Unexpected original-choice bridge dependency: {name}: {dependencies}")
            continue
        if name in {"PPAC.Migration.ReplacementFromCollection.native_replacement",
                    "PPAC.Migration.BoundedMinimal.native_minimal", "PPAC.Migration.BoundedInduction.native_induction",
                    "PPAC.Migration.ObjectPairs.native_replay", "PPAC.Migration.ObjectPairs.native_exists_unique",
                    "PPAC.Migration.ObjectPairs.native_characterization",
                    "PPAC.Migration.ObjectGraphs.native_singleton", "PPAC.Migration.ObjectGraphs.native_evaluation",
                    "PPAC.Migration.ObjectGraphs.native_domain", "PPAC.Migration.ObjectGraphs.native_single_valued",
                    "PPAC.Migration.ObjectGraphs.native_total", "PPAC.Migration.ObjectGraphInsert.native_replay",
                    "PPAC.Migration.ObjectGraphInsert.native_insert", "PPAC.Migration.ObjectGraphInsert.native_successor",
                    "PPAC.Migration.ObjectGraphInsert.native_extension", "PPAC.Migration.ObjectGraphInsert.native_edge_law",
                    "PPAC.Migration.ObjectGraphInsert.native_uniqueness", "PPAC.Migration.ObjectRestriction.native_replay",
                    "PPAC.Migration.ObjectRestriction.native_set", "PPAC.Migration.ObjectRestriction.native_function",
                    "PPAC.Migration.ObjectRestriction.native_edge", "PPAC.Migration.ObjectRestriction.native_unique",
                    "PPAC.Migration.ObjectRestriction.native_identity", "PPAC.Migration.ObjectRestriction.native_compose",
                    "PPAC.Migration.ObjectGraphFamily.native_replay", "PPAC.Migration.ObjectGraphFamily.native_domain",
                    "PPAC.Migration.ObjectGraphFamily.native_domain_unique", "PPAC.Migration.ObjectGraphFamily.native_union",
                    "PPAC.Migration.ObjectGraphFamily.native_unique", "PPAC.Migration.ObjectGraphFamily.native_edge",
                    "PPAC.Migration.ObjectGraphFamily.native_empty", "PPAC.Migration.ObjectOmega.native_replay",
                    "PPAC.Migration.ObjectOmega.native_existence", "PPAC.Migration.ObjectOmega.native_unique",
                    "PPAC.Migration.ObjectOmega.native_characterization", "PPAC.Migration.OmegaInduction.native_induction",
                    "PPAC.Migration.ObjectIrreflexivity.native_proof", "PPAC.Migration.ObjectOmegaStructure.native_replay",
                    "PPAC.Migration.ObjectOmegaStructure.native_decomposition",
                    "PPAC.Migration.ObjectOmegaStructure.native_transitive",
                    "PPAC.Migration.ObjectOmegaStructure.native_elements",
                    "PPAC.Migration.ObjectOmegaStructure.native_zero",
                    "PPAC.Migration.ObjectOmegaStructure.native_successor",
                    "PPAC.Migration.ObjectOmegaStructure.native_nonzero",
                    "PPAC.Migration.ObjectOmegaStructure.native_injective",
                    "PPAC.Migration.ObjectOmegaStructure.native_fresh",
                    "PPAC.Migration.ObjectGraphPointwise.native_replay",
                    "PPAC.Migration.ObjectGraphPointwise.native_subset",
                    "PPAC.Migration.ObjectGraphPointwise.native_edges",
                    "PPAC.Migration.ObjectGraphPointwise.native_inclusion",
                    "PPAC.Migration.ObjectGraphPointwise.native_equality",
                    "PPAC.Migration.ObjectGraphPointwise.native_domain",
                    "PPAC.Migration.ObjectGraphPointwise.native_domainUnique",
                    "PPAC.Migration.ObjectIterationUniqueness.native_replay",
                    "PPAC.Migration.ObjectIterationUniqueness.native_common",
                    "PPAC.Migration.ObjectIterationUniqueness.native_compatible",
                    "PPAC.Migration.ObjectIterationUniqueness.native_unique",
                    "PPAC.Migration.ObjectFiniteIteration.native_replay",
                    "PPAC.Migration.ObjectFiniteIteration.native_base",
                    "PPAC.Migration.ObjectFiniteIteration.native_existence",
                    "PPAC.Migration.ObjectFiniteIteration.native_uniqueness",
                    "PPAC.Migration.ObjectTransitiveCover.native_range",
                    "PPAC.Migration.ObjectTransitiveCover.native_properties",
                    "PPAC.Migration.ObjectTransitiveCover.native_cover",
                    "PPAC.Migration.SetInduction.native_induction", "PPAC.Migration.GlobalMinimal.native_minimal",
                    "PPAC.Migration.ObjectOrdinalBasic.native_replay",
                    "PPAC.Migration.ObjectOrdinalBasic.native_wellFounded",
                    "PPAC.Migration.ObjectOrdinalBasic.native_noSelf",
                    "PPAC.Migration.ObjectOrdinalBasic.native_empty",
                    "PPAC.Migration.ObjectOrdinalBasic.native_member",
                    "PPAC.Migration.ObjectOrdinalBasic.native_successor",
                    "PPAC.Migration.ObjectOrdinalBasic.native_existsEmpty",
                    "PPAC.Migration.ObjectOrdinalBasic.native_existsSuccessor",
                    "PPAC.Migration.ObjectOrdinalComparison.native_replay",
                    "PPAC.Migration.ObjectOrdinalComparison.native_difference",
                    "PPAC.Migration.ObjectOrdinalComparison.native_initial",
                    "PPAC.Migration.ObjectOrdinalComparison.native_comparison",
                    "PPAC.Migration.ObjectOrdinalComparison.native_trichotomy",
                    "PPAC.Migration.ObjectOrdinalComparison.native_subset",
                    "PPAC.Migration.ObjectOrdinalComparison.native_asymmetric",
                    "PPAC.Migration.ObjectOrdinalUnion.native_replay",
                    "PPAC.Migration.ObjectOrdinalUnion.native_family",
                    "PPAC.Migration.ObjectOrdinalUnion.native_union",
                    "PPAC.Migration.ObjectOrdinalUnion.native_least",
                    "PPAC.Migration.ObjectOrdinalUnion.native_unique",
                    "PPAC.Migration.ObjectOrdinalUnion.native_existence",
                    "PPAC.Migration.ObjectOrdinalUnion.native_strict",
                    "PPAC.Migration.ObjectOrdinalRecursion.native_replay",
                    "PPAC.Migration.ObjectOrdinalRecursion.native_preservation",
                    "PPAC.Migration.ObjectOrdinalRecursion.native_restriction",
                    "PPAC.Migration.ObjectOrdinalRecursion.native_compatibility",
                    "PPAC.Migration.ObjectOrdinalRecursion.native_uniqueness",
                    "PPAC.Migration.ObjectOrdinalRecursionSuccessor.native_replay",
                    "PPAC.Migration.ObjectOrdinalRecursionSuccessor.native_evaluation",
                    "PPAC.Migration.ObjectOrdinalRecursionSuccessor.native_preservation",
                    "PPAC.Migration.ObjectOrdinalRecursionSuccessor.native_extension",
                    "PPAC.Migration.ObjectOrdinalRecursionSuccessor.native_successor",
                    "PPAC.Migration.ObjectOrdinalRecursionSuccessor.native_unique",
                    "PPAC.Migration.ObjectOrdinalRecursionSuccessor.native_fiber",
                    "PPAC.Migration.ObjectTransfiniteRecursion.native_collection",
                    "PPAC.Migration.ObjectTransfiniteRecursion.native_union",
                    "PPAC.Migration.ObjectTransfiniteRecursion.native_existence",
                    "PPAC.Migration.ObjectTransfiniteRecursion.native_uniqueness",
                    "PPAC.Migration.ObjectTransfiniteRecursionIdentity.native_proof",
                    "PPAC.Migration.ObjectPowerUnion.native_replay",
                    "PPAC.Migration.ObjectPowerUnion.native_range",
                    "PPAC.Migration.ObjectPowerUnion.native_operation",
                    "PPAC.Migration.ObjectPowerUnion.native_total",
                    "PPAC.Migration.ObjectPowerUnion.native_deterministic",
                    "PPAC.Migration.HierarchyRecursion.native_existence",
                    "PPAC.Migration.HierarchyRecursion.native_uniqueness",
                    "PPAC.Migration.ObjectCumulativeHierarchy.native_existence",
                    "PPAC.Migration.ObjectCumulativeHierarchy.native_uniqueness",
                    "PPAC.Migration.ObjectCumulativeHierarchy.native_equality",
                    "PPAC.Migration.ObjectCumulativeHierarchy.native_zero",
                    "PPAC.Migration.ObjectHierarchyAlgebra.native_history",
                    "PPAC.Migration.ObjectHierarchyAlgebra.native_operation",
                    "PPAC.Migration.ObjectHierarchyAlgebra.native_membership",
                    "PPAC.Migration.ObjectHierarchyAlgebra.native_monotone",
                    "PPAC.Migration.ObjectHierarchyAlgebra.native_member",
                    "PPAC.Migration.ObjectHierarchyAlgebra.native_transitive",
                    "PPAC.Migration.ObjectHierarchyAlgebra.native_successor",
                    "PPAC.Migration.ObjectHierarchyLimit.native_equation",
                    "PPAC.Migration.ObjectHierarchyLimit.native_range",
                    "PPAC.Migration.ObjectHierarchyLimit.native_rangeEquality",
                    "PPAC.Migration.ObjectHierarchyLimit.native_union",
                    "PPAC.Migration.ObjectHierarchyLimit.native_assembled",
                    "PPAC.Migration.ObjectHierarchyLimit.native_zero",
                    "PPAC.Migration.ObjectOrdinalLeast.native_existence",
                    "PPAC.Migration.ObjectOrdinalLeast.native_uniqueness",
                    "PPAC.Migration.ObjectOrdinalLeast.native_equality",
                    "PPAC.Migration.ObjectRankCover.native_cover",
                    "PPAC.Migration.ObjectRankCover.native_rank",
                    "PPAC.Migration.ObjectRankCover.native_member",
                    "PPAC.Migration.ObjectRankCover.native_range",
                    "PPAC.Migration.ObjectRankCover.native_equality",
                    "PPAC.Migration.ObjectRankCover.native_property",
                    "PPAC.Migration.CollectionFromReplacement.native_source_matrix",
                    "PPAC.Migration.ObjectGraphChoiceSelector.native_replay",
                    "PPAC.Migration.ObjectGraphChoiceSelector.native_range",
                    "PPAC.Migration.ObjectGraphChoiceSelector.native_selector",
                    "PPAC.Migration.ObjectGraphChoiceSelector.native_forward",
                    "PPAC.Migration.ObjectSelectorGraphChoice.native_replay",
                    "PPAC.Migration.ObjectSelectorGraphChoice.native_family",
                    "PPAC.Migration.ObjectSelectorGraphChoice.native_reverse",
                    "PPAC.Migration.Internal.ObjectSequences.native_replay",
                    "PPAC.Migration.Internal.ObjectSequences.native_empty",
                    "PPAC.Migration.Internal.ObjectSequences.native_value",
                    "PPAC.Migration.Internal.ObjectSequences.native_append",
                    "PPAC.Migration.Internal.ObjectSequences.native_existence",
                    "PPAC.Migration.Internal.ObjectSequences.native_natural",
                    "PPAC.Migration.Internal.ObjectSequences.native_naturalAppend",
                    "PPAC.Migration.Internal.ObjectSequences.native_prefix",
                    "PPAC.Migration.Internal.ObjectSequences.native_prefixUnique",
                    "PPAC.Migration.Internal.ObjectCheckedSequences.native_replay",
                    "PPAC.Migration.Internal.ObjectCheckedSequences.native_append",
                    "PPAC.Migration.Internal.ObjectCheckedSequences.native_prefix",
                    "PPAC.Migration.Internal.OmegaOrdinals.native_proof",
                    "PPAC.Migration.Internal.NaturalRecursion.native_total",
                    "PPAC.Migration.Internal.NaturalRecursion.native_deterministic",
                    "PPAC.Migration.Internal.NaturalRecursion.native_existence",
                    "PPAC.Migration.Internal.NaturalRecursion.native_uniqueness",
                    "PPAC.Migration.Internal.ObjectNaturalRecursion.native_proof",
                    "PPAC.Migration.Internal.SuccessorRecursion.native_proof",
                    "PPAC.Migration.Internal.SuccessorRecursion.native_zero",
                    "PPAC.Migration.Internal.ObjectNaturalAddition.native_fiber",
                    "PPAC.Migration.Internal.ObjectNaturalAddition.native_closure",
                    "PPAC.Migration.Internal.ObjectNaturalAddition.native_zero",
                    "PPAC.Migration.Internal.ObjectNaturalAddition.native_successor",
                    "PPAC.Migration.Internal.ObjectNaturalAddition.native_leftZero",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplication.native_fiber",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplication.native_closure",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplication.native_zero",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplication.native_successor",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplication.native_leftZero"} or name.startswith((
            "PPAC.Migration.ZFEquivalence.", "PPAC.Migration.SeparationSyntax.", "PPAC.Migration.CollectionSyntax.", "PPAC.Migration.ZFReplay.", "PPAC.Migration.ReverseZFReplay.")):
            if not set(dependencies) <= allowed | {"Classical.choice"} | inherited:
                raise RuntimeError(f"Unexpected fixed-ZF axiom dependency: {name}: {dependencies}")
            continue
        if is_step2 or is_step3_logic:
            if not set(dependencies) <= allowed | {"Classical.choice"}:
                raise RuntimeError(f"Unexpected syntax/transport axiom dependency: {name}: {dependencies}")
            continue
        if extra != expected_extra:
            raise RuntimeError(f"Unexpected axiom dependency: {name}: {dependencies}")
    arithmetic_core = {
        f"PPAC.Migration.Internal.{namespace}.{name}_kernel_certificate"
        for namespace in ("ObjectNaturalAddition", "ObjectNaturalMultiplication")
        for name in ("fiber", "closure", "zero", "successor", "leftZero")
    }
    for name in sorted(arithmetic_core):
        if set(footprints.get(name, [])) != {"propext", "Classical.choice", "Quot.sound"}:
            raise RuntimeError(f"Unexpected arithmetic core certificate footprint: {name}")
    hashed = sources + sorted(ROOT.glob("third_party/openai/*.txt")) + [ROOT / x for x in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "scripts/verify.py", "scripts/check_source_rules.py", "scripts/check_source_theory.py", "docs/SOURCE_THEORY_LOCK.json", "docs/SOURCE_RULES_LOCK.json", "docs/TRUST_BASELINE.json", "docs/CHOICE_TRUST_BASELINE.json"]]
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
        "all_native_Project_Separation_instances_reverse_transported": True,
        "all_source_Collection_instances_proved_in_native_ZF": True,
        "arbitrary_native_Collection_presentation_object_equivalent": True,
        "all_source_Replacement_instances_proved_in_native_ZF": True,
        "full_source_ZF_derivations_replayed_in_original_native_ZF": True,
        "full_source_target_derivations_replayed_in_original_native_target": True,
        "full_bounded_membership_minimal_schema_proved_in_source_and_native_ZF": True,
        "full_bounded_membership_induction_schema_proved_in_source_and_native_ZF": True,
        "bounded_minimal_and_induction_use_only_Foundation_and_one_Separation_instance": True,
        "pure_object_Kuratowski_pair_existence_uniqueness_proved_in_source_and_native_ZF": True,
        "pure_object_Kuratowski_pair_components_characterized_proved": True,
        "Kuratowski_encoding_strictly_matches_original_source_PP_AC": True,
        "Kuratowski_pair_certificates_use_only_Pairing_and_Extensionality": True,
        "original_source_edge_and_full_functionOn_strictly_preserved": True,
        "pure_object_singleton_function_graph_constructed_in_source_and_native_ZF": True,
        "arbitrary_function_graph_edge_domain_and_single_valuedness_proved": True,
        "object_set_insert_and_original_successor_proved": True,
        "object_function_graph_extension_proved": True,
        "object_function_graph_extension_requires_fresh_input": True,
        "object_graph_extension_preserves_full_functionOn_and_exact_edges": True,
        "object_graph_extension_witness_uniqueness_proved": True,
        "object_graph_domain_constructed_using_Union_and_one_Separation_instance": True,
        "object_general_compatible_graph_union_proved": True,
        "object_graph_union_quantifies_arbitrary_internal_families_including_empty": True,
        "object_graph_union_domain_uniqueness_and_exact_edge_law_proved": True,
        "object_graph_restriction_proved": True,
        "object_graph_restriction_requires_subset_domain": True,
        "object_graph_restriction_exact_edges_and_uniqueness_proved": True,
        "object_graph_restriction_identity_and_composition_proved": True,
        "object_graph_restriction_uses_one_Separation_instance_and_Extensionality": True,
        "object_least_inductive_set_omega_exists_uniquely": True,
        "object_omega_membership_characterization_proved": True,
        "object_omega_induction_schema_proved": True,
        "object_omega_induction_has_arbitrary_parameters_and_formulas": True,
        "object_all_sets_irreflexive_using_Foundation_and_Pairing": True,
        "object_omega_zero_successor_decomposition_proved": True,
        "object_omega_and_all_its_elements_transitive_proved": True,
        "object_omega_successor_closed_and_injective_proved": True,
        "object_omega_fresh_successor_exists_proved": True,
        "object_full_graph_extensionality_from_equal_edges_proved": True,
        "object_compatible_graph_domain_inclusion_implies_graph_inclusion": True,
        "object_same_domain_compatible_graphs_equal_proved": True,
        "object_full_function_graph_has_exact_unique_domain_proved": True,
        "object_given_union_iteration_tracks_agree_on_all_common_internal_omega_inputs": True,
        "object_given_transitive_domain_union_iteration_tracks_compatible": True,
        "object_given_same_domain_union_iteration_tracks_unique": True,
        "object_omega_iteration_existence_proved": True,
        "object_omega_iteration_proved": True,
        "object_omega_iteration_quantifies_all_internal_lengths": True,
        "object_finite_iteration_successor_domain_and_graph_unique": True,
        "object_omega_iteration_collection_and_global_union_proved": False,
        "object_internal_omega_terminal_values_total_and_unique": True,
        "object_internal_omega_terminal_values_exact_range_constructed_by_Replacement": True,
        "object_terminal_range_contains_seed_and_closed_under_union": True,
        "object_each_set_has_transitive_cover_proved_in_source_Replacement_ZF": True,
        "object_each_set_has_transitive_cover_proved_in_original_native_ZF": True,
        "object_transitive_closure_proved": False,
        "object_rank_hierarchy_proved": False,
        "unbounded_object_set_induction_proved": True,
        "unbounded_object_set_induction_has_arbitrary_parameters_and_formulas": True,
        "global_object_membership_minimal_schema_proved": True,
        "global_object_membership_minimal_schema_has_arbitrary_parameters_and_formulas": True,
        "original_source_ordinal_and_internal_subset_well_founded_AST_strictly_preserved": True,
        "object_foundation_internal_membership_well_founded_condition_proved": True,
        "object_original_ordinals_member_closed_and_irreflexive": True,
        "object_original_ordinal_empty_and_successor_constructed": True,
        "object_arbitrary_ordinals_comparable_proved": True,
        "object_transitive_ordinal_subsets_are_members_or_equal_proved": True,
        "object_ordinal_comparison_three_branches_pairwise_exclusive": True,
        "object_ordinal_subset_iff_equal_or_member_proved": True,
        "object_ordinal_comparison_uses_only_Extensionality_Foundation_one_Separation": True,
        "object_arbitrary_internal_ordinal_family_union_proved": True,
        "object_ordinal_family_union_exists_is_unique_and_least_among_all_internal_set_bounds": True,
        "object_arbitrary_internal_ordinal_family_strict_bound_constructed": True,
        "object_ordinal_union_four_axioms_strict_bound_adds_only_Pairing": True,
        "object_arbitrary_formula_recursion_history_and_full_graph_syntax_defined": True,
        "object_recursion_transitive_initial_restriction_schema_proved": True,
        "object_given_ordinal_recursors_compatible_and_unique_schema_proved": True,
        "object_recursion_uses_only_Extensionality_Foundation_two_Separation_instances": True,
        "object_valid_ordinal_history_operator_totality_defined": True,
        "object_actual_ordinal_recursion_successor_extension_schema_proved": True,
        "object_actual_unique_successor_recursion_graph_fibers_proved": True,
        "object_successor_recursion_fiber_matches_original_Replacement_matrix": True,
        "object_all_internal_predecessor_recursion_graphs_collected_and_merged": True,
        "object_all_internal_ordinals_actual_recursion_existence_schema_proved": True,
        "object_all_internal_ordinals_actual_recursion_uniqueness_schema_proved": True,
        "object_transfinite_recursion_uses_source_Replacement_not_Collection": True,
        "object_identity_recursion_instance_totality_and_determinism_discharged": True,
        "object_original_PowerSet_actual_unique_values_proved": True,
        "object_actual_historical_power_set_image_constructed_by_Replacement": True,
        "object_power_union_operator_totality_and_determinism_discharged": True,
        "object_cumulative_hierarchy_recursion_graphs_exist_uniquely": True,
        "object_actual_recursive_hierarchy_layer_values_exist_uniquely": True,
        "object_recursive_hierarchy_zero_layer_is_empty": True,
        "object_hierarchy_early_history_edges_iff_actual_layers_proved": True,
        "object_power_union_exact_membership_equivalence_proved": True,
        "object_all_internal_hierarchy_layer_membership_recursion_proved": True,
        "object_hierarchy_subset_index_monotonicity_proved": True,
        "object_earlier_hierarchy_layers_are_actual_members_proved": True,
        "object_hierarchy_layers_are_transitive_proved": True,
        "object_hierarchy_successor_is_actual_PowerOf_proved": True,
        "object_hierarchy_limit_union_equation_proved": True,
        "object_actual_exact_family_of_all_earlier_hierarchy_layers_constructed": True,
        "object_hierarchy_limit_is_original_UnionOf_actual_layer_family": True,
        "object_hierarchy_zero_included_in_internal_limit_condition_proved": True,
        "object_all_parameter_formulas_definable_ordinals_actual_unique_least_schema_proved": True,
        "object_hierarchy_successor_and_limit_equations_proved": True,
        "object_hierarchy_monotonicity_transitivity_and_rank_cover_proved": True,
        "object_all_internal_sets_have_actual_hierarchy_subset_cover": True,
        "object_all_internal_sets_have_actual_hierarchy_member_cover": True,
        "object_actual_unique_rank_as_least_containing_layer_index_proved": True,
        "object_internal_member_ranks_collected_by_source_Replacement": True,
        "object_rank_cover_via_object_unbounded_set_induction_proved": True,
        "object_rank_cover_source_has_no_Collection_or_Choice_input": True,
        "native_Collection_proved_in_source_Replacement_ZF": True,
        "full_ZF_equivalence_proved": True,
        "object_full_Collection_for_arbitrary_relations_and_parameters_proved_from_Replacement": True,
        "object_minimal_witness_ranks_collected_without_choosing_relation_witnesses": True,
        "all_native_Project_Collection_matrices_proved_in_source_ZF_image": True,
        "all_open_native_ZF_and_target_derivations_replayed_to_source_theory_images": True,
        "native_ZF_and_target_closed_sentences_reverse_compile_to_original_19_rules": True,
        "reverse_native_to_source_derivation_compiler_proved": True,
        "reverse_native_kernel_constructors_covered": 6,
        "reverse_native_logical_modes_covered": 27,
        "reverse_compiler_requires_nonempty_external_variable_context": True,
        "source_closed_sentence_reverse_context_size": 1,
        "internal_reverse_compiler_representation_proved": False,
        "object_graph_choice_to_selector_choice_source_proved": True,
        "object_graph_choice_to_original_native_choice_kernel_proved": True,
        "object_function_graph_actual_precise_value_range_constructed": True,
        "object_graph_choice_forward_uses_one_Replacement_instance": True,
        "object_selector_choice_to_graph_choice_proved": True,
        "choice_presentations_equivalent_proved": True,
        "object_tagged_rows_and_exact_family_constructed": True,
        "object_tagged_family_nonempty_and_disjoint_proved": True,
        "object_selected_pair_exact_image_full_choice_graph_constructed": True,
        "object_choice_reverse_finite_background_axioms": 5,
        "object_choice_reverse_Replacement_instances": 3,
        "object_choice_reverse_allows_selector_junk": True,
        "source_rule_count": 19,
        "source_rules_match_pinned_excerpt": True,
        "object_internal_finite_sequence_full_function_graphs_proved": True,
        "object_actual_sequences_exist_at_every_internal_omega_length": True,
        "object_finite_sequence_actual_unique_append_and_exact_prefix_proved": True,
        "object_arbitrary_parameter_row_formula_append_and_prefix_schemas_proved": True,
        "object_finite_sequence_six_sentence_background_certificate_proved": True,
        "step4_prerequisite_check_passed": True,
        "object_all_internal_omega_members_are_original_ordinals_proved": True,
        "object_natural_predecessor_recursion_operator_total_and_deterministic_proved": True,
        "object_natural_recursion_actual_unique_recursor_graphs_proved": True,
        "object_natural_recursion_actual_unique_values_at_all_internal_naturals_proved": True,
        "object_natural_recursion_preserves_all_parameters": True,
        "object_natural_recursion_operator_zero_and_successor_equations_proved": True,
        "object_successor_iteration_actual_unique_values_and_zero_equation_proved": True,
        "object_natural_addition_actual_unique_omega_values_proved": True,
        "object_natural_addition_zero_and_bidirectional_successor_laws_proved": True,
        "object_natural_addition_left_zero_by_object_omega_induction_proved": True,
        "object_natural_multiplication_actual_unique_omega_values_proved": True,
        "object_natural_multiplication_zero_and_bidirectional_successor_laws_proved": True,
        "object_natural_multiplication_left_zero_by_object_omega_induction_proved": True,
        "arithmetic_closed_kernel_certificates_checked": 10,
        "object_natural_semiring_algebra_and_coding_bounds_proved": False,
        "object_full_natural_addition_and_multiplication_proved": False,
        "object_internal_godel_structural_code_correctness_proved": False,
        "dedicated_ZF_U_proof_checker_AST_implemented": False,
        "proof_checker_correctness_on_arbitrary_internal_codes_proved": False,
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
        "additional_active_inherited_choice_bridge_certificate_axioms": sorted(inherited_choice),
        "native_choice_bridge_trust_scope": choice_baseline["scope"],
        "native_ZF_seven_certificate_baseline_unchanged": True,
        "standard_axiom_only": False,
        "new_custom_axioms": [],
        "warning_lines": sum("warning:" in line for item in COMMANDS for line in (OUT / item["log"]).read_text(encoding="utf-8").splitlines()),
        "scope": "Steps 1-2 and step 3a: full reverse syntax, original-kernel normalization and presentation replay; all seven fixed ZF axioms in both directions and full bidirectional Separation, all source Replacement instances proved using Collection plus Separation, and full source ZF/target forward replay. All six native kernel constructors and 27 logical modes reverse-compile into the original 19 source rules, with arbitrary finite local contexts and a nonempty external variable context. Full bounded membership-minimal and induction schemas are proved in source ZF and the original native kernel using only Foundation and one Separation instance. Full pure-object Kuratowski pair existence, uniqueness and component characterization use only Pairing and Extensionality and strictly match the original source PP/AC encoding. Original source edge and full functionOn are strictly preserved; singleton function graphs are constructed and evaluated internally, and arbitrary function graphs have exact edge-input domains and single-valuedness. Set insertion and original source successor are constructed. Arbitrary function graphs extend at any fresh input outside the old domain, preserving full functionOn and an exact all-edge law, with actual object existence and three-axiom certificates. Arbitrary object graph restrictions are constructed by one Separation instance and Extensionality; full functionOn, exact edge law, uniqueness, identity and nested-restriction composition are proved in source ZF and the original native kernel. Arbitrary graph domains are constructed inside the double union by Union and one Separation instance. Arbitrary internal compatible graph families, including empty families, have actual unique union graphs and domains with full functionOn and an exact all-edge law. The actual internal least inductive set omega exists uniquely; its membership and full parameterized formula-induction schema have original-kernel proofs using Infinity, Extensionality and Separation. All internal omega elements split into zero or an internal successor; omega and each of its elements are transitive. Zero and successor membership, nonzero predecessors, successor injectivity and fresh successor existence have actual original-kernel certificates. Foundation and Pairing prove non-self-membership for every internal set. Full graph extensionality from equal edges, compatible function graph inclusion from domain inclusion, same-domain graph equality, and exact unique function domains are proved using only Extensionality. Given actual union-recursive object tracks with a common empty-set seed and transitive domains, full object omega induction proves agreement on all common internal inputs; when one domain is contained in omega the tracks are compatible, and same-domain tracks are equal. Actual finite tracks now exist at every internal omega length, with successor domains and unique domains/graphs. Base singletons and all four old/new successor-edge cases are proved internally using Pairing, Union, Extensionality, Foundation and four Separation instances; no Replacement, Collection or object AC is an input. Every internal length now has a unique terminal value witnessed by an actual finite track. One original full Replacement instance constructs their exact internal omega range; it contains the seed and is closed under taking unions. Its actual union yields the closed object theorem that every set has a transitive cover, in source Replacement ZF and original native ZF. The source proof does not use Collection. Full unbounded set-induction and global membership-minimal schemas now have actual source ZF and native-kernel derivations for every formula and arbitrary parameter count, obtained from transitive covers and bounded induction, without external well-foundedness. The original source ordinal, strict membership linearity and full internal-subset minimal-element formulas are strictly preserved. Foundation proves the internal well-founded condition; original ordinals are member-closed and non-self-membered, and actual empty/successor ordinals are constructed using only Foundation, EmptySet, Pairing and Union. Transitive ordinal subsets are now proved equal or members, and arbitrary internal ordinal pairs have actual pairwise-exclusive trichotomy and subset characterization. These proofs use only Extensionality, Foundation and one Separation instance, with full source ZF and original-kernel replay. Arbitrary internal ordinal-family unions now actually exist as original ordinals and are unique least inclusion upper bounds among all internal sets; successor construction provides actual strict ordinal bounds for every such family, including empty families. The union proof uses Extensionality, Foundation, Union and one Separation instance; strict bounds add Pairing. Arbitrary parameter formulas now define recursion using full original function graphs and actual restriction-history witnesses; transitive initial restrictions are actually constructed, and given recursors on arbitrary internal ordinal domains are proved compatible and same-domain unique. Every matrix instance has full source ZF and original-kernel proofs using Extensionality, Foundation and two Separation instances. Operator totality on valid ordinal/history inputs now produces an actual next value; actual successor domains and full recursor graph extensions preserve the old graph as the precise old-domain restriction and satisfy every old/new equation. Unique actual successor graph fibers match the original Replacement matrix interface. Their finite theory uses Extensionality, Foundation, Pairing, Union and one Separation instance, without Replacement or Collection input. Original full Replacement now actually collects the unique successor recursor graphs of all internal predecessors. Their precise image and coverage, pairwise compatibility, complete function graph on the exact target ordinal domain, and every actual history equation are proved. Object set induction yields actual existence and uniqueness on every internal original ordinal for arbitrary parameter matrices whose valid-input totality and single-valuedness are object premises. A concrete identity-output matrix discharges both premises. All schemas have source Replacement ZF and original native-kernel proofs, with no Collection or object AC input. Original PowerSet and one explicit full source Replacement instance now construct the exact power-set image of all historical values and its actual union. This concrete recursion operator has proved object totality and determinism, both discharged to produce actual unique recursion graphs and actual unique layer values at every internal original ordinal. The empty-index layer is proved empty. Source Replacement ZF and original native-kernel certificates exist without object Choice or Collection input. Early graph outputs are now equivalent to actual layer values at every internal earlier index. Exact power-union membership yields the full layer membership recursion formula, subset-index layer monotonicity, earlier-layer membership, layer transitivity and the actual successor PowerOf equation. All seven new closed sentences have source Replacement ZF and original native-kernel certificates. The internal zero-or-limit condition now yields the exact early-layer union membership equation. One explicit original Replacement instance constructs the actual precise family of all earlier layer values, and the zero/limit layer is proved to be its original UnionOf. Every arbitrary-parameter formula defining a nonempty ordinal property now has an actual unique least ordinal, via object membership minimality and arbitrary ordinal comparison. The schemas have full source Replacement ZF and original native-kernel certificates. Every internal set now has an actual containing hierarchy layer, an actual unique least containing-layer rank, and actual membership in some layer. One explicit original Replacement instance collects all member ranks into their precise ordinal image; an actual strict ordinal bound and an actual layer value give the object set-induction progressive step. Actual successor layers lift subset coverage to member coverage. All six new closed sentences have source Replacement ZF and original native-kernel proofs; the source proof uses no Collection or object Choice input. Full Collection is now proved in source Replacement ZF for every arbitrary-parameter relation, without functional or unique witness assumptions. A unique least witness-rank matrix is collected by original Replacement; a real strict ordinal bound and actual layer provide true original-relation witnesses. All native Project Collection matrices have original-kernel proofs in the source ZF image. Every native ZF axiom now replays into that image; all open ZF and target-theory derivations replay in both directions, and closed native sentences return to the original 19 source rules at source variable context size 1. This is full external derivation presentation equivalence; internal proof-code correctness and Con remain pending. Original graph Choice now implies the original disjoint-family choice-set sentence in the object kernel. One explicit Replacement instance constructs the exact graph-output range; full graph and intersection proofs give a unique selected point per internal family member. The source forward proof and finite-theory kernel certificates retain the standard-only dependency audit. The isolated original Axioms.choice bridge additionally references its existing FreeClosed native_decide certificate, recorded separately from the unchanged seven-certificate ZF baseline. The converse is now proved: Pairing, Extensionality and three explicit original Replacement instances construct actual tagged rows, their exact nonempty disjoint family, and the precise selected-pair image. This image excludes selector junk and satisfies the full original functionOn and choiceOn on every internal input. The original nativeZF kernel proves both implications and the actual biconditional between graph AC and original Axioms.choice, with the same isolated original-choice certificate baseline. Internal finite-sequence prerequisites are now proved: full original function graphs with bounded values, actual unique append with exact old-domain restriction, actual precise prefixes, and actual sequences at every internal omega length by object induction. Arbitrary-parameter row formulas have original-kernel append and prefix preservation schemas. Eight full closed sentences have a six-sentence finite background, source ZF and nativeZF certificates. Every internal omega member now satisfies the original full ordinal definition by object omega induction. For every arbitrary-parameter total single-valued step relation on all internal sets, a concrete natural-predecessor operator has proved totality and determinism on every valid history, without assuming that history follows the recurrence. The original transfinite recursion theorem yields actual unique recursor graphs; every internal natural index has an actual unique value witnessed by a true successor domain and complete original recursor graph. Zero and successor operator laws are proved. The original set successor relation actually discharges totality and functionality, giving unconditional unique successor iteration and its zero equation. Actual natural addition and multiplication now have unique omega-valued outputs at every internal natural index, zero equations and bidirectional successor laws. Left zero identities are proved by object omega induction. Multiplication existentially quantifies its actual internal empty initial value and aligns different zero witnesses by original-kernel equality. Ten full closed sentences have source Replacement ZF and nativeZF proofs; intermediate recursion certificates are discharged using previously proved closed theorems. Semiring algebra, order and coding bounds, internal Godel/tree-code correctness, the dedicated pure ZF/U checker AST, correctness on arbitrary internal proof codes, a global omega function graph, least transitive closure and the final internal Con theorem remain pending.",
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

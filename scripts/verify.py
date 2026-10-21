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
            ["Normalization.", "Reverse.", "Presentation.", "FormulaEquivalence.", "ProjectSyntax.", "ProjectNormalization.", "ProjectDecode.", "SeparationReverse.", "SourceAlgebra.", "SourceLogic.", "SourcePropositional.", "SourceQuantifiers.", "ReverseSubstitution.", "ReverseLogicalAxioms.", "ReverseCompile.", "MinimalPredicates.", "MinimalLogic.", "MinimalInstances.", "BoundedMinimal.", "BoundedInduction.", "PairSyntax.", "UnorderedPairLogic.", "OrderedPairExistence.", "OrderedPairElimination.", "OrderedPairWitnesses.", "OrderedPairLogic.", "ObjectPairs.", "GraphSyntax.", "GraphLogic.", "GraphProperties.", "SingletonGraphLogic.", "SingletonMap.", "ObjectGraphs.", "InsertSyntax.", "InsertLogic.", "InsertExistence.", "GraphInsertEdges.", "GraphInsertEntries.", "GraphInsertValues.", "GraphInsertFunction.", "GraphInsertSyntax.", "GraphInsertExistence.", "ObjectGraphInsert.", "RestrictionSyntax.", "RestrictionEdges.", "RestrictionFunction.", "RestrictionAlgebra.", "RestrictionExistence.", "ObjectRestriction.", "GraphDomainSyntax.", "GraphDomainBound.", "GraphDomainExistence.", "GraphDomainAlgebra.", "GraphFamilySyntax.", "GraphFamilyEdges.", "GraphFamilyValues.", "GraphFamilyEntries.", "GraphFamilyFunction.", "GraphFamilyExistence.", "GraphFamilyEmpty.", "ObjectGraphFamily.", "OmegaSyntax.", "OmegaUniversal.", "OmegaCut.", "OmegaExistence.", "OmegaAlgebra.", "OmegaInductionSyntax.", "OmegaInductionCut.", "OmegaInduction.", "ObjectOmega.", "OmegaStructureSyntax.", "ObjectIrreflexivity.", "OmegaElementary.", "OmegaStructureInduction.", "OmegaStructureAlgebra.", "ObjectOmegaStructure.", "GraphPointwiseSyntax.", "GraphPointwiseEntries.", "GraphPointwise.", "GraphPointwiseDomain.", "ObjectGraphPointwise.", "IterationSyntax.", "IterationValues.", "IterationStep.", "IterationInduction.", "IterationCompatibility.", "ObjectIterationUniqueness.", "FiniteIterationSyntax.", "IterationBase.", "IterationBaseExistence.", "IterationExtensionAlgebra.", "IterationExtension.", "IterationExtensionExistence.", "IterationExistence.", "FiniteIterationUniqueness.", "ObjectFiniteIteration.", "IterationContext.", "IterationValueSyntax.", "IterationValueExistence.", "IterationValueUniqueness.", "IterationValueCollection.", "IterationValueStep.", "IterationRangeSyntax.", "IterationRangeSeed.", "IterationRangeClosed.", "TransitiveCoverSyntax.", "TransitiveCoverLogic.", "TransitiveCoverExistence.", "ObjectTransitiveCover.", "ReplacementPredicates.", "ExactImage.", "ReplacementInstances.", "ReplacementFromCollection."])
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
                    "PPAC.Migration.ObjectTransitiveCover.native_cover"} or name.startswith((
            "PPAC.Migration.ZFEquivalence.", "PPAC.Migration.SeparationSyntax.", "PPAC.Migration.CollectionSyntax.", "PPAC.Migration.ZFReplay.")):
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
        "unbounded_object_set_induction_proved": False,
        "native_Collection_proved_in_source_Replacement_ZF": False,
        "full_ZF_equivalence_proved": False,
        "reverse_native_to_source_derivation_compiler_proved": True,
        "reverse_native_kernel_constructors_covered": 6,
        "reverse_native_logical_modes_covered": 27,
        "reverse_compiler_requires_nonempty_external_variable_context": True,
        "source_closed_sentence_reverse_context_size": 1,
        "internal_reverse_compiler_representation_proved": False,
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
        "scope": "Steps 1-2 and step 3a: full reverse syntax, original-kernel normalization and presentation replay; all seven fixed ZF axioms in both directions and full bidirectional Separation, all source Replacement instances proved using Collection plus Separation, and full source ZF/target forward replay. All six native kernel constructors and 27 logical modes reverse-compile into the original 19 source rules, with arbitrary finite local contexts and a nonempty external variable context. Full bounded membership-minimal and induction schemas are proved in source ZF and the original native kernel using only Foundation and one Separation instance. Full pure-object Kuratowski pair existence, uniqueness and component characterization use only Pairing and Extensionality and strictly match the original source PP/AC encoding. Original source edge and full functionOn are strictly preserved; singleton function graphs are constructed and evaluated internally, and arbitrary function graphs have exact edge-input domains and single-valuedness. Set insertion and original source successor are constructed. Arbitrary function graphs extend at any fresh input outside the old domain, preserving full functionOn and an exact all-edge law, with actual object existence and three-axiom certificates. Arbitrary object graph restrictions are constructed by one Separation instance and Extensionality; full functionOn, exact edge law, uniqueness, identity and nested-restriction composition are proved in source ZF and the original native kernel. Arbitrary graph domains are constructed inside the double union by Union and one Separation instance. Arbitrary internal compatible graph families, including empty families, have actual unique union graphs and domains with full functionOn and an exact all-edge law. The actual internal least inductive set omega exists uniquely; its membership and full parameterized formula-induction schema have original-kernel proofs using Infinity, Extensionality and Separation. All internal omega elements split into zero or an internal successor; omega and each of its elements are transitive. Zero and successor membership, nonzero predecessors, successor injectivity and fresh successor existence have actual original-kernel certificates. Foundation and Pairing prove non-self-membership for every internal set. Full graph extensionality from equal edges, compatible function graph inclusion from domain inclusion, same-domain graph equality, and exact unique function domains are proved using only Extensionality. Given actual union-recursive object tracks with a common empty-set seed and transitive domains, full object omega induction proves agreement on all common internal inputs; when one domain is contained in omega the tracks are compatible, and same-domain tracks are equal. Actual finite tracks now exist at every internal omega length, with successor domains and unique domains/graphs. Base singletons and all four old/new successor-edge cases are proved internally using Pairing, Union, Extensionality, Foundation and four Separation instances; no Replacement, Collection or object AC is an input. Every internal length now has a unique terminal value witnessed by an actual finite track. One original full Replacement instance constructs their exact internal omega range; it contains the seed and is closed under taking unions. Its actual union yields the closed object theorem that every set has a transitive cover, in source Replacement ZF and original native ZF. The source proof does not use Collection. A global omega function graph, least transitive closure, ordinals/ranks, reverse Collection/AC equivalences and internal Con/compiler representation remain pending.",
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

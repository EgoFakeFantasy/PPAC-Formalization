"""Rebuild and check the explicitly enumerated Lean declaration audit."""
from __future__ import annotations

import os
import sys
import hashlib
import json
import re
import subprocess
from pathlib import Path
from source_hash import POLICY, source_sha256

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


def check_mode_three_scope() -> dict:
    """Audit pinned finite call sites; this does not prove internal checker applicability."""
    inventory = json.loads((ROOT / "docs/MODE3_CHECKER_SCOPE.json").read_text(encoding="utf-8"))
    base = ROOT / ".lake/packages/YesMetaZFC"
    text = {}
    for name, expected_hash in inventory["files"].items():
        path = base / name
        if source_sha256(path) != expected_hash:
            raise RuntimeError(f"Mode3 source inventory changed: {name}")
        text[Path(name).name] = strip_comments(path.read_text(encoding="utf-8-sig"))
    node = text["ObjectProofNode.lean"]
    logical = text["ObjectLogicalAxiom.lean"]
    for body, expected in [(node, inventory["proof_shape_count"]), (logical, inventory["logical_shape_count"])]:
        match = re.search(r"def shapes : List Shape :=\s*\[([^\]]*)\]", body)
        if not match or len(match.group(1).split(",")) != expected:
            raise RuntimeError("Mode3 shape inventory mismatch")
    modes = lambda body: [int(x) for x in re.findall(r"\btransform\s+([0-3])\b", body)]
    if modes(node) != [1, 0, 3] or modes(logical) != [2, 1, 1, 2, 1, 2, 2]:
        raise RuntimeError("Unexpected transform call sites")
    subst = re.search(r"(?ms)^abbrev substitutionShape : Shape where.*?(?=^def shapes)", node).group(0)
    tight = re.sub(r"\s+", "", subst)
    for clause in ["arity:=6", "formula(.var2)(.var5)", "(.syntax,node1[.literal0,.var0,.var2,.var3])", "transform3(.var3)(.var5)(.var1)"]:
        if clause not in tight:
            raise RuntimeError(f"Missing actual substitution guard: {clause}")
    if "inductive FunctionSymbol where" not in text["Language.lean"] or "| emptySet" not in text["Language.lean"]:
        raise RuntimeError("Shared extended signature inventory mismatch")
    if "SyntaxDecode.functionSymbols.toList.map applicationRule" not in text["ObjectTermSyntax.lean"]:
        raise RuntimeError("Shared term checker signature changed")
    if inventory["full_internal_pure_syntax_checker_bridge_proved"] is not False:
        raise RuntimeError("Source inventory must remain separate from internal checker proof")
    return inventory


def check_pure_syntax_definition() -> dict:
    """Keep the actual pure Horn acceptance relation independent of its typing theorem."""
    body = strip_comments((ROOT / "PPAC/Migration/Internal/PureSyntaxTrace.lean").read_text(encoding="utf-8"))
    names = ["termRow", "argumentRow", "formulaRow", "closed", "witness", "condition", "term", "arguments", "formula"]
    forbidden = re.compile(r"SyntaxTermSyntax\.|SyntaxMixedImageCodeSyntax\.|FormulaCodeSyntax\.|SyntaxRenameJudgmentSyntax\.|HornLookupConditionSyntax\.|SyntaxTransform\.|Expr\.eval")
    for name in names:
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
        if not found or forbidden.search(found.group(0)):
            raise RuntimeError(f"Pure checker definition uses a typing/transform oracle: {name}")
    rules = strip_comments((ROOT / "PPAC/Migration/Internal/PureSyntaxRules.lean").read_text(encoding="utf-8"))
    if "ObjectTermSyntax.applicationRule" in rules or "relationSymbols" in rules or "functionSymbols" in rules:
        raise RuntimeError("Extended signature leaked into pure syntax rules")
    if "ObjectFormulaSyntax.relationRule .membership" not in rules:
        raise RuntimeError("Missing actual membership rule")
    return {"definitions": names, "independent_of_typing_oracles": True, "rules": 15,
            "term_query_scope": "all internal bound/free/input candidates under Omega",
            "argument_query_correctness_proved": True, "formula_query_correctness_proved": True, "formula_query_scope": "all internal root/bound/free candidates under Omega, object IH discharged"}


def check_pure_proof_query_definitions() -> dict:
    """Keep actual expression query acceptance separate from its typing/program specification."""
    declarations = {"PureSyntaxExprQuery": ["query", "rowQuery"],
                    "OriginalTransformExprQuery": ["query", "rowQuery"],
                    "PureProofSubstitutionTransform": ["bundle"]}
    forbidden = re.compile(r"FormulaCodeSyntax\.|SyntaxTermSyntax\.|SyntaxMixedImageCodeSyntax\.|FreeSubstProgramSyntax\.|OriginalTransformRowSyntax\.|Expr\.eval|specification")
    for module, names in declarations.items():
        body = strip_comments((ROOT / "PPAC/Migration/Internal" / (module + ".lean")).read_text(encoding="utf-8"))
        for name in names:
            found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
            if not found or forbidden.search(found.group(0)):
                raise RuntimeError(f"Actual proof query uses a comparison oracle: {module}.{name}")
    body = strip_comments((ROOT / "PPAC/Migration/Internal/PureProofSubstitutionQueries.lean").read_text(encoding="utf-8"))
    for name, index in [("substitutionFormula", 0), ("substitutionArguments", 1), ("substitutionTransform", 4)]:
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
        if not found or f"(ObjectProofNode.substitutionShape.queries[{index}]).2" not in found.group(0):
            raise RuntimeError(f"Original substitution query index changed: {name}")
    return {"acceptance_definitions": declarations, "independent_of_comparison_oracles": True,
            "actual_substitution_query_indices": [0, 1, 4], "projection_queries_proved": False,
            "full_proof_node_correctness_proved": False}


def check_raw_projection_definitions() -> dict:
    """Keep raw projection independent of the canonical-list or host checker specifications."""
    declarations = {"PairingProjectionSyntax": ["encoded", "body", "selected", "hasSelected", "step"],
                    "RawCodeProjectionSyntax": ["body", "step", "iteration"],
                    "RawCodeGetSyntax": ["get"]}
    forbidden = re.compile(r"StructuralList|ObjectCodeProjection\.|ObjectProjection\.|Expr\.eval|FormulaCodeSyntax\.|SyntaxTermSyntax\.|Classical\.choose")
    for module, names in declarations.items():
        body = strip_comments((ROOT / "PPAC/Migration/Internal" / (module + ".lean")).read_text(encoding="utf-8"))
        for name in names:
            found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
            if not found or forbidden.search(found.group(0)):
                raise RuntimeError(f"Raw projection uses a canonical-list/host oracle: {module}.{name}")
    body = strip_comments((ROOT / "PPAC/Migration/Internal/PairingProjectionSyntax.lean").read_text(encoding="utf-8"))
    if "StructuralNodeSyntax.raw w a b x" not in body or "GodelPairSyntax.code w a b x" not in body:
        raise RuntimeError("Raw projection lost the original two pairing cases")
    return {"definitions": declarations, "independent_of_canonical_list_and_host_oracles": True,
            "arbitrary_raw_tag_head_tail_iff_proved": True, "all_internal_get_values_unique_proved": True,
            "get_zero_successor_index_equations_proved": True, "get_zero_input_all_internal_indices_proved": True,
            "original_projection_full_seven_rule_trace_bridge_proved": True}


def check_raw_field_definitions() -> dict:
    """The original payload/get field relation must not call canonical-field or checker oracles."""
    body = strip_comments((ROOT / "PPAC/Migration/Internal/RawCodeFieldSyntax.lean").read_text(encoding="utf-8"))
    names = ["body", "field", "existsField", "fiber"]
    forbidden = re.compile(r"StructuralList(?:Projection|Field|Iteration|Shift)|ObjectCodeProjection\.|ObjectProjection\.|Expr\.eval|FormulaCodeSyntax\.|SyntaxTermSyntax\.|RawCodeGetZeroSyntax\.|Classical\.choose")
    for name in names:
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
        if not found or forbidden.search(found.group(0)):
            raise RuntimeError(f"Raw field acceptance uses a comparison oracle: {name}")
    if "PairingProjectionSyntax.step true false w x p" not in body or "RawCodeGetSyntax.get w p i y" not in body:
        raise RuntimeError("Original payload followed by get composition changed")
    return {"definitions": names, "independent_of_canonical_field_and_host_oracles": True,
            "input_zero_all_internal_indices_proved": True, "field_total_unique_on_internal_indices_proved": True,
            "finite_constructor_slot_scope": "external finite arity/slot schema with object quantified codes and values",
            "original_projection_full_seven_rule_trace_bridge_proved": True}


def check_projection_trace_definitions() -> dict:
    """Keep original seven-rule trace acceptance independent of numeric/typing conclusions."""
    names = {"ProjectionTraceSyntax": ["tagRow", "getRow", "fieldRow", "closed", "witness", "condition", "tag", "get", "field"],
             "ProjectionExprQuery": ["query", "rowQuery", "premises"],
             "ProjectionTraceSetSyntax": ["matrix", "one", "value", "existsValue"],
             "ProjectionTraceUnfold": ["unfolded", "existsUnfolded"]}
    forbidden = re.compile(r"PureSyntaxTrace\.|PureSyntaxRules\.|HornLookupConditionSyntax\.|ObjectCodeProjection\.|RawCode(?:Projection|Get|Field)\w*\.|StructuralList(?:Projection|Field)\w*\.|FormulaCodeSyntax\.|SyntaxTermSyntax\.|Expr\.eval|Classical\.choose")
    bodies = {}
    for mod, definitions in names.items():
        body = strip_comments((ROOT / ("PPAC/Migration/Internal/" + mod + ".lean")).read_text(encoding="utf-8"))
        bodies[mod] = body
        for name in definitions:
            found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
            if not found or forbidden.search(found.group(0)):
                raise RuntimeError(f"Original projection trace definition uses comparison oracle: {mod}.{name}")
    if "HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules" not in bodies["ProjectionTraceSyntax"]:
        raise RuntimeError("Original seven-rule list missing from projection closure")
    if "MinimalPredicates.separated matrix" not in bodies["ProjectionTraceSetSyntax"]:
        raise RuntimeError("Projection all-root set is not actual Separation")
    return {"definitions": names, "original_rule_count": 7, "independent_of_numeric_and_typing_oracles": True,
            "actual_bounded_rule_introduction_and_uniform_unfold_proved": True,
            "all_internal_numeric_projection_iff_proved": True,
            "proof_node_projection_queries_proved": False}


def check_projection_rule_partition() -> dict:
    """Match all three actual outer-tag sublists to the pinned original seven descriptors."""
    body = strip_comments((ROOT / "PPAC/Migration/Internal/ProjectionRuleDispatch.lean").read_text(encoding="utf-8"))
    groups = {"tagRules": ["tagZero", "tagPositive"], "getRules": ["getZero", "getHead", "getTail"],
              "fieldRules": ["fieldZero", "fieldPositive"]}
    for name, rules in groups.items():
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
        expected = "def" + name + ":ListRule:=[" + ",".join("ObjectProjection." + rule for rule in rules) + "]"
        if not found or re.sub(r"\s+", "", found.group(0)) != expected:
            raise RuntimeError(f"Original projection rule partition changed: {name}")
    return {"groups": groups, "all_original_rules_dispatched": True,
            "tag_numeric_all_internal_candidates_iff_proved": True,
            "query_input_index_output_natural_domains_proved": True,
            "get_and_field_numeric_all_internal_candidates_iff_proved": True}


def check_pure_substitution_node_definitions() -> dict:
    """Keep fixed original shape acceptance separate from its program/field specifications."""
    definitions = {"ProofSubstitutionProjectionSyntax": ["freeProjection", "formulaProjection", "freeFields", "formulaFields", "projections"],
                   "ProofSubstitutionAllQueries": ["bundle"],
                   "ProofSubstitutionNodeSyntax": ["queryMatrix", "boundedMatrix", "body", "node"]}
    forbidden = re.compile(r"RawCode(?:Field|Get)\w*\.|FreeSubstProgramSyntax\.|FormulaCodeSyntax\.|\bspecification\b|\bmetadata\b|Expr\.eval|Classical\.choose|ObjectLocalDecision\.(?:checked|Rule\.checked)")
    bodies = {}
    for mod, names in definitions.items():
        body = strip_comments((ROOT / ("PPAC/Migration/Internal/" + mod + ".lean")).read_text(encoding="utf-8"))
        bodies[mod] = body
        for name in names:
            found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
            if not found or forbidden.search(found.group(0)):
                raise RuntimeError(f"Pure substitution acceptance uses comparison oracle: {mod}.{name}")
    projection = bodies["ProofSubstitutionProjectionSyntax"]
    if "(ObjectProofNode.substitutionShape.queries[2]).2" not in projection or "(ObjectProofNode.substitutionShape.queries[3]).2" not in projection:
        raise RuntimeError("Exact original substitution projection queries changed")
    node = bodies["ProofSubstitutionNodeSyntax"]
    for clause in ["graph ObjectProofNode.substitutionShape.head w env row", "ProofSubstitutionAllQueries.bundle w env", "HornExprBounds.environmentBound 6 row env", "existsMany 6 (body w row)"]:
        if clause not in node:
            raise RuntimeError("Incomplete original pure substitution node: " + clause)
    return {"definitions": definitions, "original_arity": 6, "original_head_field_count": 5, "actual_query_count": 5,
            "all_internal_numeric_projection_bounds_proved": True, "all_six_assignment_bounds_discharged": True,
            "whole_fixed_shape_pure_relational_node_iff_proved": True,
            "shared_extended_condition_numeric_quotation_Bool_correspondence_proved": False}


def check_pure_mp_node_definitions() -> dict:
    """Inspect actual original six-query acceptance independently of its numeric specifications."""
    definitions = {"ProofMPSyntax": ["conclusionQuery", "antecedentQuery", "leftFreeQuery", "leftFormulaQuery", "rightFreeQuery", "rightImplicationQuery", "projections"],
                   "ProofMPAllQueries": ["formulaQueries", "bundle"],
                   "ProofMPNodeSyntax": ["queryMatrix", "boundedMatrix", "body", "node"]}
    forbidden = re.compile(r"RawCode(?:Field|Get)\w*\.|FormulaCodeSyntax\.|\bspecification\b|\bmetadata\b|\bimplicationRead\b|Expr\.eval|Classical\.choose|ObjectLocalDecision\.(?:checked|Rule\.checked)")
    bodies = {}
    for mod, names in definitions.items():
        body = strip_comments((ROOT / ("PPAC/Migration/Internal/" + mod + ".lean")).read_text(encoding="utf-8"))
        bodies[mod] = body
        for name in names:
            found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
            if not found or forbidden.search(found.group(0)):
                raise RuntimeError(f"Pure MP acceptance uses comparison oracle: {mod}.{name}")
    for i in range(6):
        if f"(ObjectProofNode.mpShape.queries[{i}]).2" not in bodies["ProofMPSyntax"]:
            raise RuntimeError(f"Exact original MP query changed: {i}")
    for clause in ["graph ObjectProofNode.mpShape.head w env row", "ProofMPAllQueries.bundle w env", "HornExprBounds.environmentBound 5 row env", "existsMany 5 (body w row)"]:
        if clause not in bodies["ProofMPNodeSyntax"]:
            raise RuntimeError("Incomplete original pure MP node: " + clause)
    return {"definitions": definitions, "original_arity": 5, "original_head_field_count": 4, "actual_query_count": 6,
            "composite_implication_output_witness_constructed_and_eliminated": True,
            "all_five_assignment_bounds_discharged": True,
            "whole_fixed_shape_pure_relational_node_iff_proved": True,
            "shared_extended_condition_numeric_quotation_Bool_correspondence_proved": False}


def check_pure_strengthening_node_definitions() -> dict:
    """Inspect actual original four-query acceptance independently of its numeric specifications."""
    definitions = {"ProofStrengtheningSyntax": ["formulaQuery", "freeQuery", "predecessorFormulaQuery", "transformQuery", "bundle"],
                   "ProofStrengtheningNodeSyntax": ["queryMatrix", "boundedMatrix", "body", "node"]}
    forbidden = re.compile(r"RawCode(?:Field|Get)\w*\.|FormulaCodeSyntax\.|WeakenFreeProgramSyntax\.|\bspecification\b|\bmetadata\b|\bimplicationRead\b|Expr\.eval|Classical\.choose|ObjectLocalDecision\.(?:checked|Rule\.checked)")
    bodies = {}
    for mod, names in definitions.items():
        body = strip_comments((ROOT / ("PPAC/Migration/Internal/" + mod + ".lean")).read_text(encoding="utf-8"))
        bodies[mod] = body
        for name in names:
            found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
            if not found or forbidden.search(found.group(0)):
                raise RuntimeError(f"Pure strengthening acceptance uses comparison oracle: {mod}.{name}")
    for i in range(4):
        if f"(ObjectProofNode.strengtheningShape.queries[{i}]).2" not in bodies["ProofStrengtheningSyntax"]:
            raise RuntimeError(f"Exact original strengthening query changed: {i}")
    for clause in ["graph ObjectProofNode.strengtheningShape.head w env row", "ProofStrengtheningSyntax.bundle w env", "HornExprBounds.environmentBound 4 row env", "existsMany 4 (body w row)"]:
        if clause not in bodies["ProofStrengtheningNodeSyntax"]:
            raise RuntimeError("Incomplete original pure strengthening node: " + clause)
    return {"definitions": definitions, "original_arity": 4, "original_head_field_count": 3, "actual_query_count": 4,
            "full_mode_zero_formula_run_and_successor_witness_discharged": True,
            "all_four_assignment_bounds_discharged": True,
            "whole_fixed_shape_pure_relational_node_iff_proved": True,
            "shared_extended_condition_numeric_quotation_Bool_correspondence_proved": False}


def check_original_mode_one_scalar_definitions() -> dict:
    """Original fixed rule selection; no numeric value/program specification defines acceptance."""
    selected = strip_comments((ROOT / "PPAC/Migration/Internal/OriginalAbstractClasses.lean").read_text(encoding="utf-8"))
    trace = strip_comments((ROOT / "PPAC/Migration/Internal/OriginalAbstractTrace.lean").read_text(encoding="utf-8"))
    for clause in ["[boundIdentity 1 true, boundAbstract, freeAbstractHead, freeAbstractTail, application 1]",
                   "if bound then [boundIdentity 1 true, boundAbstract] else [freeAbstractHead, freeAbstractTail]"]:
        if clause not in selected:
            raise RuntimeError("Original mode1 rule selection changed: " + clause)
    found = re.search(r"(?ms)^def variableStep\b.*?(?=^(?:def|theorem|end)\b|\Z)", trace)
    if not found or "HornStepSyntax.step (variableSelected bound) w r w" not in found.group(0):
        raise RuntimeError("Original mode1 variable query is not the exact original two-rule step")
    if re.search(r"SyntaxTop\w*\.|FormulaTransform\w*\.|\bvalueSpec\b|Expr\.eval|Classical\.choose", found.group(0)):
        raise RuntimeError("Mode1 variable acceptance uses comparison oracle")
    return {"mode": 1, "term_rule_count": 5, "bound_variable_rule_count": 2, "free_variable_rule_count": 2,
            "whole_variable_trace_iff_exact_original_bounded_applications_proved": True,
            "all_root_set_witness_discharged": True, "four_variable_rule_positive_traces_proved": True,
            "full_mode_one_formula_run_proved": True, "full_forall_node_proved": True}


def check_mode_one_variable_numeric_values() -> dict:
    """Independent internal value relation, distinct from original trace acceptance."""
    body = strip_comments((ROOT / "PPAC/Migration/Internal/AbstractVariableValueSyntax.lean").read_text(encoding="utf-8"))
    names = ["boundShifted", "boundValue", "freeTail", "freeValue", "valueSpec"]
    for name in names:
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
        if not found or re.search(r"Original\w*\.|Horn\w*\.|FormulaCodeSyntax\.|SyntaxTop\w*\.|FormulaTransform\w*\.|Expr\.eval|Classical\.choose", found.group(0)):
            raise RuntimeError("Mode1 numeric value relation uses acceptance/program oracle: " + name)
    return {"independent_definitions": names, "bound_preserved_and_shifted_branches_proved": True,
            "free_head_and_tail_branches_proved": True, "all_internal_candidate_outputs_iff_proved": True,
            "whole_original_variable_run_root_witness_discharged": True,
            "output_naturality_derived_not_assumed": True,
            "full_mode_one_formula_run_proved": True, "full_forall_node_proved": True}


def check_small_mode_arguments_and_pure_term_values() -> dict:
    """Keep independent pure-term numeric relation separate from original Run acceptance."""
    body = strip_comments((ROOT / "PPAC/Migration/Internal/AbstractTermValueSyntax.lean").read_text(encoding="utf-8"))
    for name in ["branch", "value"]:
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
        if not found or re.search(r"Original\w*\.|Horn\w*\.|SyntaxTop\w*\.|FormulaTransform\w*\.|Expr\.eval|Classical\.choose", found.group(0)):
            raise RuntimeError("Pure term numeric relation uses original acceptance oracle: " + name)
    return {"all_fixed_modes_below_four_original_argument_equations_proved": True,
            "mode_one_and_mode_two_exact_instances_checked": True,
            "original_nil_arity_three_and_cons_arity_seven_retained": True,
            "actual_child_Run1_and_Run2_queries_retained": True,
            "argument_root_and_all_root_set_witnesses_discharged": True,
            "pure_signature_all_terms_guarded_numeric_iff_proved": True,
            "argument_map_against_actual_abstract_coded_environment_proved": True,
            "legacy_argument_map_flag_scope": "arbitrary internal depth under the proved compatible frame",
            "zero_depth_actual_abstract_argument_map_proved": True,
            "full_mode_one_formula_run_proved": True, "full_forall_node_proved": True}


def check_actual_abstract_pure_term_operation() -> dict:
    """The actual comparison operation uses real code tables and mixed term substitution, never Run."""
    body = strip_comments((ROOT / "PPAC/Migration/Internal/AbstractTopTermSyntax.lean").read_text(encoding="utf-8"))
    for name in ["state", "body", "abstracted"]:
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
        if not found or re.search(r"OriginalTransformRowSyntax\.|HornLookup\w*\.|AbstractVariableValueSyntax\.|AbstractTermValueSyntax\.|Expr\.eval|Classical\.choose", found.group(0)):
            raise RuntimeError("Actual abstract pure term operation uses original acceptance/numeric oracle: " + name)
    if "SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S" not in body or "SyntaxCodedMixedTermSyntax.substituted w R S a B A b n q" not in body:
        raise RuntimeError("Actual abstract pure term operation changed its real environment or substitution")
    return {"actual_abstract_environment_and_mixed_term_operation_used": True,
            "all_internal_scoped_variables_table_agreement_proved": True,
            "zero_depth_all_valid_pure_term_program_and_coded_operation_iff_proved": True,
            "both_actual_code_table_witnesses_constructed_and_eliminated": True,
            "term_type_guard_inside_final_conclusion": True, "depth_required_empty": True,
            "binder_lifted_mode_one_frame_proved": True,
            "full_mode_one_formula_run_proved": True, "full_forall_node_proved": True}


def check_actual_abstract_argument_operation() -> dict:
    """Actual zero-depth map uses real tables and independent per-field programs."""
    body = strip_comments((ROOT / "PPAC/Migration/Internal/AbstractTopArgumentSyntax.lean").read_text(encoding="utf-8"))
    for name in ["state", "body", "abstracted"]:
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
        if not found or re.search(r"OriginalTransformRowSyntax\.|Horn\w*\.|OriginalArgumentFieldSyntax\.|OriginalNumericTermValueSyntax\.|Expr\.eval|Classical\.choose", found.group(0)):
            raise RuntimeError("Actual abstract argument operation uses acceptance oracle: " + name)
    for required in ["SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S", "ArgumentProgramFieldSyntax.mapped w R S k A b n q", "SyntaxMixedImageCodeSyntax.termList w k a B n", ".ex (.ex"]:
        if required not in body:
            raise RuntimeError("Actual abstract argument operation lost its real map/source guard: " + required)
    return {"zero_depth_actual_environment_program_map_iff_proved": True,
            "internal_list_length_not_externally_bounded": True,
            "list_IH_and_term_promise_discharged": True,
            "both_code_table_witnesses_constructed_and_eliminated": True,
            "source_list_type_guard_inside_final_conclusion": True, "depth_required_empty": True,
            "binder_lifted_argument_map_proved": True,
            "binder_lifted_argument_map_scope": "typed lists under proved compatible frames",
            "full_mode_one_formula_run_proved": True, "full_forall_node_proved": True}


def check_actual_abstract_frame() -> dict:
    """Compatibility is independent variable arithmetic on real typed tables, not Run correctness."""
    body = strip_comments((ROOT / "PPAC/Migration/Internal/AbstractOperationFrameSyntax.lean").read_text(encoding="utf-8"))
    for name in ["point", "compatible", "frame"]:
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", body)
        if not found or re.search(r"OriginalTransformRowSyntax\.|Horn\w*\.|OriginalArgumentFieldSyntax\.|OriginalNumericTermValueSyntax\.|TermTransformProgram\w*\.|Expr\.eval|Classical\.choose", found.group(0)):
            raise RuntimeError("Abstract frame uses operation/acceptance oracle: " + name)
    for required in ["SyntaxMixedImageCodeSyntax.termLists w a b c e R S", "AbstractVariableValueSyntax.valueSpec bound w depth i n q", "StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q", ".all (.all (.all"]:
        if required not in body:
            raise RuntimeError("Abstract frame lost actual all-internal variable/table contract: " + required)
    return {"arbitrary_internal_depth_compatible_frame_proved": True,
            "actual_top_environment_root_instance_proved": True,
            "actual_original_coded_binder_lift_preserves_frame_proved": True,
            "all_internal_scoped_variables_and_candidate_outputs_covered": True,
            "eight_lift_graph_map_head_witnesses_eliminated": True,
            "old_variable_code_and_field_witnesses_eliminated": True,
            "full_mode_one_formula_run_proved": True, "full_forall_node_proved": True}


def check_actual_abstract_frame_programs() -> dict:
    """Final arbitrary-depth endpoints carry no externally supplied Promise or list induction."""
    for module, name, premises in [
        ("AbstractFrameTerm", "program_iff", {"hw", "hF", "ht"}),
        ("AbstractFrameTerm", "guarded_coded_iff", {"hw", "hF"}),
        ("AbstractFrameTermFiber", "promise", {"hw", "hF"}),
        ("AbstractFrameArguments", "run_iff", {"hw", "hFrame", "hL"}),
        ("AbstractFrameArguments", "guarded_iff", {"hw", "hFrame"})]:
        text = strip_comments((ROOT / ("PPAC/Migration/Internal/" + module + ".lean")).read_text(encoding="utf-8"))
        found = re.search(r"(?ms)^theorem " + name + r"\b.*?(?=:=)", text)
        if not found or set(re.findall(r"\((\w+)\s*:\s*Derives Γ \(", found.group(0))) != premises:
            raise RuntimeError("Arbitrary-depth frame program contract changed: " + module + "." + name)
    return {"arbitrary_internal_depth_term_program_and_coded_operation_iff_proved": True,
            "actual_typed_unique_term_fiber_and_internal_promise_proved": True,
            "arbitrary_internal_depth_argument_program_field_map_iff_proved": True,
            "list_IH_and_term_promise_discharged": True,
            "source_type_guards_inside_final_conclusions": True,
            "source_target_bound_lengths_remain_independent": True,
            "full_mode_one_formula_run_proved": True, "full_forall_node_proved": True}


def check_small_mode_formula_and_abstract_atomic_programs() -> dict:
    """Use original eleven outcomes and real mode1 frame, never the old Boolean mode0 interface."""
    modules = ["SmallModeFormulaMatrix", "SmallModeFormulaConstantApplication", "SmallModeFormulaTrace", "SmallModeFormulaRun", "SmallModeAtomicDispatch", "AbstractFrameAtomicAgreement", "AbstractFrameAtomicExisting", "AbstractFrameTypedAtomic", "AbstractFrameAtomic"]
    for module in modules:
        text = strip_comments((ROOT / ("PPAC/Migration/Internal/" + module + ".lean")).read_text(encoding="utf-8"))
        if re.search(r"OriginalFormulaRunEquation\.run_iff|OriginalAtomicRunDispatch\.run_iff|OriginalMemberRunDispatch\.run_iff|Expr\.eval|Classical\.choose", text):
            raise RuntimeError("New small-mode formula/atomic proof uses old Boolean Run or host oracle: " + module)
        if re.search(r"(?m)^(?:def|axiom) ", text):
            raise RuntimeError("New proof route must reuse actual acceptance/program definitions: " + module)
    return {"every_fixed_mode_below_four_original_formula_constant_guard_proved": True,
            "original_eleven_outcomes_and_all_actual_child_queries_retained": True,
            "whole_formula_Run3_unfold_equation_proved": True,
            "actual_mode_one_instance_checked": True,
            "arbitrary_internal_depth_mode_one_all_four_atomic_program_iff_proved": True,
            "term_and_pair_agreements_proved_not_assumed": True,
            "atomic_source_field_and_pair_length_witnesses_eliminated": True,
            "full_mode_one_formula_run_proved": True, "full_forall_node_proved": True}


def check_mode_one_full_formula_correctness() -> dict:
    """All internal formula codes, varying frames, real lifted binders, discharged object IH."""
    directory = ROOT / "PPAC/Migration/Internal"
    texts = {m: strip_comments((directory / (m + ".lean")).read_text(encoding="utf-8")) for m in [
        "AbstractUniformInductionSyntax", "AbstractUniformInductionRules", "SmallModeLogicalDispatch",
        "SmallModeLogicalProgram", "SmallModeLogicalFromInduction", "AbstractBinderReadAtLift",
        "AbstractBinderAdvance", "AbstractBinderCaseBridge", "AbstractBinderProgram",
        "AbstractFullFormulaProgram", "AbstractFormulaCorrectnessPoint",
        "AbstractFormulaCorrectnessInduction", "AbstractTopFormula"]}
    for module, name, premises in [
        ("AbstractFormulaCorrectnessInduction", "run_iff_execution", {"hw", "hf", "hn"}),
        ("AbstractFormulaCorrectnessInduction", "run_iff_program", {"hw", "hf", "hn", "hg"}),
        ("AbstractFormulaCorrectnessInduction", "agreed_history_exists", {"hw", "hn", "hf"}),
        ("AbstractTopFormula", "run_iff_execution", {"hw", "hm", "hd", "hz", "he", "hn"}),
        ("AbstractTopFormula", "run_iff_program", {"hw", "hm", "hd", "hz", "he", "hn", "hg"})]:
        found = re.search(r"(?ms)^theorem " + name + r"\b.*?(?=:=)", texts[module])
        if not found or set(re.findall(r"\((\w+)\s*:\s*Derives Γ \(", found.group(0))) != premises:
            raise RuntimeError("Full formula final contract changed: " + module + "." + name)
        if re.search(r"Model|Consistent|Classical\.choose|allFramesIH|prefixIH|Promise", found.group(0)):
            raise RuntimeError("Undischarged assumption in final formula contract")
    clauses = {
        "AbstractUniformInductionSyntax": ["(AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp", "(FormulaCodeSyntax.formulaCode w n a b).imp", "(OriginalTransformRowSyntax.run 3 w mode depth P n q).iff", "FormulaTransformExecutionSyntax.executed w R S a b c e n q", "Fin 10 → Fin m", "allMany 10 (body w n)"],
        "AbstractUniformInductionRules": ["AbstractOperationFrameBinder.lifted", "prefix_at_frame w n mode D P A b C e K H"],
        "SmallModeLogicalDispatch": ["(modeIndex : Nat) (hSmall : modeIndex < 4)", "SmallModeFormulaRun.run_iff"],
        "AbstractBinderReadAtLift": ["AbstractUniformInductionRules.binder_prefix", "OriginalHistoryRead.read_iff_executed"],
        "AbstractBinderAdvance": ["SyntaxCodedMixedBinderExistence.exists_pair", "OriginalBinderStepSyntax.successor_exists w a hw ha", "OriginalBinderStepSyntax.successor_exists w.castSucc c.castSucc", "(slot 4 1) (old 4 e) (old 4 X) Fin.castSucc"],
        "AbstractBinderProgram": ["SmallModeLogicalDispatch.run_iff_quantified hZ 1 (by decide)", "AbstractBinderCaseBridge.quantified_iff"],
        "AbstractFullFormulaProgram": ["AbstractFrameAtomic.program_iff", "SmallModeLogicalFromInduction", "AbstractBinderProgram.quantified_iff", "FormulaCodeRecursiveSyntax.singleCase 9 true", "FormulaCodeRecursiveSyntax.singleCase 10 true"],
        "AbstractFormulaCorrectnessPoint": ["FormulaTransformRecursionCorrectness.graph_exists", "HornBinderRules.eliminate_many 1", "FormulaTransformRootStep.execution_iff_program"],
        "AbstractFormulaCorrectnessInduction": ["SetInduction.all_holds", "ZFContext.separation hZ", ".base.foundation", "ObjectTransitiveCover.source_cover", "correct_at w n mode depth P a b c e R S q (at_root hZ w n hw) hf hn"],
        "AbstractTopFormula": ["AbstractOperationFrameRoot.from_actual", "SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S", "FormulaTransformExecutionSyntax.executed w R S a B A b n q"]}
    for module, required in clauses.items():
        for clause in required:
            if clause not in texts[module]:
                raise RuntimeError("Missing actual full formula derivation clause: " + module + ": " + clause)
    for module, body in texts.items():
        if re.search(r"OriginalOperationFrameSyntax\.|OriginalUniformInductionSyntax\.|\(three : Bool\)|Classical\.choose|\.model\b", body):
            raise RuntimeError("Unexpected old restricted mode or semantic shortcut in " + module)
    return {"all_internal_typed_formula_codes_at_arbitrary_internal_depth_proved": True,
            "all_ten_frame_and_output_parameters_object_quantified": True,
            "all_eleven_original_formula_constructors_proved": True,
            "actual_source_target_bound_lengths_independent": True,
            "real_lifted_binder_tables_and_separate_successors_constructed": True,
            "object_set_induction_IH_and_history_existence_discharged": True,
            "actual_AbstractFreeTop_environment_root_formula_bridge_proved": True,
            "full_mode_one_formula_run_proved": True,
            "full_forall_node_proved": True,
            "shared_quotation_Proof_and_Con_proved": False}


def check_actual_top_formula_and_forall_node() -> dict:
    """Actual AbstractFreeTop and all four original forall queries, bounds and nested head."""
    directory = ROOT / "PPAC/Migration/Internal"
    modules = ["AbstractTopFormulaOperation", "ProofForallSyntax", "ProofForallQueries",
               "ProofForallAllQueries", "ProofForallBounds", "ProofForallHead", "ProofForallNodeSyntax", "ProofForallNode"]
    texts = {m: strip_comments((directory / (m + ".lean")).read_text(encoding="utf-8")) for m in modules}
    contracts = [
        ("AbstractTopFormulaOperation", "at_codes_iff", {"hw", "hm", "hd", "hz", "he", "hn"}),
        ("AbstractTopFormulaOperation", "run_iff", {"hw", "hm", "hd", "hz", "hi", "hn"}),
        ("AbstractTopFormulaOperation", "guarded_iff", {"hw", "hm", "hd", "hz", "hi"}),
        ("ProofForallAllQueries", "bundle_iff", {"hw", "hn", "hz"}),
        ("ProofForallBounds", "environment_bound", {"hw", "hn", "hh", "hq"}),
        ("ProofForallHead", "head_iff", {"hw", "hn"}),
        ("ProofForallNode", "node_iff", {"hw", "hz"}),
        ("ProofForallNode", "normalized_node_iff", {"hw", "hz"})]
    for module, name, premises in contracts:
        header = re.search(r"(?ms)^theorem " + name + r"\b.*?(?=:=)", texts[module])
        if not header or set(re.findall(r"\((\w+)\s*:\s*Derives Γ \(", header.group(0))) != premises:
            raise RuntimeError("Actual top/forall final contract changed: " + module + "." + name)
        if re.search(r"Model|Consistent|Classical\.choose|Promise|allFramesIH|hIH\s*:", header.group(0)):
            raise RuntimeError("Unexpected external oracle in actual top/forall interface")
    clauses = {
        "AbstractTopFormulaOperation": ["AbstractTopFormula.run_iff_execution", "FormulaTransformRecursionCorrectness.execution_iff", "SyntaxTopFormulaCodes.abstract_at_codes", "SyntaxTopCodedEnvironmentExistence.abstract_exists", "SyntaxRenameBinders.eliminate_2", "((FormulaCodeSyntax.formulaCode w n a B).conj (OriginalTransformRowSyntax.run 3 w mode z P n q)).iff"],
        "ProofForallSyntax": ["ObjectProofNode.forallShape.queries[0]", "ObjectProofNode.forallShape.queries[1]", "ObjectProofNode.forallShape.queries[2]", "ObjectProofNode.forallShape.queries[3]", "ObjectProofNode.formula (.succ (.var 0)) (.var 3)", "ObjectProofNode.transform 1 (.literal 0) (.var 3) (.var 1)", "SyntaxTopFormulaSyntax.abstracted w z (env 0) A B (env 3) (env 1)"],
        "ProofForallQueries": ["OriginalTransformRowSyntax.run 3 w A z z (env 3) (env 1)", "HornRowFields.five (.literal 1) (.literal 0) (.literal 0) (.var 3) (.var 1)", "SyntaxNumeralSyntax.intro_succ 0 A z hz hA", "AbstractTopFormulaOperation.run_iff"],
        "ProofForallAllQueries": ["InsertExistence.exists_insert (env 0) (env 0)", "InsertExistence.exists_insert z z", "Derives.exE", "intro_atOneSpecification", "intro_specification"],
        "ProofForallBounds": ["ProofSubstitutionBounds.atOne_bound", "NaturalOrderBasic.transitive", "HornExprBounds.intro_environmentBound", "head_first_variables"],
        "ProofForallHead": ["ObjectProofNode.node 9 [.var 1]", "SyntaxNodeSyntax.constructor 1 9", "SyntaxNodeSyntax.constructor 3 3", "HornExprExistence.exists_value", "HornExprConstructor.constructor_iff", "Derives.exE"],
        "ProofForallNodeSyntax": ["graph ObjectProofNode.forallShape.head", "ProofForallSyntax.bundle", "HornExprBounds.environmentBound 4", "existsMany 4 (body w row)"],
        "ProofForallNode": ["ProofForallAllQueries.bundle_iff", "ProofForallBounds.environment_bound", "HornApplicationBounds.existsMany_congr 4", "ProofForallHead.head_iff", "normalized_node_iff"]}
    for module, required in clauses.items():
        for clause in required:
            if clause not in texts[module]:
                raise RuntimeError("Missing original forall construction clause: " + module + ": " + clause)
    for module, body in texts.items():
        if re.search(r"Expr\.eval|Classical\.choose|OriginalFormulaRunEquation\.run_iff.*false|WellFounded|Model|Consistent", body):
            raise RuntimeError("Host computation or restricted-mode shortcut in " + module)
    # Acceptance definitions refer to actual original query expressions, not their comparison specification.
    for name in ["formulaQuery", "freeQuery", "predecessorFormulaQuery", "transformQuery", "bundle"]:
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|end)\b|\Z)", texts["ProofForallSyntax"])
        if not found or re.search(r"FormulaCodeSyntax|SyntaxTopFormulaSyntax|specification|atSuccessor", found.group(0)):
            raise RuntimeError("Forall acceptance contains comparison oracle: " + name)
    return {"actual_mode_one_full_formula_AbstractFreeTop_operation_proved": True,
            "both_actual_code_table_witnesses_discharged": True,
            "source_type_guard_inside_final_conclusion": True,
            "original_arity": 4, "actual_query_count": 4,
            "original_mode_one_zero_depth_input_output_direction_checked": True,
            "both_bound_and_free_successor_witnesses_discharged": True,
            "nested_quantifier_and_outer_head_numeric_constructors_proved": True,
            "all_four_original_assignment_bounds_derived": True,
            "full_forall_node_proved": True,
            "shared_quotation_Bool_Proof_and_Con_proved": False}


def check_mode_two_variables_and_frame_terms() -> dict:
    """Genuine Num2 variable Run1, all internal outputs, and the explicit conditional frame."""
    directory = ROOT / "PPAC/Migration/Internal"
    modules = ["OriginalInstantiateClasses", "OriginalInstantiateDispatch", "OriginalInstantiatePositive",
               "OriginalInstantiateTrace", "InstantiateVariableValueSyntax", "InstantiateVariableSound",
               "InstantiateOperationFrameSyntax", "InstantiateVariableComplete", "InstantiateVariableNumeric",
               "InstantiateVariableRun", "InstantiateFrameTerm"]
    texts = {m: strip_comments((directory / (m + ".lean")).read_text(encoding="utf-8")) for m in modules}
    for module, name, premises in [
        ("InstantiateVariableRun", "run_iff", {"hw", "hm", "hd", "hv"}),
        ("InstantiateVariableNumeric", "bound_iff", {"hw", "hc", "hm", "hv"}),
        ("InstantiateVariableNumeric", "free_iff", {"hw", "hc", "hm", "hv"}),
        ("InstantiateFrameTerm", "program_iff", {"hw", "hF", "ht"}),
        ("InstantiateFrameTerm", "coded_iff", {"hw", "hF", "ht"}),
        ("InstantiateFrameTerm", "guarded_coded_iff", {"hw", "hF"})]:
        header = re.search(r"(?ms)^theorem " + name + r"\b.*?(?=:=)", texts[module])
        if not header or set(re.findall(r"\((\w+)\s*:\s*Derives Γ \(", header.group(0))) != premises:
            raise RuntimeError("Mode2 endpoint contract changed: " + module + "." + name)
        if re.search(r"Promise|Model|Consistent|Classical\.choose|hIH\s*:", header.group(0)):
            raise RuntimeError("Mode2 final endpoint has an unproved oracle")
    for module in ["OriginalInstantiateDispatch", "OriginalInstantiateTrace", "InstantiateVariableRun"]:
        if "SyntaxNumeralSyntax.numeral 2" not in texts[module] or "SyntaxNumeralSyntax.numeral 1 " in texts[module]:
            raise RuntimeError("Mode2 must use the actual Num2 guard: " + module)
    values = texts["InstantiateVariableValueSyntax"]
    if re.search(r"OriginalTransform|HornLookup|TermTransformProgram|StructuralListField|SyntaxTopFormula", values):
        raise RuntimeError("Independent mode2 numeric value contains an acceptance/comparison oracle")
    required = {
        "OriginalInstantiateClasses": ["[boundIdentity 2 true, boundPoint, boundPredecessor, freeIdentity, application 1]", "if bound then [boundIdentity 2 true, boundPoint, boundPredecessor] else [freeIdentity]"],
        "OriginalInstantiateDispatch": ["SyntaxNumerals.different hZ1 tag 2 hne", "OriginalVariableDispatch.input_rejected"],
        "OriginalInstantiateTrace": ["HornUniversalTraceValue.exists_value", "HornUniversalTraceClosed.unfold_iff", "OriginalInstantiateDispatch.variable_dispatch_iff", "SyntaxNumeralSyntax.numeral_rename 2"],
        "InstantiateVariableValueSyntax": ["Formula.mem idx depth", "Formula.equal idx depth", "successor idx.castSucc (Fin.last m)", "Formula.mem depth.castSucc idx.castSucc", "if bound then boundValue w depth P idx x y else .equal y x"],
        "InstantiateVariableComplete": ["HornExprConstructor.constructor_iff", "OriginalInstantiatePositive.bound_point", "OriginalInstantiatePositive.bound_predecessor", "apply Derives.exE"],
        "InstantiateVariableNumeric": ["InstantiateVariableSound.application_bound_point", "InstantiateVariableComplete.from_tail", "InstantiateVariableComplete.free_identity"],
        "InstantiateVariableRun": ["SyntaxConstructors.exists_constructor", "OriginalTransformRowSyntax.intro_run 1", "(add (.conjR hd) E)", "SyntaxNumerals.range (ZFContext.add hZ E) 2"],
        "InstantiateOperationFrameSyntax": ["closedParameter w e P", "EmptyBoundFreeInputs.term_free", "(OmegaSyntax.successor a depth).conj ((Formula.equal c depth).conj (.equal e b))", "contextsAtDepth depth a b c e"],
        "InstantiateFrameTerm": ["InstantiateVariableRun.run_iff", "compatible_at bound w depth P a b", "OriginalTermScopeElimination.eliminate", "TermTransformProgramCorrectness.at_typed_term", "SyntaxCodedMixedTermTyping.source_type"]}
    for module, clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:
                raise RuntimeError("Missing actual mode2 derivation: " + module + ": " + clause)
    classes = re.search(r"(?ms)^theorem classified.*?(?=^theorem selected_mem)", texts["OriginalInstantiateClasses"]).group(0)
    if len(re.findall(r"^  ·", classes, re.MULTILINE)) != 28:
        raise RuntimeError("The complete original 28 rules must be classified")
    frame = texts["InstantiateOperationFrameSyntax"]
    if re.search(r"OriginalTransformRowSyntax|HornLookupConditionSyntax|TermTransformProgramSyntax|FormulaTransformExecutionSyntax", frame):
        raise RuntimeError("Mode2 frame contains its final operation theorem")
    return {"genuine_Num2_original_twenty_eight_rule_dispatch_proved": True,
            "all_internal_variable_codes_and_candidate_outputs_numeric_iff_proved": True,
            "whole_Run1_root_row_and_output_naturality_witnesses_discharged": True,
            "point_parameter_output_naturality_from_metadata_proved": True,
            "conditional_mode2_frame_typed_term_program_and_coded_iff_proved": True,
            "closed_parameter_and_source_successor_target_depth_guards_explicit": True,
            "actual_mode2_frame_root_and_binder_closure_proved": True,
            "mode2_full_formula_and_InstantiateTop_operation_proved": True,
            "Proof_and_final_internal_Con_proved": False}


def check_mode_two_actual_root() -> dict:
    """Actual instantiateCoded supplies the root; the binder is separately checked."""
    directory = ROOT / "PPAC/Migration/Internal"
    names = ["InstantiateClosedParameterRename", "InstantiateVariableSpecialization", "InstantiateOperationFrameRoot", "InstantiateTopTermOperation"]
    texts = {n: strip_comments((directory / (n + ".lean")).read_text(encoding="utf-8")) for n in names}
    for module, theorem, premises in [
        ("InstantiateClosedParameterRename", "closed_iff", {"hw", "hU", "hV", "hp"}),
        ("InstantiateOperationFrameRoot", "from_actual_input", {"hw", "hm", "hz", "he"}),
        ("InstantiateTopTermOperation", "program_iff", {"hw", "hm", "hz", "he", "ht"}),
        ("InstantiateTopTermOperation", "coded_iff", {"hw", "hm", "hz", "he", "ht"}),
        ("InstantiateTopTermOperation", "guarded_coded_iff", {"hw", "hm", "hz", "he"})]:
        header = re.search(r"(?ms)^theorem " + theorem + r"\b.*?(?=:=)", texts[module])
        if not header or set(re.findall(r"\((\w+)\s*:\s*Derives Γ \(", header.group(0))) != premises:
            raise RuntimeError("Actual mode2 root endpoint changed: " + module + "." + theorem)
        if re.search(r"Promise|Model|Consistent|Classical\.choose|hIH\s*:|hF\s*:", header.group(0)):
            raise RuntimeError("Actual mode2 root assumes an unproved oracle/frame")
    required = {
        "InstantiateClosedParameterRename": ["SyntaxTermSyntax.eliminate_branch", "AbstractBinderRename.free_at", "AbstractBinderRename.code_iff_equal", "InstantiateOperationFrameSyntax.closedParameter_free"],
        "InstantiateVariableSpecialization": ["NaturalOrderBasic.nonself", "NaturalOrderBasic.below_not_reverse", "apply Derives.exE"],
        "InstantiateOperationFrameRoot": ["SyntaxTopCodedEnvironmentFields.instantiate_zero", "SyntaxTopCodedEnvironmentFields.instantiate_free", "SyntaxTopCodedEnvironmentTyping.instantiate_lists", "SyntaxTerms.range", "OmegaStructureAlgebra.zero_member", "intro_closedParameter", "compatible_from_actual hZ true", "compatible_from_actual hZ false"],
        "InstantiateTopTermOperation": ["InstantiateOperationFrameRoot.from_actual_input", "InstantiateFrameTerm.program_iff", "InstantiateFrameTerm.coded_iff", "InstantiateFrameTerm.guarded_coded_iff"]}
    for module, clauses in required.items():
        if re.search(r"^(?:def|axiom|unsafe)\s", texts[module], re.MULTILINE):
            raise RuntimeError("Actual mode2 root proof must not change acceptance definitions")
        for clause in clauses:
            if clause not in texts[module]:
                raise RuntimeError("Missing actual root derivation: " + module + ": " + clause)
    check = (ROOT / "CheckStep4.lean").read_text(encoding="utf-8")
    if "ObjectInstantiateRoot.native_modeTwoActualRootGuardedTermCodedIff w mode z P b A R S n q" not in check:
        raise RuntimeError("Missing expanded actual root native contract")
    return {"closed_parameter_actual_binder_rename_iff_identity_proved": True,
            "actual_InstantiateTop_root_frame_from_code_tables_proved": True,
            "root_metadata_and_variable_compatibility_discharged": True,
            "actual_root_all_internal_typed_term_program_and_coded_iff_proved": True,
            "actual_root_source_guard_inside_conclusion": True,
            "actual_binder_frame_closure_proved": True,
            "mode2_full_formula_and_InstantiateTop_operation_proved": True,
            "Proof_and_final_internal_Con_proved": False}


def check_mode_two_actual_binder() -> dict:
    """Actual coded lifting preserves the Num2 frame with the same raw parameter P."""
    directory = ROOT / "PPAC/Migration/Internal"
    modules = ["InstantiateBinderGeometry", "InstantiateBinderVariablePoint", "InstantiateBinderVariable",
               "InstantiateFrameLiftPoint", "InstantiateFrameLiftValues", "InstantiateFrameLiftCompatibility", "InstantiateOperationFrameBinder"]
    texts = {n: strip_comments((directory / (n + ".lean")).read_text(encoding="utf-8")) for n in modules}
    for module, theorem, premises in [
        ("InstantiateBinderGeometry", "lifted_contexts", {"hc", "hD", "hA", "hC"}),
        ("InstantiateOperationFrameBinder", "lifted", {"hw", "hF", "hD", "hl"})]:
        header = re.search(r"(?ms)^theorem " + theorem + r"\b.*?(?=:=)", texts[module])
        if not header or set(re.findall(r"\((\w+)\s*:\s*Derives Γ \(", header.group(0))) != premises:
            raise RuntimeError("Actual mode2 binder endpoint changed: " + module + "." + theorem)
        if re.search(r"Promise|Model|Consistent|Classical\.choose|hIH\s*:", header.group(0)):
            raise RuntimeError("Actual mode2 binder assumes an unproved oracle")
    for module, text in texts.items():
        if re.search(r"^(?:def|axiom|unsafe)\s", text, re.MULTILINE):
            raise RuntimeError("Binder proof module may not change acceptance definitions")
        if re.search(r"AbstractOperationFrameSyntax|AbstractVariableValueSyntax|freeValue|boundShifted|Expr\.eval", text):
            raise RuntimeError("Mode2 binder accidentally uses mode1 values/host evaluation: " + module)
    required = {
        "InstantiateBinderGeometry": ["OmegaUniversal.successor_unique a D d", "successor_base_subst A a D", "successor_point hZ d c D C"],
        "InstantiateBinderVariablePoint": ["InstantiateVariableSpecialization.below_iff", "InstantiateVariableSpecialization.at_point_iff", "InstantiateClosedParameterRename.closed_iff", "InstantiateBinderGeometry.successor_point"],
        "InstantiateBinderVariable": ["InsertLogic.member_cases a d d i ha hi", "InstantiateBinderVariablePoint.preserved", "InstantiateBinderVariablePoint.at_point", "AbstractBinderRename.free_at"],
        "InstantiateFrameLiftPoint": ["SyntaxCodedMixedBinderFields.zero_iff", "SyntaxCodedMixedBinderFields.bound_iff", "SyntaxCodedMixedBinderFields.free_iff", "parameter_closed w mode depth P a b c e R S hF"],
        "InstantiateFrameLiftValues": ["SyntaxVariables.exists_code", "StructuralListFieldValues.exists_value", "InstantiateFrameLiftPoint.bound_at", "InstantiateFrameLiftPoint.free_at"],
        "InstantiateFrameLiftCompatibility": ["OmegaStructureAlgebra.decomposition_at", "SyntaxIndexLiftOrder.predecessor_member", "InstantiateBinderGeometry.lifted_contexts", "SyntaxCodedMixedBinderTyping.output_lists", "parameter_closed w mode depth P a b c e R S hF"],
        "InstantiateOperationFrameBinder": ["SyntaxRenameBinders.eliminate_4 B _ hl", "SyntaxRenameBinders.eliminate_4 T _ (.conjL (.conjR hB))", "InstantiateFrameLiftCompatibility.at_witnesses"]}
    for module, clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:
                raise RuntimeError("Missing actual mode2 binder derivation: " + module + ": " + clause)
    if texts["InstantiateOperationFrameBinder"].count("apply SyntaxRenameBinders.eliminate_4") != 2:
        raise RuntimeError("Both actual four-witness blocks must be eliminated")
    if "frame w mode D P A b C e K H" not in texts["InstantiateOperationFrameBinder"]:
        raise RuntimeError("Original mode2 binder must retain P")
    check = (ROOT / "CheckStep4.lean").read_text(encoding="utf-8")
    if "ObjectInstantiateBinder.native_modeTwoActualBinderFrame w mode depth P D R S a b c e A C K H" not in check:
        raise RuntimeError("Missing expanded actual mode2 binder native endpoint")
    return {"independent_source_target_successors_aligned_by_object_uniqueness": True,
            "all_scoped_bound_indices_split_below_or_point_by_actual_source_successor": True,
            "point_parameter_preserved_by_actual_binder_rename": True,
            "fresh_zero_bound_successor_and_free_fields_compatible": True,
            "old_variable_and_field_value_witnesses_object_eliminated": True,
            "both_actual_four_witness_lift_blocks_object_eliminated": True,
            "actual_mode2_frame_binder_closure_proved": True,
            "raw_parameter_P_unchanged": True,
            "mode2_full_formula_and_InstantiateTop_operation_proved": True,
            "Proof_and_final_internal_Con_proved": False}


def check_mode_two_full_formula() -> dict:
    """All internal typed Num2 formula runs and the existing empty-bound-target InstantiateTop."""
    directory = ROOT / "PPAC/Migration/Internal"
    modules = ["InstantiateFrameTermFiber", "InstantiateFrameArguments", "InstantiateFrameAtomicAgreement",
               "InstantiateFrameAtomicExisting", "InstantiateFrameTypedAtomic", "InstantiateFrameAtomic",
               "InstantiateUniformInductionSyntax", "InstantiateUniformInductionRules", "InstantiateBinderReadAtLift",
               "InstantiateBinderAdvance", "InstantiateBinderCaseBridge", "InstantiateBinderProgram",
               "InstantiateFullFormulaProgram", "InstantiateFormulaCorrectnessPoint", "InstantiateFormulaCorrectnessInduction",
               "InstantiateTopFormula", "InstantiateTopFormulaOperation"]
    texts = {n: strip_comments((directory / (n + ".lean")).read_text(encoding="utf-8")) for n in modules}
    for module, theorem, premises in [
        ("InstantiateFrameTermFiber", "promise", {"hw", "hF"}),
        ("InstantiateFrameArguments", "run_iff", {"hw", "hFrame", "hL"}),
        ("InstantiateFrameArguments", "guarded_iff", {"hw", "hFrame"}),
        ("InstantiateFrameAtomic", "program_iff", {"hw", "hF", "hA"}),
        ("InstantiateFormulaCorrectnessInduction", "all_correct", {"hw"}),
        ("InstantiateFormulaCorrectnessInduction", "at_root", {"hw"}),
        ("InstantiateFormulaCorrectnessInduction", "run_iff_execution", {"hw", "hf", "hn"}),
        ("InstantiateFormulaCorrectnessInduction", "run_iff_program", {"hw", "hf", "hn", "hg"}),
        ("InstantiateTopFormulaOperation", "at_codes_iff", {"hw", "hm", "hz", "he", "hn"}),
        ("InstantiateTopFormulaOperation", "run_iff", {"hw", "hm", "hz", "hi", "hn"}),
        ("InstantiateTopFormulaOperation", "guarded_iff", {"hw", "hm", "hz", "hi"})]:
        header = re.search(r"(?ms)^theorem " + theorem + r"\b.*?(?=:=)", texts[module])
        if not header or set(re.findall(r"\((\w+)\s*:\s*Derives Γ \(", header.group(0))) != premises:
            raise RuntimeError("Mode2 full formula endpoint changed: " + module + "." + theorem)
        if re.search(r"Promise|Model|Consistent|Classical\.choose|hIH\s*:", header.group(0)):
            raise RuntimeError("Mode2 final formula endpoint has an unproved oracle")
    for module, text in texts.items():
        if re.search(r"Abstract(?:OperationFrame|Frame|UniformInduction|FullFormula|FormulaCorrectness|Binder|TopFormula)|Expr\.eval|Classical\.choose", text):
            raise RuntimeError("Mode2 formula accidentally uses the old mode1 proof or host evaluation: " + module)
        if re.search(r"SmallMode\w+\.\w+ hZ 1 \(by decide\)", text):
            raise RuntimeError("Mode2 formula must instantiate the generic dispatch with 2: " + module)
        if re.search(r"^def ", text, re.MULTILINE) and module not in ["InstantiateUniformInductionSyntax", "InstantiateFormulaCorrectnessInduction"]:
            raise RuntimeError("Mode2 proof module must not introduce acceptance definitions: " + module)
    required = {
        "InstantiateFrameTermFiber": ["TermTransformProgramValue.actual_fiber", "OriginalNumericTermValueTransfer.fiber_of_program", "InstantiateFrameTerm.program_iff"],
        "InstantiateFrameArguments": ["SmallModeArgumentFieldCompletion.run_iff hZ 2 (by decide)", "InstantiateFrameTermFiber.promise", "InstantiateFrameTerm.program_iff"],
        "InstantiateFrameAtomicExisting": ["SmallModeAtomicDispatch.run_iff_application hZ 2", "SmallModeAtomicDispatch.run_iff_equality hZ 2", "SmallModeAtomicDispatch.run_iff_false hZ 2", "SmallModeAtomicDispatch.run_iff_true hZ 2"],
        "InstantiateUniformInductionSyntax": ["Fin 10", "allMany 10", "InstantiateOperationFrameSyntax.frame", "allFramesIH"],
        "InstantiateUniformInductionRules": ["InstantiateOperationFrameBinder.lifted", "OriginalHistoryFromInduction.from_graph", "OriginalHistoryFromInduction.exists_agreed_history"],
        "InstantiateBinderReadAtLift": ["InstantiateUniformInductionRules.binder_prefix", "OriginalHistoryRead.read_iff_executed"],
        "InstantiateBinderAdvance": ["SyntaxCodedMixedBinderExistence.exists_pair", "OriginalBinderStepSyntax.successor_exists", "InstantiateBinderReadAtLift.read_at_lift_iff"],
        "InstantiateBinderProgram": ["SmallModeLogicalDispatch.run_iff_quantified hZ 2"],
        "InstantiateFullFormulaProgram": ["SmallModeLogicalFromInduction.negation_iff hZ 2", "SmallModeLogicalFromInduction.binary_iff hZ 2", "InstantiateBinderProgram.quantified_iff", "have h7 :", "disj_imp h0"],
        "InstantiateFormulaCorrectnessPoint": ["FormulaTransformRecursionCorrectness.graph_exists", "execution_iff_from_induction", "OriginalUniversalBlock.intro_many 10"],
        "InstantiateFormulaCorrectnessInduction": ["SetInduction.all_holds", "ZFContext.separation hZ (matrix ).neg", "ObjectTransitiveCover.source_cover", "correct_at w n mode depth P a b c e R S q (at_root hZ w n hw)"],
        "InstantiateTopFormula": ["InstantiateOperationFrameRoot.from_actual_input", "SyntaxNumeralSyntax.numeral 2 mode"],
        "InstantiateTopFormulaOperation": ["SyntaxTopFormulaCodes.instantiate_at_codes", "SyntaxTopCodedEnvironmentExistence.instantiate_exists", "SyntaxRenameBinders.eliminate_2 D", "SyntaxTopFormulaTyping.instantiate_source_type", "SyntaxNumeralSyntax.numeral 2 mode"]}
    for module, clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:
                raise RuntimeError("Missing full internal mode2 derivation: " + module + ": " + clause)
    check = (ROOT / "CheckStep4.lean").read_text(encoding="utf-8")
    for name in ["modeTwoAllInternalWholeFormulaExecutionIff w n mode depth P a b c e R S q", "modeTwoActualInstantiateTopGuardedIff w mode z P b A n q"]:
        if "ObjectInstantiateFormula.native_" + name not in check:
            raise RuntimeError("Missing expanded mode2 native contract: " + name)
    return {"genuine_Num2_full_term_fiber_and_argument_program_proved": True,
            "all_four_atomic_and_all_eleven_formula_cases_proved": True,
            "all_ten_changing_parameters_object_quantified": True,
            "original_ZF_Separation_Foundation_SetInduction_discharges_formula_IH": True,
            "actual_history_and_independent_binder_witnesses_object_eliminated": True,
            "mode2_full_typed_internal_formula_run_proved": True,
            "actual_empty_bound_target_InstantiateTop_operation_proved": True,
            "actual_root_code_table_pair_constructed_and_object_eliminated": True,
            "final_source_type_guard_inside_conclusion": True,
            "shared_original_quotation_checker_Proof_and_final_Con_proved": False}


def check_logical_instantiation_nodes() -> dict:
    """Exact original logical 20/23/25 queries, bounded assignments and numeric nested heads."""
    directory = ROOT / "PPAC/Migration/Internal"
    modules = ['LogicalInstantiateQueries', 'LogicalInstantiateSyntax', 'LogicalInstantiateAllQueries',
               'LogicalRule20Head', 'LogicalRule23Head', 'LogicalRule25Head',
               'LogicalInstantiateNodeSyntax', 'LogicalInstantiateNode', 'ObjectLogicalInstantiate']
    texts = {n: strip_comments((directory / (n + '.lean')).read_text(encoding='utf-8')) for n in modules}
    contracts = [('LogicalInstantiateQueries', 'typed_transform_iff', {'hw','hn','hz','hA','hp','hf'}),
                 ('LogicalInstantiateAllQueries', 'bundle4_iff', {'hw','hn','hz'}),
                 ('LogicalInstantiateAllQueries', 'bundle6_iff', {'hw','hn','hz'}),
                 ('LogicalInstantiateNode', 'normalized_node4_iff', {'hw','hz'}),
                 ('LogicalInstantiateNode', 'normalized_node6_iff', {'hw','hz'})]
    contracts += [(n, 'head_iff', {'hw','hn'}) for n in ['LogicalRule20Head','LogicalRule23Head','LogicalRule25Head']]
    for module, theorem, premises in contracts:
        header = re.search(r'(?ms)^theorem ' + theorem + r'\b.*?(?=:=)', texts[module])
        if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(', header.group(0))) != premises:
            raise RuntimeError('Logical instantiation contract changed: ' + module + '.' + theorem)
        if re.search(r'Promise|Model|Consistent|Classical\.choose|hIH\s*:', header.group(0)):
            raise RuntimeError('Unproved logical node premise: ' + module)
    for module, text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|axiom|unsafe|native_decide)\b', text):
            raise RuntimeError('Forbidden logical instantiation shortcut: ' + module)
    required = {
        'LogicalInstantiateQueries': ['grammar false (.literal 1)', 'grammar true (.literal 0)',
            'ObjectLogicalAxiom.transform 2', 'SyntaxNumerals.exists_numeral hZ 2 w hw',
            'InstantiateTopFormulaOperation.run_iff', 'OriginalTransformExprQuery.constructor_query_iff hZ 5 3'],
        'LogicalInstantiateSyntax': ['same_twenty_twenty_three_queries', 'transformQuery 2 1 3',
            'transformQuery 1 3 4', 'transformQuery 2 3 5', 'ObjectLogicalAxiom.rule25.queries[4]'],
        'LogicalInstantiateAllQueries': ['InsertExistence.exists_insert', 'typed_transform_iff', 'intro_specification4', 'intro_specification6'],
        'LogicalInstantiateNodeSyntax': ['HornExprBounds.variable_bound', 'actual_rule20_arity', 'actual_rule23_arity',
            'actual_rule25_arity', 'actual_rule20_queries', 'actual_rule23_queries', 'actual_rule25_queries',
            'actual_head20', 'actual_head23', 'actual_head25', '(true, LogicalInstantiateSyntax.leftTransform6)',
            '(true, LogicalInstantiateSyntax.rightTransform6)', 'existsMany 4', 'existsMany 6'],
        'LogicalInstantiateNode': ['HornApplicationBounds.existsMany_congr 4', 'HornApplicationBounds.existsMany_congr 6',
            'head4_bounds', 'head6_bounds', 'specification4_normalized_iff', 'specification6_normalized_iff']}
    for rule, count in [(20,3),(23,3),(25,4)]:
        required['LogicalRule'+str(rule)+'Head'] = ['HornExprExistence', 'SyntaxNodeSyntax.constructor', 'existsMany '+str(count), 'head_iff']
    for module, clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:
                raise RuntimeError('Missing exact logical node derivation: ' + module + ': ' + clause)
    def definition(module, name):
        match = re.search(r'(?ms)^def '+name+r'\b.*?(?=^def |^theorem |^end |\Z)', texts[module])
        if not match: raise RuntimeError('Missing definition: ' + module + '.' + name)
        return match.group(0)
    for n in [4,6]:
        bundle = definition('LogicalInstantiateSyntax','bundle'+str(n))
        if re.search(r'formulaCode|SyntaxTermSyntax|instantiated|specification|atBound', bundle):
            raise RuntimeError('Specification smuggled into accepting queries')
        for name in ['queryMatrix','boundedMatrix','body','node']:
            accepting = definition('LogicalInstantiateNodeSyntax',name+str(n))
            if re.search(r'formulaCode|SyntaxTermSyntax|instantiated|specification|normalized', accepting):
                raise RuntimeError('Specification smuggled into accepting node')
    for rule in [20,23,25]:
        numeric = definition('LogicalRule'+str(rule)+'Head','atValues')
        if re.search(r'\bgraph\b|specification|instantiated|formulaCode',numeric):
            raise RuntimeError('Numeric nested head still assumes its graph/specification')
    check = (ROOT / 'CheckStep4.lean').read_text(encoding='utf-8')
    for name in ['logicalTwentyTwentyThreeWholeNormalizedNodeIff universal w z row','logicalTwentyFiveWholeNormalizedNodeIff w z row']:
        if 'ObjectLogicalInstantiate.native_'+name not in check:
            raise RuntimeError('Missing expanded native logical node contract')
    return {'exact_original_arity_heads_ordered_query_flags': True,
            'mode2_literal_and_successor_witnesses_object_eliminated': True,
            'rule25_both_actual_instantiation_parameters_proved': True,
            'all_four_or_six_assignment_bounds_derived_from_actual_heads': True,
            'all_nested_numeric_head_witnesses_object_quantified': True,
            'complete_pure_relational_nodes_only_Omega_empty_premises': True,
            'accepting_AST_independent_of_mathematical_specification': True,
            'shared_original_quotation_Bool_Proof_compiler_and_Con_proved': False}


def check_static_logical_nodes() -> dict:
    # Exact original 0-19, 22, 26 queries, bounded assignments and numerical nested heads.
    directory = ROOT / 'PPAC/Migration/Internal'
    cases = [(0, 3, 7), (1, 1, 3), (2, 2, 3), (3, 2, 4), (4, 1, 4), (5, 2, 4), (6, 2, 6), (7, 0, 2), (8, 1, 3), (9, 1, 5), (10, 1, 5), (11, 2, 4), (12, 2, 3), (13, 2, 3), (14, 2, 3), (15, 2, 3), (16, 3, 7), (17, 2, 6), (18, 2, 4), (19, 2, 4), (22, 1, 3), (26, 1, 2)]
    modules = ['LogicalStaticQueries','LogicalStaticQueryList','LogicalStaticNodeSyntax','LogicalStaticNode','LogicalStaticPatterns','ObjectLogicalStatic']
    modules += ['LogicalRule'+str(rule)+'Head' for rule,count,witnesses in cases]
    texts = {n:strip_comments((directory / (n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for module,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|axiom|unsafe|native_decide)\b',text):
            raise RuntimeError('Forbidden static logical node shortcut: '+module)
    for module,theorem,premises in [('LogicalStaticQueries','query_iff',{'hw','hn','hz'}),
            ('LogicalStaticQueries','bundle_iff',{'hw','hn','hz'}),
            ('LogicalStaticNode','normalized_node_iff',{'hw','hz'})]:
        header=re.search(r'(?ms)^theorem '+theorem+r'\b.*?(?=:=)',texts[module])
        if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header.group(0)))!=premises:
            raise RuntimeError('Static logical node endpoint changed: '+module+'.'+theorem)
        if re.search(r'Promise|Model|Consistent|Classical\.choose|hIH\s*:',header.group(0)):
            raise RuntimeError('Unproved static logical node object premise')
    required={
      'LogicalStaticQueries':['ObjectLogicalAxiom.grammar isTerm (.literal 0)', 'PureSyntaxQueryTyping.formula_iff',
          'LogicalInstantiateQueries.term_iff','List.finRange n','conjoin_iff n'],
      'LogicalStaticQueryList':['if flag then OriginalTransformExprQuery.query expr w env else PureSyntaxExprQuery.query expr w env',
          'finRange_bundle','List.finRange_succ','original_bundle'],
      'LogicalStaticNodeSyntax':['HornExprBounds.environmentBound (n+1)', 'existsMany (n+1)',
          'graph head w env row','LogicalStaticQueries.bundle n isTerm'],
      'LogicalStaticNode':['HornExprBounds.variable_bound','HornApplicationBounds.existsMany_congr (n+1)',
          'LogicalStaticQueries.bundle_iff','hHead (ZFContext.add hZ E)']}
    for rule,count,witnesses in cases:
        name='LogicalRule'+str(rule)+'Head'
        required[name]=['HornExprExistence.exists_value','SyntaxNodeSyntax.constructor','existsMany '+str(witnesses),'head_iff']
        for part in ['arity','queries','head_variables','actual_list_bundle']:
            if 'theorem rule'+str(rule)+'_'+part not in texts['LogicalStaticPatterns']:
                raise RuntimeError('Missing actual static pattern certificate: '+str(rule)+':'+part)
        wrapper='staticLogicalRule'+str(rule)+'WholeNormalizedNodeIff'
        header=re.search(r'(?ms)^def '+wrapper+r'Sentence\b.*?(?=^theorem)',texts['ObjectLogicalStatic'])
        if not header or header.group(0).count('.imp')!=2 or 'omega w' not in header.group(0) or 'empty z' not in header.group(0):
            raise RuntimeError('Concrete whole node has extra assumptions: '+str(rule))
        call=('LogicalStaticNode.normalized_node_iff hZ '+str(count)+' '+str(rule==26).lower()+
              ' (YesMetaZFC.Automation.ObjectLogicalAxiom.rule'+str(rule)+'.head) (@LogicalRule'+str(rule)+
              'Head.normalized) LogicalStaticPatterns.rule'+str(rule)+'_head_variables (@LogicalRule'+str(rule)+'Head.head_iff)')
        if call not in texts['ObjectLogicalStatic']:
            raise RuntimeError('Concrete head certificate was not discharged: '+str(rule))
        if 'ObjectLogicalStatic.native_'+wrapper+' w z row' not in (ROOT/'CheckStep4.lean').read_text(encoding='utf-8'):
            raise RuntimeError('Missing expanded concrete native contract: '+str(rule))
    for module,clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:raise RuntimeError('Missing static logical derivation: '+module+': '+clause)
    def definition(module,name):
        match=re.search(r'(?ms)^def '+name+r'\b.*?(?=^def |^theorem |^end |\Z)',texts[module])
        if not match:raise RuntimeError('Missing static logical definition: '+name)
        return match.group(0)
    for name in ['queryMatrix','boundedMatrix','body','node']:
        if re.search(r'formulaCode|SyntaxTermSyntax|instantiated|types|normalized|numeric',definition('LogicalStaticNodeSyntax',name)):
            raise RuntimeError('Comparison specification inserted into accepting static node')
    if re.search(r'formulaCode|SyntaxTermSyntax|instantiated|types|normalized',definition('LogicalStaticQueries','bundle')):
        raise RuntimeError('Comparison type inserted into accepting query bundle')
    for rule,count,witnesses in cases:
        if re.search(r'\bgraph\b|formulaCode|instantiated|specification',definition('LogicalRule'+str(rule)+'Head','atValues')):
            raise RuntimeError('Uneliminated head oracle in numeric static specification')
    return {'original_rules':[r for r,c,w in cases], 'exact_arities_and_ordered_query_lists_formally_proved':True,
            'actual_Bool_query_list_interpretation_matches_bundle':True,
            'empty_rule7_query_list_and_nullary_nodes_checked':True,
            'all_assignment_bounds_derived_from_original_heads':True,
            'all_nested_head_numeric_witnesses_object_quantified':True,
            'concrete_head_proof_parameters_fully_discharged':True,
            'whole_nodes_only_Omega_empty_object_premises':True,
            'all_internal_assignment_candidates_in_scope':True,
            'remaining_rules21_24_shared_quotation_Proof_compiler_and_Con_proved':False}


def check_abstract_logical_nodes_and_exact_table() -> dict:
    # Actual mode1 logical21/24 and the complete original 27-Shape pure relational table.
    directory=ROOT/'PPAC/Migration/Internal'
    modules=['LogicalAbstractQueries','LogicalAbstractSyntax','LogicalAbstractAllQueries','LogicalAbstractQueryList',
             'LogicalRule21Head','LogicalRule24Head','LogicalAbstractNodeSyntax','LogicalAbstractNode','LogicalAllPatterns',
             'LogicalOriginalQueryBundles','LogicalOriginalNodeSyntax','LogicalOriginalNodes','ObjectLogicalAbstract']
    texts={n:strip_comments((directory/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for module,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|axiom|unsafe|native_decide)\b',text):
            raise RuntimeError('Forbidden abstract logical node shortcut: '+module)
    contracts=[('LogicalAbstractQueries','typed_transform_iff',{'hw','hn','hz','hA','hs','hf'}),
        ('LogicalAbstractAllQueries','bundle21_iff',{'hw','hn','hz'}),
        ('LogicalAbstractAllQueries','bundle24_iff',{'hw','hn','hz'}),
        ('LogicalAbstractNode','normalized_node21_iff',{'hw','hz'}),
        ('LogicalAbstractNode','normalized_node24_iff',{'hw','hz'}),
        ('LogicalAllPatterns','node_iff',{'hw','hz'}),('LogicalOriginalNodes','raw_table_iff',set()),
        ('LogicalOriginalNodes','table_iff',{'hw','hz'})]
    for module,theorem,premises in contracts:
        header=re.search(r'(?ms)^theorem '+theorem+r'\b.*?(?=:=)',texts[module])
        if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header.group(0)))!=premises:
            raise RuntimeError('Original logical endpoint changed: '+module+'.'+theorem)
        if re.search(r'Promise|Model|Consistent|Classical\.choose|hIH\s*:',header.group(0)):
            raise RuntimeError('Undischarged logical table oracle')
    required={
        'LogicalAbstractQueries':['grammar false (.literal 0) (.succ (.var free))','ObjectLogicalAxiom.transform 1 (.literal 0)',
            'SyntaxNumeralSyntax.intro_succ 0 A z hz hA','AbstractTopFormulaOperation.run_iff hZ w A z z z',
            'HornRowFields.five (.literal 1) (.literal 0) (.literal 0)', 'SyntaxTopEnvironmentSyntax.abstractInput'],
        'LogicalAbstractSyntax':['actual_arity21','actual_arity24','actual_queries21','actual_queries24',
            'transformQuery 1 3','transformQuery 2 4','LogicalStaticQueries.query false 0 2','atOneSpecification21','atOneSpecification24'],
        'LogicalAbstractAllQueries':['LogicalAbstractQueries.typed_transform_iff','InsertExistence.exists_insert',
            'intro_atOneSpecification21','intro_atOneSpecification24','intro_specification21','intro_specification24'],
        'LogicalAbstractNode':['HornExprBounds.variable_bound','HornApplicationBounds.existsMany_congr 5',
            'HornApplicationBounds.existsMany_congr 4','LogicalAbstractAllQueries.bundle21_iff','LogicalAbstractAllQueries.bundle24_iff'],
        'LogicalOriginalNodeSyntax':['environmentNat shape.arity','environmentBound shape.arity','graph shape.head',
            'LogicalStaticQueryList.listBundle shape.queries','existsMany shape.arity','ObjectLogicalAxiom.shapes.map'],
        'LogicalOriginalNodes':['raw_table_iff','LogicalAllPatterns.node_iff hZ w z row hw hz'],
        'LogicalAllPatterns':['original_table_exact','original_table_length','patternNodes','patternSpecifications']}
    for r,witnesses in [(21,7),(24,6)]:
        required['LogicalRule'+str(r)+'Head']=['SyntaxNodeSyntax.constructor','existsMany '+str(witnesses),
            'HornExprExistence.exists_value','head_iff']
        if 'original_bundle'+str(r)+'_iff' not in texts['LogicalAbstractQueryList']:
            raise RuntimeError('Missing actual ordered abstract query list bridge')
    for r in [20,23,25]:
        if 'original_bundle'+str(r)+'_iff' not in texts['LogicalOriginalQueryBundles']:
            raise RuntimeError('Missing original mixed query bundle bridge')
    for module,clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:raise RuntimeError('Missing complete logical derivation: '+module+': '+clause)
    for r in range(27):
        if 'theorem rule'+str(r)+'_iff ' not in texts['LogicalOriginalNodes']:
            raise RuntimeError('Missing actual original node transfer: '+str(r))
        if 'have h'+str(r)+' :=' not in texts['LogicalAllPatterns']:
            raise RuntimeError('Missing actual normalized pattern: '+str(r))
    def definition(module,name):
        found=re.search(r'(?ms)^def '+name+r'\b.*?(?=^def |^theorem |^end |\Z)',texts[module])
        if not found:raise RuntimeError('Missing logical acceptance definition: '+module+'.'+name)
        return found.group(0)
    for name in ['matrix','body','node','table']:
        if re.search(r'formulaCode|SyntaxTermSyntax|abstracted|specification|normalized',definition('LogicalOriginalNodeSyntax',name)):
            raise RuntimeError('Comparison specification in exact original accepting table')
    for r in [21,24]:
        for name in ['queryMatrix','boundedMatrix','body','node']:
            if re.search(r'formulaCode|SyntaxTermSyntax|abstracted|specification|normalized',definition('LogicalAbstractNodeSyntax',name+str(r))):
                raise RuntimeError('Comparison specification in accepting abstract node')
        if re.search(r'formulaCode|abstracted|specification',definition('LogicalAbstractSyntax','bundle'+str(r))):
            raise RuntimeError('Type/operation oracle in actual query bundle')
        if re.search(r'\bgraph\b|formulaCode|abstracted|specification',definition('LogicalRule'+str(r)+'Head','atValues')):
            raise RuntimeError('Graph oracle in numeric nested head')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in ['logicalRule21WholeNormalizedNodeIff','logicalRule24WholeNormalizedNodeIff','logicalAllTwentySevenActualTableSpecificationIff']:
        if 'ObjectLogicalAbstract.native_'+name+' w z row' not in check:
            raise RuntimeError('Missing expanded original native logical table contract')
    return {'remaining_original_rules21_24_full_nodes_proved':True,
            'both_source_and_target_successors_object_eliminated':True,
            'real_Num1_and_actual_AbstractFreeTop_used':True,
            'all_five_or_four_assignment_bounds_derived':True,
            'all_thirteen_numeric_head_codes_object_quantified':True,
            'all_twenty_seven_actual_Shape_nodes_object_transferred':True,
            'exact_original_arity_head_ordered_Bool_lists_and_full_table_proved':True,
            'whole_exact_table_only_Omega_empty_premises':True,
            'all_internal_candidate_assignments_in_scope':True,
            'shared_quotation_Bool_Proof_compiler_interpretation_and_Con_proved':False}


def check_base_proof_nodes_and_parameterized_six_table() -> dict:
    # Actual logicalShape and object-formula-parameterized theoryShape, then the exact six-rule local table.
    directory=ROOT/'PPAC/Migration/Internal'
    modules=['LogicalTableRenaming','OriginalLogicalExprQuery','AxiomTestSyntax','OriginalAxiomExprQuery',
        'ProofLogicalSyntax','ProofLogicalQueries','ProofLogicalNodeSyntax','ProofLogicalNode',
        'ProofTheorySyntax','ProofTheoryQueries','ProofTheoryNodeSyntax','ProofTheoryNode',
        'ProofAllQuerySyntax','ProofAllQueryBundles','ProofAllNodeSyntax','ProofAllNodes','ObjectProofBaseNodes']
    texts={n:strip_comments((directory/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for module,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b',text):
            raise RuntimeError('Forbidden base proof node shortcut: '+module)
        if re.search(r'test\s*:\s*(?:Nat\s*→|.*Model|.*Consistent)',text):
            raise RuntimeError('Axiom test must be an object Formula 1, not a host predicate')
    contracts=[('ProofLogicalQueries','query_normalized_iff',{'hw','hn','hz'}),
        ('ProofLogicalNode','normalized_node_iff',{'hw','hz'}),
        ('ProofTheoryQueries','bundle_iff',{'hw','hn','hz'}),
        ('ProofTheoryNode','normalized_node_iff',{'hw','hz'}),
        ('ProofAllNodes','raw_table_iff',set()),('ProofAllNodes','table_iff',{'hw','hz'})]
    for module,theorem,premises in contracts:
        header=re.search(r'(?ms)^theorem '+theorem+r'\b.*?(?=:=)',texts[module])
        if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header.group(0)))!=premises:
            raise RuntimeError('Base proof node endpoint changed: '+module+'.'+theorem)
        if re.search(r'Promise|Model|Consistent|Classical\.choose|hIH\s*:|hTest\s*:',header.group(0)):
            raise RuntimeError('Undischarged base proof node oracle')
        if module in ['ProofTheoryQueries','ProofTheoryNode','ProofAllNodes'] and '(test : Formula 1)' not in header.group(0):
            raise RuntimeError('Theory test object formula parameter was hidden')
    required={
        'LogicalTableRenaming':['listBundle_rename','matrix_rename','body_lift','node_rename','table_rename'],
        'OriginalLogicalExprQuery':['LogicalOriginalNodeSyntax.table','LogicalTableRenaming.table_rename','Derives.exE','HornExprConstructor.constructor_iff'],
        'AxiomTestSyntax':['test : Formula 1','test.rename (fun _ => row)','holds_rename'],
        'OriginalAxiomExprQuery':['test : Formula 1','AxiomTestSyntax.holds test','AxiomTestSyntax.holds_rename','Derives.exE'],
        'ProofLogicalSyntax':['actual_arity','actual_query','actual_query_fields','node 0 [.var 0, .var 2, .var 1]',
            'LogicalAllPatterns.specification','OriginalLogicalExprQuery.query queryExpr'],
        'ProofLogicalQueries':['OriginalLogicalExprQuery.constructor_query_iff hZ 3 0','LogicalOriginalNodes.table_iff',
            'FormulaCodeCongruence.ex_congr','HornExprBounds.variable_bound'],
        'ProofTheorySyntax':['actual_arity','actual_queries','actual_formula','actual_axiom','node 0 [.var 2, .var 1]',
            'OriginalAxiomExprQuery.query test axiomExpr'],
        'ProofTheoryQueries':['LogicalStaticQueries.query_iff hZ false','OriginalAxiomExprQuery.constructor_query_iff test hZ 2 0',
            'HornExprBounds.variable_bound'],
        'ProofAllQuerySyntax':['.projection','ProjectionExprQuery.query','.syntax','PureSyntaxExprQuery.query','.transform',
            'OriginalTransformExprQuery.query','.logical','OriginalLogicalExprQuery.query','.axiom','OriginalAxiomExprQuery.query test'],
        'ProofAllNodeSyntax':['environmentNat shape.arity','environmentBound shape.arity','graph shape.head',
            'ProofAllQuerySyntax.listBundle test shape.queries','existsMany shape.arity','ObjectProofNode.shapes.map',
            'original_arity_order','original_query_counts'],
        'ProofAllNodes':['ProofLogicalNode.normalized_node_iff hZ','ProofTheoryNode.normalized_node_iff test hZ',
            'ProofMPNode.node_iff hZ','ProofForallNode.normalized_node_iff hZ','ProofStrengtheningNode.node_iff hZ','ProofSubstitutionNode.node_iff hZ']}
    for module,clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:raise RuntimeError('Missing exact six-rule local derivation: '+module+': '+clause)
    for kind,arity in [('logical',3),('theory',3),('mp',5),('forall',4),('strengthening',4),('substitution',6)]:
        if 'theorem '+kind+'_bundle_iff' not in texts['ProofAllQueryBundles'] or 'theorem '+kind+'_node_iff' not in texts['ProofAllNodes']:
            raise RuntimeError('Missing actual query/node transfer: '+kind)
        if 'HornApplicationBounds.existsMany_congr '+str(arity) not in texts['ProofAllNodes']:
            raise RuntimeError('Incomplete assignment block: '+kind)
    def definition(module,name):
        found=re.search(r'(?ms)^def '+name+r'\b.*?(?=^def |^theorem |^end |\Z)',texts[module])
        if not found:raise RuntimeError('Missing six-rule acceptance definition: '+module+'.'+name)
        return found.group(0)
    for module,names in [('ProofAllNodeSyntax',['matrix','body','node','table']),
            ('ProofLogicalNodeSyntax',['boundedMatrix','body','node']),('ProofTheoryNodeSyntax',['boundedMatrix','body','node'])]:
        for name in names:
            if re.search(r'formulaCode|SyntaxTermSyntax|abstracted|specification|normalized',definition(module,name)):
                raise RuntimeError('Specification oracle in accepting proof table')
    for module in ['ProofLogicalSyntax','ProofTheorySyntax']:
        if re.search(r'formulaCode|specification|normalized',definition(module,'bundle')):
            raise RuntimeError('Type oracle in accepting base queries')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name,args in [('proofLogicalWholeNodeIff','w z row'),('proofTheoryParameterizedWholeNodeIff','test w z row'),
            ('proofSixRulesParameterizedActualTableSpecificationIff','test w z row')]:
        if 'ObjectProofBaseNodes.native_'+name+' '+args not in check:
            raise RuntimeError('Missing expanded native base proof node contract')
    return {'actual_logical_conclusion_axiom_code_field_swap_proved':True,
            'logical_query_row_witness_and_complete_three_assignments_object_eliminated':True,
            'actual_logical_query_uses_exact_twenty_seven_pattern_table':True,
            'theory_axiom_test_is_explicit_object_Formula1_parameter':True,
            'parameterized_theory_query_and_complete_node_proved':True,
            'all_five_original_query_Kinds_preserved':True,
            'exact_six_original_arities_ordered_queries_and_assignment_blocks_proved':True,
            'all_six_local_nodes_under_parameterized_axiom_formula_transferred':True,
            'whole_local_table_only_Omega_empty_object_premises':True,
            'dedicated_ZF_U_tests_Proof_recursion_shared_Bool_compiler_and_Con_proved':False}


def check_proof_tree_checked_trace_equation() -> dict:
    # Exact original 12 branches and a closed-trace unfolding equation, not yet rank/Bool/Proof soundness.
    directory=ROOT/'PPAC/Migration/Internal'
    modules=['ProofAllTableRenaming','ProofTreeRowLocalSyntax','ProofTreeTraceSyntax','ProofTreeTraceMonotone',
        'ProofTreeTraceExtension','ProofTreeUniversalSyntax','ProofTreeUniversalValue','ProofTreeUniversalClosed',
        'ProofTreeTracedStep','ProofTreeTraceEquation','ProofTreeBranchConstruction','ProofTreeEntrySyntax','ObjectProofTreeTrace']
    texts={n:strip_comments((directory/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for module,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b',text):
            raise RuntimeError('Forbidden proof-tree trace shortcut: '+module)
    for module,theorem,premises in [('ProofTreeUniversalValue','exists_value',set()),
            ('ProofTreeTraceEquation','recursive_iff',set()),('ProofTreeEntrySyntax','root_recursive_iff',set()),
            ('ProofTreeEntrySyntax','node_recursive_iff',set()),('ProofTreeBranchConstruction','intro_branch',{'hw','hn','hm','hl'})]:
        header=re.search(r'(?ms)^theorem '+theorem+r'\b.*?(?=:=)',texts[module])
        if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header.group(0)))!=premises:
            raise RuntimeError('Checked-trace endpoint changed: '+module+'.'+theorem)
        if re.search(r'Promise|Model|Consistent|Classical\.choose|hIH\s*:|hTest\s*:',header.group(0)):
            raise RuntimeError('Undischarged checked-trace oracle')
        if '(test : Formula 1)' not in header.group(0):raise RuntimeError('Object axiom-test parameter hidden')
    required={
      'ProofAllTableRenaming':['query_rename','listBundle_rename','matrix_rename','node_rename','table_rename'],
      'ProofTreeRowLocalSyntax':['PairingProjectionSyntax.step true true','RawCodeFieldSyntax.field',
          'ProofAllNodeSyntax.table test','(OmegaSyntax.empty (Fin.last m)).imp'],
      'ProofTreeTraceSyntax':['HornStepSyntax.step ObjectProofTree.rules','ProofTreeRowLocalSyntax.localCondition',
          'RestrictionSyntax.subset R w','original_rules_count','payload_arities','child_positions'],
      'ProofTreeTraceMonotone':['HornTraceMonotone.step','Derives.eqSubst'],
      'ProofTreeTraceExtension':['InsertExistence.exists_insert','ProofTreeTraceMonotone.step','ProofTreeTraceMonotone.row_subst'],
      'ProofTreeUniversalSyntax':['MinimalPredicates.separated (matrix test)','ProofTreeTraceSyntax.condition test'],
      'ProofTreeUniversalValue':['MinimalInstances.separation_instance','ZFContext.separation hZ','subtrace_included'],
      'ProofTreeUniversalClosed':['ProofTreeUniversalValue.subtrace_included','ProofTreeTraceMonotone.step','ProofTreeTraceExtension.condition'],
      'ProofTreeTracedStep':['HornRuleSyntax.guards rule.guards','HornExprBounds.environmentBound rule.arity',
          'HornApplicationBounds.existsMany_congr rule.arity','ProofTreeUniversalValue.member_iff'],
      'ProofTreeTraceEquation':['ProofTreeUniversalValue.exists_value test hZ w','Derives.exE','at_value_iff',
          'ProofTreeTracedStep.step_iff','ProofTreeRowLocalSyntax.localCondition'],
      'ProofTreeBranchConstruction':['shape_mem','head_variables','HornExprBounds.variable_bound','ObjectProofTree.branch_mem',
          'HornExprRange.range','ProofTreeTraceEquation.recursive_iff'],
      'ProofTreeEntrySyntax':['SyntaxNodeSyntax.constructor 1 0','SyntaxNodeSyntax.constructor 2 1',
          'SetLanguage.args2 code.castSucc conclusion.castSucc','FormulaCodeCongruence.ex_congr']}
    for module,clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:raise RuntimeError('Missing exact checked trace construction: '+module+': '+clause)
    # The accepting trace cannot use its recursion equation or an intended proof-validity assertion.
    for module in ['ProofTreeTraceSyntax','ProofTreeRowLocalSyntax']:
        if re.search(r'ProofTreeTraceEquation|WellFounded|ProofValid|dedicatedProof|Consistent',texts[module]):
            raise RuntimeError('Conclusion used as checked-trace acceptance oracle')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name,args in [('proofTreeFullRecursiveTraceIff','test w r'),('proofTreeRootEntryRecursiveIff','test w code conclusion')]:
        if 'ObjectProofTreeTrace.native_'+name+' '+args not in check:
            raise RuntimeError('Missing expanded native checked trace contract')
    return {'actual_twelve_original_rules_and_payload_arities_children_preserved':True,
            'per_row_actual_tag_and_field_local_check_retained':True,
            'arbitrary_internal_omega_subset_closed_traces':True,
            'Pairing_Union_inserts_real_root_and_preserves_local_checks':True,
            'original_Separation_constructs_all_trace_root_set':True,
            'canonical_trace_set_witness_object_eliminated_in_final_equation':True,
            'all_actual_twelve_branch_bounds_and_composition_proved':True,
            'actual_node_and_root_candidate_conclusion_entry_equations_proved':True,
            'object_test_Formula1_parameter_still_explicit':True,
            'rank_induction_root_closedness_Bool_and_dedicated_Proof_Con_proved':False}


def check_proof_tree_root_closed_fields() -> dict:
    directory=ROOT/'PPAC/Migration/Internal'
    modules=['ProofTreeConstructorFacts', 'ProofTreeZeroGuard', 'ProofTreeTraceQuery', 'ProofTreeBranchHead', 'ProofTreeRootLocal', 'ProofTreeEntryFacts', 'ProofTreeRootSyntax', 'ProofTreeRootForward', 'ProofTreeRootBackward', 'ObjectProofTreeRoot']
    texts={n:strip_comments((directory/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for module,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b',text):
            raise RuntimeError('Forbidden root closed-fields shortcut: '+module)
    required={
      'ProofTreeConstructorFacts':['SyntaxNumerals.exists_numeral','RawCodeFieldAtConstructor.constructor_at','SyntaxNodes.range'],
      'ProofTreeZeroGuard':['InsertLogic.new_member','OmegaUniversal.empty_unique','SyntaxNumerals.exists_numeral','HornRuleSyntax.guard (.var i) (.literal 1)','one_member_iff'],
      'ProofTreeTraceQuery':['ProofTreeTraceSyntax.condition test','HornExprConstructor.constructor_iff','Derives.exE'],
      'ProofTreeBranchHead':['ObjectProofTree.payload s','HornExprConstructor.constructor_iff','ProofTreeTraceQuery.constructor_query_iff'],
      'ProofTreeRootLocal':['PairingProjection.selected_code true true','ProofTreeZeroGuard.one_nonempty','SyntaxForests.range'],
      'ProofTreeRootSyntax':['environmentNat ((shape kind).extra+2)','SyntaxNodeSyntax.constructor ((shape kind).extra+2) (shape kind).tag','empty (env 0)','equal (env 1) conclusion','kinds : List (Fin 6) := [0,1,2,3,4,5]'],
      'ProofTreeRootForward':['SyntaxConstructors.disjoint hZ1 1 2 0 1','ProofTreeConstructorFacts.field_equal','ProofTreeZeroGuard.guard_iff','ProofTreeEntryFacts.node_subst','HornBinderRules.eliminate_many','rule_cases rule hRule','ProofTreeTraceEquation.recursive_iff'],
      'ProofTreeRootBackward':['SyntaxConstructors.exists_constructor hZ 2 1','ProofTreeRootLocal.constructor_one','ProofTreeBranchConstruction.intro_branch','HornBinderRules.eliminate_many','ProofTreeRootSyntax.disjoin_elim','root_iff'],
      'ObjectProofTreeRoot':['TheoryTransport.sentence','ZFReplay.replay','native_proofRootExactClosedFieldsIff']}
    for module,clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:raise RuntimeError('Missing actual root construction: '+module+': '+clause)
    if re.search(r'ProofTreeTraceSyntax|ProofTreeTracedStep|HornExprBounds|graph |HornRuleSyntax',texts['ProofTreeRootSyntax']):
        raise RuntimeError('Closed payload specification contains a checker oracle')
    header=re.search(r'(?ms)^theorem root_iff\b.*?(?=:=)',texts['ProofTreeRootBackward'])
    if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header.group(0)))!={'hw'}:
        raise RuntimeError('Root endpoint must have only Omega object premise')
    if '(test : Formula 1)' not in header.group(0) or re.search(r'Promise|Model|Consistent|hIH\s*:|hTest\s*:',header.group(0)):
        raise RuntimeError('Root endpoint has a hidden test or validity premise')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    if 'ObjectProofTreeRoot.native_proofRootExactClosedFieldsIff test w code conclusion' not in check:
        raise RuntimeError('Missing expanded native root closed-fields contract')
    return {'actual_literal_one_strict_guard_iff_internal_empty':True,
            'all_twelve_original_branches_root_node_tag_separation':True,
            'all_six_payload_arities_object_quantified':True,
            'root_free_zero_and_actual_candidate_conclusion_fields':True,
            'backward_constructs_actual_root_row_and_trace':True,
            'final_root_iff_only_Omega_object_premise':True,
            'object_test_Formula1_parameter_explicit':True,
            'rank_Bool_dedicated_Proof_compiler_and_Con_proved':False}


def check_proof_tree_six_node_equation() -> dict:
    directory=ROOT/'PPAC/Migration/Internal'
    modules=['ProofTreeNodeFieldLocal', 'ProofTreeNodeTag', 'ProofTreeChildren', 'ProofTreeNodeSyntax', 'ProofTreeNodeForward', 'ProofTreeNodeBackward', 'ObjectProofTreeNode']
    texts={n:strip_comments((directory/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for module,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b',text):
            raise RuntimeError('Forbidden node equation shortcut: '+module)
    required={
      'ProofTreeNodeFieldLocal':['RawCodeFieldAtConstructor.constructor_at','SyntaxNumerals.exists_numeral','ProofAllTableRenaming.table_rename','Derives.eqSubst'],
      'ProofTreeNodeTag':['PairingProjection.selected_code true true','PairingProjection.functional_point','constructor_zero_tag','ProofTreeNodeFieldLocal.atZero_iff','local_at_zero'],
      'ProofTreeChildren':['ProofTreeEntrySyntax.node test w (env i)','ProofTreeTraceQuery.constructor_query_iff','is.map (fun i => .node (.literal 0) [.var i])','FormulaCodeCongruence.conj_congr'],
      'ProofTreeNodeSyntax':['environmentNat ((shape kind).extra+2)','SyntaxNodeSyntax.constructor ((shape kind).extra+2) (shape kind).tag','ProofTreeChildren.children test (shape kind).children','ProofAllNodeSyntax.table test w code','ProofTreeRootSyntax.kinds.map','SyntaxConstructors.child_member'],
      'ProofTreeNodeForward':['SyntaxConstructors.disjoint hZ1 2 1 1 0','ProofTreeConstructorFacts.field_equal','ProofTreeChildren.children_iff','HornBinderRules.eliminate_many','ProofTreeRootForward.rule_cases rule hRule','ProofTreeNodeTag.local_iff','ProofTreeTraceEquation.recursive_iff'],
      'ProofTreeNodeBackward':['SyntaxConstructors.exists_constructor hZ 1 0','ProofTreeChildren.children_iff','ProofTreeBranchConstruction.intro_branch','HornBinderRules.eliminate_many','ProofTreeRootSyntax.disjoin_elim','ProofTreeRootBackward.root_iff','node_iff'],
      'ObjectProofTreeNode':['TheoryTransport.sentence','ZFReplay.replay','native_proofNodeExactSixCasesIff','native_proofRootExactNodeSixCasesIff']}
    for module,clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:raise RuntimeError('Missing actual node construction: '+module+': '+clause)
    if re.search(r'ProofTreeTraceSyntax|ProofTreeTracedStep|HornExprBounds|graph |HornRuleSyntax',texts['ProofTreeNodeSyntax']):
        raise RuntimeError('Independent node specification contains an acceptance oracle')
    for theorem in ['node_iff','root_iff']:
        header=re.search(r'(?ms)^theorem '+theorem+r'\b.*?(?=:=)',texts['ProofTreeNodeBackward'])
        if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header.group(0)))!={'hw'}:
            raise RuntimeError('Node/root endpoint must have only Omega object premise')
        if '(test : Formula 1)' not in header.group(0) or re.search(r'Promise|Model|Consistent|hIH\s*:|hTest\s*:',header.group(0)):
            raise RuntimeError('Node/root endpoint has hidden validity premise')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name,args in [('proofNodeExactSixCasesIff','test w code'),('proofRootExactNodeSixCasesIff','test w code conclusion')]:
        if 'ObjectProofTreeNode.native_'+name+' '+args not in check:
            raise RuntimeError('Missing expanded native node/root contract')
    return {'actual_zero_tag_and_field_zero_witnesses_object_eliminated':True,
            'local_condition_iff_exact_six_kind_table_at_actual_payload':True,
            'all_twelve_original_branch_disjunction_eliminated':True,
            'all_six_actual_children_lists_and_payload_arities_preserved':True,
            'node_six_case_and_refined_root_equations_only_Omega_premise':True,
            'all_internal_payload_fields_strictly_below_parent_code':True,
            'dedicated_test_internal_rank_induction_Proof_Bool_compiler_and_Con_proved':False}


def check_proof_tree_internal_induction() -> dict:
    directory=ROOT/'PPAC/Migration/Internal'
    modules=['ProofTreeInductionSyntax', 'ProofTreeInductionChildren', 'ProofTreeInductionStep', 'ProofTreeInduction', 'ObjectProofTreeInduction']
    texts={n:strip_comments((directory/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for module,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|induction code\b',text):
            raise RuntimeError('Forbidden internal proof induction shortcut: '+module)
    required={
      'ProofTreeInductionSyntax':['(P : Formula 2)','P.rename (SetLanguage.args2 w code)','ProofTreeRootSyntax.kinds.map','children P (shape kind).children','closure','Formula.mem (Fin.last m) w.castSucc','Formula.mem (Fin.last m) code.castSucc'],
      'ProofTreeInductionChildren':['Derives.allE child hi','ProofTreeNodeSyntax.payload_field_below','transfer_children'],
      'ProofTreeInductionStep':['HornBinderRules.eliminate_many','ProofTreeRootSyntax.disjoin_elim','ProofTreeNodeBackward.node_iff','ProofTreeInductionChildren.payload_children','ProofTreeConstructorFacts.range','closure_at'],
      'ProofTreeInduction':['SetInduction.all_holds','ZFContext.separation hZ (inductionMatrix test P).neg','base.foundation','ObjectTransitiveCover.source_cover','ProofTreeInductionStep.from_induction','ProofTreeRootBackward.root_iff','reject_node','reject_root'],
      'ObjectProofTreeInduction':['TheoryTransport.sentence','ZFReplay.replay','native_proofTreeInternalInduction','native_proofTreePointInduction']}
    for module,clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:raise RuntimeError('Missing internal proof induction construction: '+module+': '+clause)
    if re.search(r'Prop\b|Model|Consistent|Classical\.choose',texts['ProofTreeInductionSyntax']):
        raise RuntimeError('Internal induction property must be an object formula')
    for theorem in ['progressive','all_correct','at_node']:
        header=re.search(r'(?ms)^theorem '+theorem+r'\b.*?(?=:=)',texts['ProofTreeInduction'])
        if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header.group(0)))!={'hw','hc'}:
            raise RuntimeError('Internal induction endpoint must retain exactly Omega and object closure')
        if '(test : Formula 1)' not in header.group(0) or '(P : Formula 2)' not in header.group(0):
            raise RuntimeError('Missing explicit object-formula scheme indices')
        if re.search(r'Promise|Model|Consistent|hIH\s*:|hTest\s*:',header.group(0)):
            raise RuntimeError('Undischarged external induction or test oracle')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name,args in [('proofTreeInternalInduction','test P w'),('proofTreePointInduction','test P w code')]:
        if 'ObjectProofTreeInduction.native_'+name+' '+args not in check:
            raise RuntimeError('Missing expanded native internal-induction contract')
    return {'actual_six_shape_children_transferred_under_member_IH':True,
            'all_assignment_existentials_object_eliminated':True,
            'original_Foundation_Separation_transitive_cover_discharge_internal_IH':True,
            'all_internal_codes_not_external_Nat_induction':True,
            'property_is_explicit_Formula2_not_host_Prop_predicate':True,
            'final_schema_retains_only_Omega_and_explicit_object_local_closure':True,
            'conditional_root_property_and_negative_rejection_transferred':True,
            'dedicated_Proof_local_closure_Bool_compiler_interpretation_Con_proved':False}


def check_proof_tree_equation_unique() -> dict:
    directory=ROOT/'PPAC/Migration/Internal'
    modules=['ProofTreeEquationSyntax', 'ProofTreeEquationReverseStep', 'ProofTreeEquationUnique', 'ProofTreeEquationCanonical', 'ObjectProofTreeEquation']
    texts={n:strip_comments((directory/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for module,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|induction code\b',text):
            raise RuntimeError('Forbidden recursive-equation uniqueness shortcut: '+module)
    required={
      'ProofTreeEquationSyntax':['def equation','property P w.castSucc (Fin.last m)).iff (normalized test P','closure_from_equation','reverseIH'],
      'ProofTreeEquationReverseStep':['Derives.allE child hi','ProofTreeNodeSyntax.payload_field_below','HornBinderRules.eliminate_many','children_to_nodes','ProofTreeNodeBackward.node_backward','equation_at'],
      'ProofTreeEquationUnique':['SetInduction.all_holds','ZFContext.separation hZ (inductionMatrix test P).neg','base.foundation','ObjectTransitiveCover.source_cover','closure_from_equation','all_iff','two_solutions','ProjectionNodeFields.constructor_field_natural'],
      'ProofTreeEquationCanonical':['def nodeTemplate','ProofTreeEntrySyntax.node test (0 : Fin 2) (Fin.last 1)','property_node','children_node','cases_node','normalized_node','ProofTreeNodeBackward.node_iff'],
      'ObjectProofTreeEquation':['TheoryTransport.sentence','ZFReplay.replay','native_proofTreeEquationAllCodeUnique','native_proofTreeCanonicalNodeEquation']}
    for module,clauses in required.items():
        for clause in clauses:
            if clause not in texts[module]:raise RuntimeError('Missing actual recursive equation proof: '+module+': '+clause)
    equation_def=re.search(r'(?ms)^def equation\b.*?(?=^def|\Z)',texts['ProofTreeEquationSyntax'])
    if not equation_def or 'Formula mem' in equation_def.group(0) or 'Formula.mem' in equation_def.group(0) or '.imp' in equation_def.group(0):
        raise RuntimeError('Candidate equation must quantify all objects without an Omega guard')
    for module,theorem,premises in [('ProofTreeEquationUnique','all_iff',{'hw','he'}),('ProofTreeEquationUnique','point_iff',{'hw','he'}),('ProofTreeEquationCanonical','equation_proved',{'hw'})]:
        header=re.search(r'(?ms)^theorem '+theorem+r'\b.*?(?=:=)',texts[module])
        if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header.group(0)))!=premises:
            raise RuntimeError('Recursive equation endpoint premise drift: '+module+'.'+theorem)
        if '(test : Formula 1)' not in header.group(0) or re.search(r'Promise|Model|Consistent|hIH\s*:|hTest\s*:',header.group(0)):
            raise RuntimeError('Hidden checker correctness or IH premise')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name,args in [('proofTreeEquationAllCodeUnique','test P w'),('proofTreeCanonicalNodeEquation','test w')]:
        if 'ObjectProofTreeEquation.native_'+name+' '+args not in check:
            raise RuntimeError('Missing expanded native equation contract')
    return {'candidate_equation_quantifies_all_object_codes':True,
            'equation_discharges_forward_object_closure':True,
            'reverse_Foundation_Separation_induction_IH_object_discharged':True,
            'all_actual_six_case_assignment_witnesses_object_eliminated':True,
            'node_and_root_equivalence_and_two_solution_uniqueness':True,
            'canonical_Node_Formula2_satisfies_equation_without_equation_premise':True,
            'candidate_property_natural_range_object_proved':True,
            'dedicated_Bool_Proof_equation_compiler_interpretation_Con_proved':False}

# Exact per-declaration footprints: fixed native sentences carry the seven existing certificates.
FIXED_AXIOM_FOOTPRINT_GROUPS = {'std2': ['NativeAxiomCertificateData.Certificate', 'NativeAxiomCertificateData.toZFC', 'NativeAxiomCertificateData.narrow', 'NativeAxiomCertificateData.narrow_toZFC', 'NativeAxiomCertificateData.encode', 'NativeAxiomCertificateData.decode', 'NativeAxiomCertificateData.decode_encode', 'NativeAxiomCertificateData.choice_packet_rejected', 'NativeAxiomCertificateData.TargetCertificate', 'NativeAxiomCertificateData.extraSentence', 'NativeAxiomCertificateData.fixedTag_lt', 'NativeAxiomCertificateData.targetEncode', 'NativeAxiomCertificateData.targetDecode', 'NativeAxiomCertificateData.targetDecode_as_base', 'NativeAxiomCertificateData.target_decode_encode', 'NativeAxiomCertificateData.target_choice_packet_rejected', 'NativeAxiomCertificateData.fixedCertificate', 'NativeAxiomCertificateData.fixedTag_injective', 'NativeAxiomCertificateData.fixed_encode_exact', 'NativeAxiomCertificateData.fixed_decode_exact', 'NativeAxiomCertificateData.fixedTag_ne_choice', 'FixedAxiomPacketSyntax.matrix', 'FixedAxiomPacketSyntax.body', 'FixedAxiomPacketSyntax.leaf', 'FixedAxiomPacketSyntax.existsLeaf', 'FixedAxiomPacketSyntax.varint_small', 'FixedAxiomPacketSyntax.original_leaf_packet_raw', 'FixedAxiomPacketSyntax.packet_polynomial', 'FixedAxiomPacketSyntax.original_leaf_packet_value', 'FixedAxiomPacketFacts.field0', 'FixedAxiomPacketFacts.field1', 'FixedAxiomPacketFacts.field2', 'FixedAxiomPacketFacts.field3', 'FixedAxiomPacketFacts.field4', 'FixedAxiomPacketFacts.field5', 'FixedAxiomPacketFacts.field6', 'FixedAxiomTableSyntax.target_kind_mem', 'FixedAxiomTableSyntax.base_kind_mem', 'ObjectFixedAxiomTest.fixedPacketExistsSentence', 'ObjectFixedAxiomTest.fixedPacketNaturalSentence', 'ObjectFixedAxiomTest.fixedPacketUniqueSentence', 'ObjectFixedAxiomTest.fixedPacketTagsDisjointSentence', 'ObjectFixedAxiomTest.fixedPacketAtValueSentence'], 'std2_inherited': ['NativeAxiomCertificateData.projectSentence', 'NativeAxiomCertificateData.sentence', 'NativeAxiomCertificateData.project_sound', 'NativeAxiomCertificateData.sound', 'NativeAxiomCertificateData.complete', 'NativeAxiomCertificateData.targetSentence', 'NativeAxiomCertificateData.target_sound', 'NativeAxiomCertificateData.target_complete', 'NativeAxiomCertificateData.fixedFormula', 'NativeAxiomCertificateData.fixed_target_sound', 'NativeAxiomCertificateData.fixed_sentence_exact', 'FixedAxiomTableSyntax.branch', 'FixedAxiomTableSyntax.table', 'FixedAxiomTableSyntax.rowTest', 'FixedAxiomTableSyntax.test', 'FixedAxiomTableFacts.intro_table', 'FixedAxiomTableFacts.rowBody', 'FixedAxiomTableFacts.rowTest_eq', 'FixedAxiomTableExistence.existsTest', 'ObjectFixedAxiomTest.fixedAxiomTableAtPacketSentence', 'ObjectFixedAxiomTest.fixedAxiomRowAtConstructorSentence', 'ObjectFixedAxiomTest.fixedAxiomTestAtOmegaSentence', 'ObjectFixedAxiomTest.fixedAxiomTestAtPacketRowSentence', 'ObjectFixedAxiomTest.fixedAxiomChoicePacketRejectedSentence', 'ObjectFixedAxiomTest.fixedAxiomAcceptedWitnessExistsSentence'], 'empty': ['NativeAxiomCertificateData.fixedTag', 'FixedAxiomPacketSyntax.packet_fold'], 'std3': ['FixedAxiomPacketSyntax.matrix_rename', 'FixedAxiomPacketSyntax.body_lift', 'FixedAxiomPacketSyntax.leaf_rename', 'FixedAxiomPacketSyntax.existsLeaf_rename', 'FixedAxiomPacketSyntax.intro_leaf', 'FixedAxiomPacketSyntax.intro_exists', 'FixedAxiomPacketArithmetic.mul_inputs', 'FixedAxiomPacketArithmetic.add_inputs', 'FixedAxiomPacketArithmetic.base_nonempty', 'FixedAxiomPacketFacts.matrix_natural', 'FixedAxiomPacketFacts.matrix_range', 'FixedAxiomPacketFacts.matrix_unique', 'FixedAxiomPacketFacts.matrix_tag_equal', 'FixedAxiomPacketExistence.exists_packet', 'FixedAxiomPacketUnique.unique_at_matrix', 'FixedAxiomPacketUnique.unique', 'FixedAxiomPacketUnique.range', 'FixedAxiomPacketUnique.reject_at_matrix', 'FixedAxiomPacketUnique.disjoint', 'FixedAxiomPacketUnique.output_subst', 'FixedAxiomPacketUnique.at_value', 'ObjectFixedAxiomTest.source_fixedPacketExists', 'ObjectFixedAxiomTest.fixedPacketExists_kernel_certificate', 'ObjectFixedAxiomTest.source_fixedPacketNatural', 'ObjectFixedAxiomTest.fixedPacketNatural_kernel_certificate', 'ObjectFixedAxiomTest.source_fixedPacketUnique', 'ObjectFixedAxiomTest.fixedPacketUnique_kernel_certificate', 'ObjectFixedAxiomTest.source_fixedPacketTagsDisjoint', 'ObjectFixedAxiomTest.fixedPacketTagsDisjoint_kernel_certificate', 'ObjectFixedAxiomTest.source_fixedPacketAtValue', 'ObjectFixedAxiomTest.fixedPacketAtValue_kernel_certificate'], 'propext': ['FixedAxiomTableSyntax.kinds', 'FixedAxiomTableSyntax.fixed_counts'], 'std3_inherited': ['FixedAxiomTableSyntax.branch_rename', 'FixedAxiomTableSyntax.table_rename', 'FixedAxiomTableSyntax.rowTest_rename', 'FixedAxiomTableSyntax.test_at', 'FixedAxiomTableFacts.table_at', 'FixedAxiomTableFacts.table_inputs', 'FixedAxiomTableFacts.intro_row', 'FixedAxiomTableFacts.row_at', 'FixedAxiomTableFacts.row_omega_subst', 'FixedAxiomTableFacts.test_iff_row', 'FixedAxiomTableFacts.at_packet_row', 'FixedAxiomTableFacts.reject_choice_row', 'FixedAxiomTableExistence.existsTest_rename', 'FixedAxiomTableExistence.exists_accepted', 'ObjectFixedAxiomTest.native_fixedPacketExists', 'ObjectFixedAxiomTest.native_fixedPacketNatural', 'ObjectFixedAxiomTest.native_fixedPacketUnique', 'ObjectFixedAxiomTest.native_fixedPacketTagsDisjoint', 'ObjectFixedAxiomTest.native_fixedPacketAtValue', 'ObjectFixedAxiomTest.source_fixedAxiomTableAtPacket', 'ObjectFixedAxiomTest.fixedAxiomTableAtPacket_kernel_certificate', 'ObjectFixedAxiomTest.native_fixedAxiomTableAtPacket', 'ObjectFixedAxiomTest.source_fixedAxiomRowAtConstructor', 'ObjectFixedAxiomTest.fixedAxiomRowAtConstructor_kernel_certificate', 'ObjectFixedAxiomTest.native_fixedAxiomRowAtConstructor', 'ObjectFixedAxiomTest.source_fixedAxiomTestAtOmega', 'ObjectFixedAxiomTest.fixedAxiomTestAtOmega_kernel_certificate', 'ObjectFixedAxiomTest.native_fixedAxiomTestAtOmega', 'ObjectFixedAxiomTest.source_fixedAxiomTestAtPacketRow', 'ObjectFixedAxiomTest.fixedAxiomTestAtPacketRow_kernel_certificate', 'ObjectFixedAxiomTest.native_fixedAxiomTestAtPacketRow', 'ObjectFixedAxiomTest.source_fixedAxiomChoicePacketRejected', 'ObjectFixedAxiomTest.fixedAxiomChoicePacketRejected_kernel_certificate', 'ObjectFixedAxiomTest.native_fixedAxiomChoicePacketRejected', 'ObjectFixedAxiomTest.source_fixedAxiomAcceptedWitnessExists', 'ObjectFixedAxiomTest.fixedAxiomAcceptedWitnessExists_kernel_certificate', 'ObjectFixedAxiomTest.native_fixedAxiomAcceptedWitnessExists']}

def fixed_axiom_expected_footprints(inherited: set[str]) -> dict[str, set[str]]:
    basis={"empty":set(), "propext":{"propext"}, "std2":{"propext","Quot.sound"}, "std3":{"propext","Classical.choice","Quot.sound"}}
    result={}
    for group,names in FIXED_AXIOM_FOOTPRINT_GROUPS.items():
        expected=basis[group.removesuffix("_inherited")] | (inherited if group.endswith("_inherited") else set())
        for name in names:
            full="PPAC.Migration.Internal."+name
            if full in result: raise RuntimeError("Duplicate fixed axiom footprint")
            result[full]=expected
    return result

def check_fixed_axiom_partial_test() -> dict:
    modules=['NativeAxiomCertificateData', 'FixedAxiomPacketSyntax', 'FixedAxiomPacketArithmetic', 'FixedAxiomPacketFacts', 'FixedAxiomPacketExistence', 'FixedAxiomPacketUnique', 'FixedAxiomTableSyntax', 'FixedAxiomTableFacts', 'FixedAxiomTableExistence', 'ObjectFixedAxiomTest']
    texts={n:strip_comments((ROOT/'PPAC/Migration/Internal'/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for name,body in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b',body):
            raise RuntimeError('Forbidden fixed-axiom proof shortcut: '+name)
    required={
      'NativeAxiomCertificateData':['inductive Certificate','Project.UnarySchema','Project.BinarySchema','| .choice => none','target_choice_packet_rejected','fixed_encode_exact','fixed_decode_exact','fixedTag_ne_choice'],
      'FixedAxiomPacketSyntax':['numeral 256','packet_fold','original_leaf_packet_value','packet_polynomial'],
      'FixedAxiomPacketFacts':['matrix_tag_equal','NaturalMultiplicationOrderLaws.left_cancel','NaturalDifference.unique'],
      'FixedAxiomPacketExistence':['SyntaxNumerals.exists_numeral','ZFArithmetic.mul_exists','ZFArithmetic.add_exists','Derives.exE','intro_leaf'],
      'FixedAxiomPacketUnique':['HornBinderRules.eliminate_many 6','SyntaxNumerals.different','theorem disjoint','theorem at_value'],
      'FixedAxiomTableSyntax':['def kinds','[0,1,2,3,4,5,6,7,8,9]','[0,1,2,3,4,5,6]','PureQuotationSyntax.formula (fixedFormula kind)','def test','def rowTest'],
      'FixedAxiomTableFacts':['at_packet_row','OmegaAlgebra.unique','ProofTreeConstructorFacts.field_equal','reject_choice_row','FixedAxiomPacketUnique.disjoint'],
      'FixedAxiomTableExistence':['OriginalTreeQuotationExistence.tree_exists','FixedAxiomPacketExistence.exists_packet','SyntaxConstructors.exists_constructor','Derives.exE','exists_accepted'],
      'ObjectFixedAxiomTest':['TheoryTransport.sentence','ZFReplay.replay','native_fixedAxiomTestAtPacketRow','native_fixedAxiomAcceptedWitnessExists']}
    for module,clauses in required.items():
        if any(clause not in texts[module] for clause in clauses): raise RuntimeError('Fixed axiom endpoint drift: '+module)
    certificate=texts['NativeAxiomCertificateData'].split('inductive Certificate',1)[1].split('def projectSentence',1)[0]
    if re.search(r'\bchoice\b',certificate):raise RuntimeError('Choice added to nativeZF certificate data')
    names={'PPAC.Migration.Internal.'+mod+'.'+n for mod,body in texts.items() for n in re.findall(r'^(?:def|theorem|abbrev|inductive|structure) (\w+)',body,re.M)}
    expected=set(fixed_axiom_expected_footprints(set()))
    if names != expected: raise RuntimeError('Fixed axiom exact footprint coverage drift')
    header=re.search(r'(?ms)^theorem exists_accepted\b.*?(?=:=)',texts['FixedAxiomTableExistence']).group(0)
    if set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header)) != {'hw'}:raise RuntimeError('Hidden accepted witness premise')
    return {'explicit_declarations':len(names),'fixed_native_ZF_axioms':7,'fixed_target_extras':3,
            'fixed_packet_tags':[0,1,2,3,4,5,6,10,11,12],
            'NatPacket_bytes_distinct_from_structural_tree_quotation':True,
            'all_packet_and_formula_and_row_witnesses_object_eliminated':True,
            'fixed_test_iff_actual_formula_at_actual_packet_row':True,
            'choice_tag_7_rejected_by_both_partial_tests':True,
            'full_schema_certificate_data_host_roundtrip_only':True,
            'full_Separation_Collection_internal_test_proved':False,
            'Bool_Proof_compiler_interpretation_Con_proved':False}

def check_all_internal_forall_closure() -> dict:
    modules=['SyntaxUnaryIterationStep', 'SyntaxUnaryIterationSyntax', 'SyntaxUnaryIterationCore', 'SyntaxUnaryIterationLaws', 'SyntaxForallClosureTypingSyntax', 'SyntaxForallClosureTypingHelpers', 'SyntaxForallClosureTypingPoint', 'SyntaxForallClosureTyping', 'SyntaxForallClosureOutput', 'ObjectForallClosure']
    texts={name:strip_comments((ROOT/'PPAC/Migration/Internal'/(name+'.lean')).read_text(encoding='utf-8')) for name in modules}
    for name,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix',text):
            raise RuntimeError('Forbidden internal closure shortcut: '+name)
    required={
      'SyntaxUnaryIterationStep':['SyntaxConstructors.exists_constructor','SyntaxConstructors.unique','relationTotal','relationFunctional'],
      'SyntaxUnaryIterationSyntax':['NaturalEvaluationSyntax.evaluation (SyntaxUnaryIterationStep.matrix tag)','def forallClosure','iterate 9 w a n y'],
      'SyntaxUnaryIterationCore':['NaturalRecursion.source_uniqueness','ObjectNaturalRecursion.instantiate_unique','NaturalEvaluationFiber.at_natural','NaturalEvaluationRange.evaluation_range'],
      'SyntaxUnaryIterationLaws':['NaturalRecursionLaws.evaluation_zero','NaturalEvaluationStep.evaluation_step','successor_backward','all_internal_counts'],
      'SyntaxForallClosureTypingSyntax':['allMany 2 (body','NaturalAdditionSyntax.sum w n b source','formulaCode w y b f','formulaCode w a source f'],
      'SyntaxForallClosureTypingHelpers':['ZFArithmetic.add_commute','ZFArithmetic.add_succ_backward','FormulaCodeKnownLogical.forall_iff','FormulaCodeBranchSyntax.at_successor'],
      'SyntaxForallClosureTypingPoint':['move_successor','SyntaxUnaryIterationCore.exists_iteration','Derives.exE','quantified_at_successor','at_point'],
      'SyntaxForallClosureTyping':['OmegaInduction.induction_on_omega','ZFContext.separation hZ','all_correct','typed_iff'],
      'SyntaxForallClosureOutput':['FormulaCodeProperties.guards','closed_iff','closed_exists_unique','SyntaxUnaryIterationCore.exists_unique'],
      'ObjectForallClosure':['TheoryTransport.sentence','ZFReplay.replay','native_forallClosureClosedExistsUnique','native_forallClosureAllInternalCounts']}
    for name,clauses in required.items():
        if any(clause not in texts[name] for clause in clauses):raise RuntimeError('Internal closure proof drift: '+name)
    for module,name,premises in [('SyntaxForallClosureTyping','typed_iff',{'hw','ha','hf','hn','hb','hs','hy'}),('SyntaxForallClosureOutput','closed_exists_unique',{'hw','hz','ht'}),('SyntaxUnaryIterationLaws','all_internal_counts',{'hw','ha'})]:
        header=re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[module])
        if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header.group(0)))!=premises:raise RuntimeError('Closure endpoint hidden premise: '+name)
        if re.search(r'hIH\s*:|Promise|Consistent|Model',header.group(0)):raise RuntimeError('Closure endpoint retains an external correctness premise')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for clause in ['ObjectForallClosure.native_forallClosureAllInternalCounts w a','ObjectForallClosure.native_forallClosureClosedExistsUnique w a n z','SyntaxUnaryIterationSyntax.fiber 9 w.castSucc a.castSucc (Fin.last m)']:
        if clause not in check:raise RuntimeError('Missing expanded internal-count closure check')
    return {'arbitrary_internal_count_is_object_ALL_not_external_Nat_index':True,
            'actual_recursion_graphs_and_natural_witnesses_object_eliminated':True,
            'zero_and_successor_unary_node_equations_proved':True,
            'remaining_bound_and_output_vary_in_object_ALL2_IH':True,
            'object_omega_induction_discharges_typing_IH':True,
            'exact_type_equivalence_bound_n_plus_b_to_b':True,
            'input_typing_supplies_closed_fiber_natural_guards':True,
            'original_Project_schema_and_Horn_condition_correspondence_proved':False,
            'complete_schema_test_Proof_interpretation_Con_proved':False}

def check_three_schema_index_system() -> dict:
    modules=['SchemaDoubleShiftSyntax', 'SchemaDoubleShiftPoint', 'SchemaDoubleShiftGraph', 'SchemaIndexSyntax', 'SchemaIndexGraphExistence', 'SchemaIndexFacts', 'SchemaIndexScopes', 'SchemaIndexCoded', 'SchemaIndexRenameSystem', 'SchemaIndexTail', 'SchemaIndexHead', 'SchemaIndexSites', 'ObjectSchemaIndex']
    texts={n:strip_comments((ROOT/'PPAC/Migration/Internal'/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for name,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix',text):
            raise RuntimeError('Forbidden schema-index shortcut: '+name)
    required={
      'SchemaDoubleShiftSyntax':['def displacement','successor (Fin.last m) i.castSucc','SyntaxComposeSyntax.composed','existsMany 2'],
      'SchemaDoubleShiftPoint':['composite_value_iff','matrix_edge_iff','edge_target'],
      'SchemaDoubleShiftGraph':['RelationGraph.unique_graph','SyntaxFreeShiftGraph.exists_map','SyntaxComposeGraph.exists_graph','Derives.exE','HornBinderRules.eliminate_many 2'],
      'SchemaIndexSyntax':['def sourceScope','def targetScope','def chain','SyntaxFreeShiftSyntax.shiftMap','SyntaxIndexLiftSyntax.lifted','existsMany 5','existsMany 6','SyntaxMapCodeSyntax.encoded'],
      'SchemaIndexGraphExistence':['theorem separation','theorem collection_premise','theorem collection_image','SchemaDoubleShiftGraph.exists_map','SyntaxIndexLift.exists_lift','Derives.exE'],
      'SchemaIndexFacts':['SyntaxIndexLift.target_map','SyntaxIndexLiftEdges.zero_iff','graph_map','graph_zero_iff'],
      'SchemaIndexScopes':['OmegaSyntax.step_at','HornBinderRules.intro_many 5','SchemaIndexGraphExistence.exists_graph','Derives.exE'],
      'SchemaIndexCoded':['SyntaxMapCodeExistence.exists_code','HornBinderRules.intro_many 6','HornBinderRules.eliminate_many 5'],
      'SchemaIndexRenameSystem':['def law','FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m)','SyntaxRenameOutputSyntax.fiber','SyntaxRenameOutputClassify.fiber_iff_input','SyntaxIdentityCode.exists_code','existsMany 7','HornBinderRules.eliminate_many 6','theorem exists_system'],
      'SchemaIndexTail':['SyntaxIndexLiftEdges.successor_iff','StructuralListTraceOrder.member_member','SyntaxIndexLiftOrder.successor_member','theorem separation_graph','theorem collection_graph'],
      'SchemaIndexHead':['SyntaxIndexLiftEdges.zero_iff','SyntaxIndexLiftEdges.successor_iff','SyntaxNumeralSyntax.eliminate_succ','GraphProperties.single_valued','Derives.eqSubst','theorem one_iff'],
      'SchemaIndexSites':['BoundEmbedding.unaryUnderTwo','BoundEmbedding.binaryUnderOne','BoundEmbedding.binaryUnderTwo','theorem scope_depths'],
      'ObjectSchemaIndex':['TheoryTransport.sentence','ZFReplay.replay','native_schemaIndexSystemExists','native_schemaCollectionTailIff']}
    for name,clauses in required.items():
        missing=[c for c in clauses if c not in texts[name]]
        if missing:raise RuntimeError('Schema-index proof drift: '+name+': '+repr(missing))
    for module,name,premises in [('SchemaIndexScopes','exists_state',{'hw','hn'}),('SchemaIndexCoded','exists_coded_state',{'hw','hn'}),('SchemaIndexRenameSystem','exists_system',{'hw','hn','hz'})]:
        header=re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[module])
        if not header or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',header.group(0)))!=premises:raise RuntimeError('Schema-index hidden premise: '+name)
        if re.search(r'hIH\s*:|Promise|Consistent|Model|Nat\)',header.group(0)):raise RuntimeError('Schema-index endpoint external premise')
    if texts['SchemaIndexSyntax'].split('def matrix ',1)[1].split('def body ',1)[0].count('SyntaxIndexLiftSyntax.lifted')!=5:raise RuntimeError('Three schema binder diagrams changed')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for clause in ['ObjectSchemaIndex.native_schemaIndexSystemExists site w n z','Internal.SchemaIndexRenameSystem.existsSystem site w n z','ObjectSchemaIndex.native_schemaSeparationTailIff','ObjectSchemaIndex.native_schemaCollectionOneIff']:
        if clause not in check:raise RuntimeError('Missing original-kernel schema-index check')
    return {'all_parameter_counts_and_index_values_are_object_slots':True,
            'actual_successor_scopes_n1_n2_n3_n4_constructed':True,
            'separation_one_lift_of_double_shift_proved':True,
            'collection_premise_two_lifts_of_shift_proved':True,
            'collection_image_two_lifts_of_double_shift_proved':True,
            'zero_and_second_head_and_arbitrary_internal_tail_edges_proved':True,
            'complete_graph_and_original_natural_list_code_constructed':True,
            'actual_free_identity_and_bound_codes_object_eliminated':True,
            'all_internal_pure_formula_codes_have_unique_renamed_output':True,
            'final_exists7_system_premises_only_Omega_count_and_empty':True,
            'external_BoundEmbedding_metadata_alone_not_internal_correctness':True,
            'Project_12_to_pure_11_body_translation_proved':False,
            'complete_schema_test_Proof_interpretation_Con_proved':False}


def check_Project_atomic_compile() -> dict:
    modules=['ProjectBoundShiftSyntax', 'ProjectBoundShiftPoint', 'ProjectBoundShiftLaws', 'ProjectBoundShiftExistence', 'ProjectSubsetSyntax', 'ProjectSubsetPoint', 'ProjectSubsetLaws', 'ProjectSubsetAssembly', 'ProjectSubsetFinish', 'ProjectSubsetExistence', 'ProjectAtomicSyntax', 'ProjectAtomicMember', 'ProjectAtomicLaws', 'ProjectAtomicExistence', 'ProjectAtomicData', 'ObjectProjectAtomic']
    texts={n:strip_comments((ROOT/'PPAC/Migration/Internal'/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for name,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix',text):
            raise RuntimeError('Forbidden Project atomic shortcut: '+name)
    required={
      'ProjectBoundShiftSyntax':['SyntaxVariableSyntax.code true w i x','successor j i','SyntaxVariableSyntax.code true w j y','existsMany 2','def uniqueOutput'],
      'ProjectBoundShiftPoint':['SyntaxVariableDecode.index_eq','InsertLogic.unique','SyntaxVariables.unique','SyntaxIndexLiftOrder.successor_member','SyntaxTermSyntax.intro_term'],
      'ProjectBoundShiftLaws':['HornBinderRules.eliminate_many 2','matrix_unique','matrix_type','theorem unique_output'],
      'ProjectBoundShiftExistence':['OmegaSyntax.step_at','SyntaxVariables.exists_code','SyntaxTermSyntax.eliminate_branch','theorem exists_unique','Derives.exE'],
      'ProjectSubsetSyntax':['existsMany 8','successor (env 0) b','shifted w x (env 1)','shifted w y (env 2)','SyntaxVariableSyntax.code true w z (env 3)','zeroScalar w (env 4)','memberCode w (env 4) (env 3) (env 1) (env 5)','memberCode w (env 4) (env 3) (env 2) (env 6)','binaryCode 2 w (env 5) (env 6) (env 7)','singleCode 9 w (env 7) q'],
      'ProjectSubsetAssembly':['def environment','ProjectSubsetSyntax.intro_expanded','theorem assemble'],
      'ProjectSubsetPoint':['Derives.eqSubst','ProjectBoundShiftLaws.unique','SyntaxVariables.unique','SyntaxConstructors.unique','FormulaCodeKnownAtomic.member_iff','FormulaCodeKnownLogical.binary2_iff','FormulaCodeKnownLogical.forall_iff','FormulaCodeBranchSyntax.at_successor'],
      'ProjectSubsetLaws':['HornBinderRules.eliminate_many 8','theorem target_type','theorem unique_output'],
      'ProjectSubsetFinish':['ProjectSubsetAssembly.assemble','SyntaxConstructors.exists_constructor','Derives.exE','def prepared'],
      'ProjectSubsetExistence':['ProjectBoundShiftExistence.exists_output','SyntaxVariables.exists_code','SyntaxConstructors.exists_constructor','ProjectSubsetFinish.finish','theorem exists_unique_typed'],
      'ProjectAtomicSyntax':['if kind.val=0 then 2 else if kind.val=1 then 3 else 11','SyntaxTermSyntax.branch true w b x','SyntaxTermSyntax.branch true w b y','constructor 2 (sourceTag kind)','memberResult w x y q','SyntaxAtomSyntax.equalCode w x y q','ProjectSubsetSyntax.expanded w b z x y q'],
      'ProjectAtomicMember':['ProjectSubsetPoint.inputs3_subst','SyntaxConstructors.exists_constructor','FormulaCodeKnownAtomic.member_iff','SyntaxAtomSyntax.zeroScalar'],
      'ProjectAtomicLaws':['theorem equal_same_code','SyntaxConstructors.unique hZ 2 3','ProjectSubsetLaws.target_type','ProjectAtomicMember.target_type'],
      'ProjectAtomicExistence':['ProjectSubsetExistence.exists_output','theorem exists_unique_typed','def allInputs','allMany 4','theorem all_internal_inputs','HornBinderRules.zf_body 4'],
      'ProjectAtomicData':['ZFC.ProjectEncode.formula','NatPacket.Tree.node (ProjectAtomicSyntax.sourceTag kind)','theorem source_encoding'],
      'ObjectProjectAtomic':['TheoryTransport.sentence','ZFReplay.replay','native_projectAtomicTypedUnique','native_projectAtomicAllInternalInputs']}
    for name,clauses in required.items():
        missing=[c for c in clauses if c not in texts[name]]
        if missing:raise RuntimeError('Project atomic proof drift: '+name+': '+repr(missing))
    for module,name,premises in [('ProjectBoundShiftExistence','exists_unique',{'hw','hx'}),('ProjectSubsetExistence','exists_unique_typed',{'hw','hb','hz','hx','hy'}),('ProjectAtomicExistence','exists_unique_typed',{'hw','hz','hi'}),('ProjectAtomicExistence','all_internal_inputs',{'hw','hz'})]:
        h=re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[module])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0)))!=premises:raise RuntimeError('Project atomic hidden premise: '+module+'.'+name)
        if re.search(r'hIH\s*:|Promise|Consistent|Model|Nat\)',h.group(0)):raise RuntimeError('Project atomic external premise')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for clause in ['ObjectProjectAtomic.native_projectAtomicAllInternalInputs kind w z','Internal.ProjectAtomicExistence.allInputs kind w z','ObjectProjectAtomic.native_projectSubsetTypedUnique','ObjectProjectAtomic.native_projectEqualitySameCode']:
        if clause not in check:raise RuntimeError('Missing native Project atomic check')
    return {'all_bound_indices_scope_sizes_and_candidate_codes_object_quantified':True,
            'actual_bound_term_index_successor_shift_exists_unique':True,
            'exact_successor_scope_type_without_external_standardness':True,
            'Project_membership_two_source_fields_to_actual_three_pure_fields':True,
            'Project_equality_primitive_equal_and_same_code':True,
            'Project_subset_actual_bound_shift_and_member_imp_forall_template':True,
            'all_subset_intermediate_scopes_and_term_and_formula_codes_object_eliminated':True,
            'three_atomic_modes_have_typed_unique_output_for_all_internal_inputs':True,
            'final_ALL4_endpoint_premises_only_Omega_and_empty':True,
            'original_Project_encoder_tag_metadata_checked_separately':True,
            'full_twelve_constructor_body_compiler_and_recursive_IH_discharged':False,
            'NatPacket_byte_packet_to_structural_tree_bridge_for_all_schema_codes':False,
            'complete_schema_test_Proof_interpretation_Con_proved':False}


def check_Project_source_recursive_grammar() -> dict:
    modules=['ProjectSourceAtomSyntax', 'ProjectSourceAtoms', 'ProjectSourceLocalSyntax', 'ProjectSourceLocal', 'ProjectSourceTypeStateSyntax', 'ProjectSourceTypeStateRows', 'ProjectSourceTypeStateExistence', 'ProjectSourceTypeStateMembership', 'ProjectSourceTypeRecursionSyntax', 'ProjectSourceTypeRecursionStep', 'ProjectSourceTypeRecursors', 'ProjectSourceTypeEvaluationSyntax', 'ProjectSourceTypeEvaluationExistence', 'ProjectSourceTypeEvaluationUnique', 'ProjectSourceTypeGraphValues', 'ProjectSourceTypeHistory', 'ProjectSourceTypeJudgmentSyntax', 'ProjectSourceTypeJudgment', 'ProjectSourceTypeRecursiveSyntax', 'ProjectSourceTypeReadTransfer', 'ProjectSourceTypeFieldsTransfer', 'ProjectSourceTypeCaseTransfer', 'ProjectSourceTypeLocalTransfer', 'ProjectSourceTypeRecursive', 'ProjectSourceCodeSyntax', 'ProjectSourceCodeTransport', 'ProjectSourceCodeCarrier', 'ProjectSourceCodeRecursiveSyntax', 'ProjectSourceCodeCongruence', 'ProjectSourceCodeCriterionTransfer', 'ProjectSourceCodeProperties', 'ProjectSourceCodeRecursive', 'ObjectProjectSourceCode']
    texts={n:strip_comments((ROOT/'PPAC/Migration/Internal'/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for name,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option\s+(?:maxHeartbeats|linter\.)',text):raise RuntimeError('Forbidden Project source shortcut: '+name)
        if 'FormulaCodeSyntax.formulaCode' in text or 'ProjectAtomicSyntax.result' in text or 'ProjectAtomicSyntax.compiled' in text:raise RuntimeError('Source validity must be independent of target validity/compilation')
    # Recheck the complete proof re-instantiation, not just selected tokens.
    mapping={'SyntaxFormulaLocalSyntax': 'ProjectSourceLocalSyntax', 'SyntaxFormulaLocal': 'ProjectSourceLocal', 'SyntaxTypeStateSyntax': 'ProjectSourceTypeStateSyntax', 'SyntaxTypeStateRows': 'ProjectSourceTypeStateRows', 'SyntaxTypeStateExistence': 'ProjectSourceTypeStateExistence', 'SyntaxTypeStateMembership': 'ProjectSourceTypeStateMembership', 'SyntaxTypeRecursionSyntax': 'ProjectSourceTypeRecursionSyntax', 'SyntaxTypeRecursionStep': 'ProjectSourceTypeRecursionStep', 'SyntaxTypeRecursors': 'ProjectSourceTypeRecursors', 'SyntaxTypeEvaluationSyntax': 'ProjectSourceTypeEvaluationSyntax', 'SyntaxTypeEvaluationExistence': 'ProjectSourceTypeEvaluationExistence', 'SyntaxTypeEvaluationUnique': 'ProjectSourceTypeEvaluationUnique', 'SyntaxTypeGraphValues': 'ProjectSourceTypeGraphValues', 'SyntaxTypeHistory': 'ProjectSourceTypeHistory', 'SyntaxTypeJudgmentSyntax': 'ProjectSourceTypeJudgmentSyntax', 'SyntaxTypeJudgment': 'ProjectSourceTypeJudgment', 'SyntaxTypeRecursiveSyntax': 'ProjectSourceTypeRecursiveSyntax', 'SyntaxTypeReadTransfer': 'ProjectSourceTypeReadTransfer', 'SyntaxTypeFieldsTransfer': 'ProjectSourceTypeFieldsTransfer', 'SyntaxTypeCaseTransfer': 'ProjectSourceTypeCaseTransfer', 'SyntaxTypeLocalTransfer': 'ProjectSourceTypeLocalTransfer', 'SyntaxTypeRecursive': 'ProjectSourceTypeRecursive', 'FormulaCodeSyntax': 'ProjectSourceCodeSyntax', 'FormulaCodeTransport': 'ProjectSourceCodeTransport', 'FormulaCodeCarrier': 'ProjectSourceCodeCarrier', 'FormulaCodeRecursiveSyntax': 'ProjectSourceCodeRecursiveSyntax', 'FormulaCodeCongruence': 'ProjectSourceCodeCongruence', 'FormulaCodeCriterionTransfer': 'ProjectSourceCodeCriterionTransfer', 'FormulaCodeProperties': 'ProjectSourceCodeProperties', 'FormulaCodeRecursive': 'ProjectSourceCodeRecursive'}
    for src,dst in mapping.items():
        expected=strip_comments((ROOT/'PPAC/Migration/Internal'/(src+'.lean')).read_text(encoding='utf-8'))
        for a,b in sorted(mapping.items(),key=lambda kv:-len(kv[0])):expected=re.sub(r'\b'+a+r'\b',b,expected)
        expected=expected.replace('import PPAC.Migration.Internal.ObjectSyntaxTypeStates','import PPAC.Migration.Internal.ProjectSourceTypeJudgment').replace('import PPAC.Migration.Internal.ObjectSyntaxTypeRecursive','import PPAC.Migration.Internal.ProjectSourceTypeRecursive')
        expected=expected.replace('formulaCode','sourceCode').replace('SyntaxAtomSyntax.atomic','ProjectSourceAtomSyntax.atomic')
        expected=re.sub(r'(?<![.\w])atomic_rename\b','ProjectSourceAtomSyntax.atomic_rename',expected)
        expected=re.sub(r'(?<![.\w])atomic\b','ProjectSourceAtomSyntax.atomic',expected)
        expected=expected.replace('SyntaxAtomCases.context','ProjectSourceAtoms.context').replace('SyntaxAtomCases.range','ProjectSourceAtoms.range')
        if src=='SyntaxFormulaLocalSyntax':expected='import PPAC.Migration.Internal.ProjectSourceAtoms\n'+expected
        if expected.strip()!=texts[dst].strip():raise RuntimeError('Project source object proof re-instantiation drift: '+dst)
    required={
      'ProjectSourceAtomSyntax':['ProjectAtomicSyntax.sourceAt kind','existsMany 2','SyntaxAtomSyntax.nullary false','SyntaxAtomSyntax.nullary true','binaryAtom 0','binaryAtom 1','binaryAtom 2'],
      'ProjectSourceAtoms':['SyntaxNodeInjective.constructor_range','HornBinderRules.eliminate_many 2','theorem context','theorem range'],
      'ProjectSourceLocalSyntax':['ProjectSourceAtomSyntax.atomic','negation w b f h n','binary 0 w b f h n','binary 1 w b f h n','binary 2 w b f h n','binary 3 w b f h n','quantified true w b f h n','quantified false w b f h n'],
      'ProjectSourceTypeStateSyntax':['MinimalPredicates.separated selectionMatrix','def rowBody'],
      'ProjectSourceTypeStateExistence':['MinimalInstances.separation_instance','extensionality_instance'],
      'ProjectSourceTypeRecursors':['ObjectTransfiniteRecursion.source_uniqueness matrix','ProjectSourceTypeRecursionStep.total','ProjectSourceTypeRecursionStep.deterministic','theorem actual_carrier_recursors'],
      'ProjectSourceTypeEvaluationExistence':['InsertExistence.exists_insert','ProjectSourceTypeRecursors.exists_graph','OrdinalSuccessor.ordinal'],
      'ProjectSourceTypeEvaluationUnique':['OrdinalRecursionCompatibility','theorem exists_unique'],
      'ProjectSourceTypeRecursive':['ProjectSourceTypeHistory.from_value','ProjectSourceTypeStateMembership.edge_iff','theorem recursive_iff'],
      'ProjectSourceCodeSyntax':['def sourceCode','carrier w.castSucc.castSucc','typed w.castSucc.castSucc'],
      'ProjectSourceCodeCarrier':['PowerSetLogic.unique','theorem exists_carrier','theorem code_iff_typed'],
      'ProjectSourceCodeRecursive':['def universalLaw','theorem all_law','ProjectSourceCodeCarrier.exists_carrier','theorem recursive_iff'],
      'ObjectProjectSourceCode':['TheoryTransport.sentence','ZFReplay.replay','native_projectSourceAllInternalRecursiveLaw']}
    for name,clauses in required.items():
        missing=[x for x in clauses if x not in texts[name]]
        if missing:raise RuntimeError('Project source proof drift: '+name+': '+repr(missing))
    for module,name,premises in [('ProjectSourceTypeRecursors','all_unique',set()),('ProjectSourceTypeStateExistence','exists_state',set()),('ProjectSourceCodeRecursive','recursive_iff',{'hw'}),('ProjectSourceCodeRecursive','all_law',{'hw'})]:
        h=re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[module])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0)))!=premises:raise RuntimeError('Project source hidden premise: '+module+'.'+name)
        if re.search(r'hIH\s*:|Promise|Consistent|Model|Nat\)',h.group(0)):raise RuntimeError('External Project source correctness premise')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for clause in ['ObjectProjectSourceCode.native_projectSourceAllInternalRecursiveLaw w','Internal.ProjectSourceCodeSyntax.sourceCode w.castSucc.castSucc.castSucc','Internal.ProjectSourceCodeRecursiveSyntax.criterion w.castSucc.castSucc.castSucc']:
        if clause not in check:raise RuntimeError('Missing expanded native Project source universal check')
    return {'independent_source_grammar_has_five_atomic_and_seven_logical_modes':True,
            'Project_atomic_terms_bound_only_no_free_term_branch':True,
            'thirty_object_recursion_proof_modules_reinstantiated_and_compared_exactly':True,
            'actual_Separation_states_and_full_ordinal_recursors_exists_unique':True,
            'actual_internal_evaluation_unique_and_compatible_histories_proved':True,
            'source_code_two_power_carriers_and_evaluation_witnesses_object_existential':True,
            'full_source_recursive_iff_for_all_internal_root_and_scope_candidates':True,
            'final_ALL3_recursive_law_has_only_Omega_premise':True,
            'invalid_natural_and_context_guards_and_omega_independence_proved':True,
            'target_twelve_constructor_body_compiler_and_recursive_IH_discharged':False,
            'actual_NatPacket_schema_packets_and_Horn_test_correspondence_proved':False,
            'complete_schema_test_Proof_interpretation_Con_proved':False}


def check_Project_actual_compiler() -> dict:
    modules=['ProjectCompilerCaseSyntax', 'ProjectCompilerLocalSyntax', 'ProjectCompilerLocal', 'ProjectCompilerStateSyntax', 'ProjectCompilerStateRows', 'ProjectCompilerStateExistence', 'ProjectCompilerStateMembership', 'ProjectCompilerRecursionSyntax', 'ProjectCompilerRecursionStep', 'ProjectCompilerRecursors', 'ProjectCompilerEvaluationSyntax', 'ProjectCompilerEvaluationExistence', 'ProjectCompilerEvaluationUnique', 'ProjectCompilerGraphValues', 'ProjectCompilerHistory', 'ProjectCompilerJudgmentSyntax', 'ProjectCompilerJudgment', 'ProjectCompilerCodeSyntax', 'ProjectCompilerCodeTransport', 'ProjectCompilerCodeCarrier', 'ProjectCompilerCodeProperties', 'ProjectCompilerRootSyntax', 'ProjectCompilerRoot', 'ProjectCompilerIndependent', 'ProjectCompilerCaseIntro', 'ProjectCompilerBase', 'ObjectProjectCompiler']
    texts={n:strip_comments((ROOT/'PPAC/Migration/Internal'/(n+'.lean')).read_text(encoding='utf-8')) for n in modules}
    for name,text in texts.items():
        if re.search(r'Expr\.eval|Classical\.choose|\b(?:sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option\s+(?:maxHeartbeats|linter\.)',text):raise RuntimeError('Forbidden actual compiler shortcut: '+name)
    mapping={'ProjectSourceTypeStateSyntax': 'ProjectCompilerStateSyntax', 'ProjectSourceTypeStateRows': 'ProjectCompilerStateRows', 'ProjectSourceTypeStateExistence': 'ProjectCompilerStateExistence', 'ProjectSourceTypeStateMembership': 'ProjectCompilerStateMembership', 'ProjectSourceTypeRecursionSyntax': 'ProjectCompilerRecursionSyntax', 'ProjectSourceTypeRecursionStep': 'ProjectCompilerRecursionStep', 'ProjectSourceTypeRecursors': 'ProjectCompilerRecursors', 'ProjectSourceTypeEvaluationSyntax': 'ProjectCompilerEvaluationSyntax', 'ProjectSourceTypeEvaluationExistence': 'ProjectCompilerEvaluationExistence', 'ProjectSourceTypeEvaluationUnique': 'ProjectCompilerEvaluationUnique', 'ProjectSourceTypeGraphValues': 'ProjectCompilerGraphValues', 'ProjectSourceTypeHistory': 'ProjectCompilerHistory', 'ProjectSourceTypeJudgmentSyntax': 'ProjectCompilerJudgmentSyntax', 'ProjectSourceTypeJudgment': 'ProjectCompilerJudgment', 'ProjectSourceCodeSyntax': 'ProjectCompilerCodeSyntax', 'ProjectSourceCodeTransport': 'ProjectCompilerCodeTransport', 'ProjectSourceCodeCarrier': 'ProjectCompilerCodeCarrier', 'ProjectSourceCodeProperties': 'ProjectCompilerCodeProperties'}
    for src,dst in mapping.items():
        expected=strip_comments((ROOT/'PPAC/Migration/Internal'/(src+'.lean')).read_text(encoding='utf-8'))
        for a,b in sorted(mapping.items(),key=lambda kv:-len(kv[0])):expected=re.sub(r'\b'+a+r'\b',b,expected)
        expected=expected.replace('ProjectSourceLocalSyntax','ProjectCompilerLocalSyntax').replace('ProjectSourceLocal','ProjectCompilerLocal')
        expected=expected.replace('ProjectSourceTypeRecursive','ProjectCompilerJudgment').replace('ProjectSourceCodeCriterionTransfer','ProjectCompilerCodeCarrier')
        expected=expected.replace('sourceCode','compiled').replace('typed','atCarrier').replace('Typed','AtCarrier').replace('localType','localStep').replace('subst_free','subst_output')
        if expected.strip()!=texts[dst].strip():raise RuntimeError('Compiler recursion re-instantiation drift: '+dst)
    required={
      'ProjectCompilerCaseSyntax':['def relation','def queried','(Formula.mem x n).conj','def advanced','successor (Fin.last m) b.castSucc','ProjectAtomicSyntax.compiled kind','singleCode tag w x n','singleCode tag w y q','binaryCode kind w x y n','binaryCode kind w X Y q','constant false w n q','constant true w n q','atomicCase 0','atomicCase 1','atomicCase 2','singleCase 4 false','singleCase 9 true','singleCase 10 true','binaryCase 0','binaryCase 1','binaryCase 2','binaryCase 3'],
      'ProjectCompilerLocalSyntax':['SyntaxContextReadSyntax.read (0 : Fin 1)','ProjectCompilerCaseSyntax.cases readMatrix (one h)','(empty (Fin.last m)).conj','(Formula.mem n w).conj','SyntaxTermSyntax.contexts w b q','theorem intro_local'],
      'ProjectCompilerStateExistence':['MinimalInstances.separation_instance','extensionality_instance'],
      'ProjectCompilerRecursors':['ObjectTransfiniteRecursion.source_uniqueness matrix','ProjectCompilerRecursionStep.total','ProjectCompilerRecursionStep.deterministic'],
      'ProjectCompilerRoot':['ProjectCompilerHistory.from_value','ProjectCompilerStateMembership.local_of_edge','ProjectCompilerCodeSyntax.eliminate_code','theorem certificate_of_compiled'],
      'ProjectCompilerRootSyntax':['existsMany 4','ProjectCompilerRecursionSyntax.graph','ProjectCompilerStateSyntax.state','ProjectCompilerLocalSyntax.localStep'],
      'ProjectCompilerIndependent':['def allHistories','ProjectCompilerCodeCarrier.exists_carrier','ProjectCompilerEvaluationExistence.exists_value','ProjectCompilerStateMembership.edge_of_local','ProjectCompilerCodeSyntax.intro_code'],
      'ProjectCompilerBase':['theorem constant_compiled','ProjectCompilerCaseIntro.constant_cases','ProjectCompilerCaseIntro.atomic_cases','ProjectCompilerIndependent.compiled','theorem atomic_compiled','ProjectAtomicExistence.exists_unique_typed','theorem atomic_exists_typed'],
      'ObjectProjectCompiler':['TheoryTransport.sentence','ZFReplay.replay','native_compilerConstantsActuallyProduced','native_compilerThreeAtomsTypedOutputExists']}
    for name,clauses in required.items():
        missing=[x for x in clauses if x not in texts[name]]
        if missing:raise RuntimeError('Actual compiler proof drift: '+name+': '+repr(missing))
    for n in ['ProjectCompilerCaseSyntax','ProjectCompilerLocalSyntax']:
        if 'FormulaCodeSyntax.formulaCode' in texts[n] or 'ProjectSourceCodeSyntax.sourceCode' in texts[n]:raise RuntimeError('Actual step must not assume target typing or whole source correctness')
    for mod,name,pre in [('ProjectCompilerRecursors','all_unique',set()),('ProjectCompilerRoot','certificate_of_compiled',{'hw','hc'}),('ProjectCompilerIndependent','compiled',{'hw','hn','hl'}),('ProjectCompilerBase','constant_compiled',{'hw','hb','hc'}),('ProjectCompilerBase','atomic_exists_typed',{'hw','hz','hi'})]:
        h=re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0)))!=pre:raise RuntimeError('Actual compiler hidden premise: '+mod+'.'+name)
        if re.search(r'hIH\s*:|Promise|Consistent|Model',h.group(0)):raise RuntimeError('Unexpected compiler external correctness premise')
    check=(ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for clause in ['ObjectProjectCompiler.native_compilerThreeAtomsTypedOutputExists kind w b z x y n','Internal.ProjectCompilerBase.existsTyped w n b z','ObjectProjectCompiler.native_compilerProducedOutputRootCertificate']:
        if clause not in check:raise RuntimeError('Missing actual compiler native check')
    return {'all_twelve_actual_input_and_output_constructor_cases_defined':True,
            'child_query_uses_actual_history_and_strict_internal_child_bound':True,
            'quantifier_queries_use_actual_independent_successor_scope':True,
            'local_program_does_not_assume_target_FormulaCode_or_whole_source_correctness':True,
            'actual_Separation_states_and_full_ordinal_recursors_constructed_unique':True,
            'produced_output_actual_parent_graph_state_and_edge_certificate_proved':True,
            'both_constants_really_produce_same_input_code':True,
            'three_atomic_modes_really_produce_a_typed_output':True,
            'construction_stage_only_establishes_state_and_evaluation_value_uniqueness':True,
            'generic_history_independent_helper_retains_explicit_object_ALL_premise':True,
            'construction_stage_alone_proves_legal_source_unique_typed_output':False,
            'compiler_recursive_IH_discharged_on_all_twelve_modes':False,
            'actual_NatPacket_Horn_schema_test_Proof_interpretation_Con_proved':False}


def check_Project_compiler_recursive_equation() -> dict:
    modules = ['ProjectCompilerQuerySyntax', 'ProjectCompilerRecursiveSyntax', 'ProjectCompilerQueryTransport', 'ProjectCompilerCaseTransport', 'ProjectCompilerQueryBridge', 'ProjectCompilerLocalBridge', 'ProjectCompilerRecursivePoint', 'ProjectCompilerRecursive', 'ObjectProjectCompilerRecursive']
    required = {'ProjectCompilerQuerySyntax': ['def equivalent', 'OriginalUniversalBlock.allMany 3', 'OriginalUniversalBlock.at_many 3'], 'ProjectCompilerRecursiveSyntax': ['ProjectCompilerCodeSyntax.compiled', 'ProjectCompilerCaseSyntax.cases codeMatrix', '(Formula.mem n w).conj', 'SyntaxTermSyntax.contexts w b q', '(empty (Fin.last m)).conj'], 'ProjectCompilerQueryTransport': ['theorem advanced_iff', 'ProjectSourceCodeCongruence.ex_congr', 'theorem check_iff'], 'ProjectCompilerCaseTransport': ['theorem single_case', 'theorem binary_case', 'theorem all_cases', 'single_case 4 false', 'single_case 9 true', 'single_case 10 true', 'binary_case 0', 'binary_case 1', 'binary_case 2', 'binary_case 3'], 'ProjectCompilerQueryBridge': ['theorem at_member', 'ProjectCompilerJudgment.read_iff', 'ProjectCompilerCodeCarrier.code_iff_atCarrier', 'StructuralListTraceOrder.member_member', 'theorem guarded', 'theorem all_queries', 'HornBinderRules.zf_many 3'], 'ProjectCompilerLocalBridge': ['ProjectCompilerQueryBridge.all_queries', 'ProjectCompilerCaseTransport.all_cases', 'theorem local_iff'], 'ProjectCompilerRecursivePoint': ['ProjectCompilerStateMembership.edge_iff', 'ProjectCompilerLocalBridge.local_iff', 'ProjectCompilerHistory.from_value', 'ProjectCompilerJudgment.at_value'], 'ProjectCompilerRecursive': ['ProjectCompilerEvaluationExistence.at_natural', 'SourcePropositional.by_cases (Formula.mem n w)', 'ProjectCompilerCodeProperties.guards', 'ProjectCompilerCodeCarrier.exists_carrier', 'HornBinderRules.eliminate_many 2', 'theorem recursive_iff', 'def universalLaw', 'theorem all_law'], 'ObjectProjectCompilerRecursive': ['TheoryTransport.sentence', 'ZFReplay.replay', 'native_compilerAllCandidatesRecursiveIff', 'native_compilerAllInternalRecursiveLaw']}
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b', text):
            raise RuntimeError('Compiler recursive equation forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Compiler recursive proof drift: '+mod+': '+clause)
    expected_premises = [
        ('ProjectCompilerQueryBridge','at_member',{'hw','hn','hc','hg','hx'}),
        ('ProjectCompilerQueryBridge','guarded',{'hw','hn','hc','hg'}),
        ('ProjectCompilerQueryBridge','all_queries',{'hw','hn','hc','hg'}),
        ('ProjectCompilerLocalBridge','local_iff',{'hw','hn','hc','hg'}),
        ('ProjectCompilerRecursivePoint','at_value',{'hw','hn','hc','hv'}),
        ('ProjectCompilerRecursive','at_carrier',{'hw','hc'}),
        ('ProjectCompilerRecursive','recursive_iff',{'hw'}),
        ('ProjectCompilerRecursive','all_law',{'hw'})]
    for mod,name,expected in expected_premises:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Compiler recursive hidden premise: '+mod+'.'+name)
        if any(x in h.group(0) for x in ['hIH','Promise','Consistent','FormulaCodeSyntax.formulaCode','ProjectSourceCodeSyntax.sourceCode']):
            raise RuntimeError('Compiler recursive correctness oracle: '+mod+'.'+name)
    if any(x in texts['ProjectCompilerRecursiveSyntax'] for x in ['FormulaCodeSyntax.formulaCode','ProjectSourceCodeSyntax.sourceCode']):
        raise RuntimeError('Compiler criterion assumes semantic correctness')
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in ['compilerActualChildReadIff', 'compilerGuardedChildQueryIff', 'compilerAllInternalChildQueries', 'compilerSuccessorQueryIff', 'compilerScopedChildQueryIff', 'compilerAllTwelveCasesIff', 'compilerActualLocalRecursiveIff', 'compilerActualStateRecursiveIff', 'compilerAtEvaluationRecursiveIff', 'compilerAtCarrierRecursiveIff', 'compilerAllCandidatesRecursiveIff', 'compilerAllInternalRecursiveLaw']:
        if 'Internal.ObjectProjectCompilerRecursive.native_'+name not in check:
            raise RuntimeError('Missing compiler recursive native fixture: '+name)
    return {'actual_child_read_iff_actual_compiled_proved':True,
            'all_internal_guarded_child_queries_and_successor_scopes_transported':True,
            'all_twelve_actual_cases_transported':True,
            'actual_state_evaluation_history_and_carrier_witnesses_object_eliminated':True,
            'only_omega_premise_in_final_all_internal_recursive_equation':True,
            'non_natural_and_invalid_candidates_retained':True,
            'recursive_equation_alone_proves_source_completeness_typing_scalar_uniqueness':False,
            'full_schema_Proof_interpretation_Con_proved':False}


def check_Project_compiler_output_typing() -> dict:
    modules = ['ProjectCompilerTypingSyntax', 'ProjectCompilerQueryTyping', 'ProjectCompilerMatrixTyping', 'ProjectCompilerCaseTyping', 'ProjectCompilerAllTyping', 'ProjectCompilerTypingQueries', 'ProjectCompilerTypingStep', 'ProjectCompilerTyping', 'ObjectProjectCompilerTyping']
    required = {'ProjectCompilerTypingSyntax': ['def goodQueries', 'OriginalUniversalBlock.allMany 3', 'def propertyBody', '(empty (slot 3 2)).imp', 'ProjectCompilerCodeSyntax.compiled', 'formulaCode (old 3 w)', 'def correct', 'def allIH', 'theorem at_correct', 'theorem below_correct'], 'ProjectCompilerQueryTyping': ['theorem advanced_type', 'Derives.exE', 'Derives.exI', 'query_type', 'theorem check_type'], 'ProjectCompilerMatrixTyping': ['FormulaCodeKnownAtomic.nullary_iff', 'FormulaCodeTransport.code_root', 'FormulaCodeKnownLogical.negation_iff', 'FormulaCodeKnownLogical.forall_iff', 'FormulaCodeKnownLogical.exists_iff', 'FormulaCodeKnownLogical.binary0_iff', 'FormulaCodeKnownLogical.binary1_iff', 'FormulaCodeKnownLogical.binary2_iff', 'FormulaCodeKnownLogical.binary3_iff', 'ProjectCompilerQueryTyping.check_type'], 'ProjectCompilerCaseTyping': ['ProjectAtomicLaws.compiled_type', 'HornBinderRules.eliminate_many 2', 'HornBinderRules.eliminate_many 4', 'ProjectCompilerMatrixTyping.single_matrix', 'ProjectCompilerMatrixTyping.binary_matrix'], 'ProjectCompilerAllTyping': ['theorem all_cases', 'constant false', 'constant true', 'atomicCase 0', 'atomicCase 1', 'atomicCase 2', 'singleCase 4 false', 'singleCase 9 true', 'singleCase 10 true', 'binaryCase 0', 'binaryCase 1', 'binaryCase 2', 'binaryCase 3', 'FormulaCodeCaseLogic.disj_imp'], 'ProjectCompilerTypingQueries': ['theorem from_induction', 'below_correct', 'codeMatrix_at', 'at_correct', 'HornBinderRules.under_body 3 hI'], 'ProjectCompilerTypingStep': ['ProjectCompilerRecursive.recursive_iff', 'ProjectCompilerTypingQueries.from_induction', 'ProjectCompilerAllTyping.all_cases', 'OmegaUniversal.empty_unique', 'FormulaCodeTransport.code_free', 'theorem from_induction'], 'ProjectCompilerTyping': ['def inductionMatrix', 'theorem progressive', 'ProjectCompilerTypingStep.from_induction', 'SetInduction.all_holds', 'ZFContext.separation hZ inductionMatrix.neg', '.base.foundation', 'ObjectTransitiveCover.source_cover', 'theorem all_correct', 'theorem output_type', 'theorem reject_untyped'], 'ObjectProjectCompilerTyping': ['TheoryTransport.sentence', 'ZFReplay.replay', 'native_compilerAllInternalOutputsTargetTyped', 'native_compilerActualOutputTargetTyped']}
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b', text):
            raise RuntimeError('Compiler typing forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Compiler typing proof drift: '+mod+': '+clause)
    expected_premises = [
        ('ProjectCompilerTypingQueries','from_induction',{'hz','hI'}),
        ('ProjectCompilerTypingStep','output_from_induction',{'hw','hz','hI','hc'}),
        ('ProjectCompilerTypingStep','from_induction',{'hw','hI'}),
        ('ProjectCompilerTyping','progressive',{'hw'}),
        ('ProjectCompilerTyping','all_correct',{'hw'}),
        ('ProjectCompilerTyping','at_input',{'hw'}),
        ('ProjectCompilerTyping','output_type',{'hw','hz','hc'}),
        ('ProjectCompilerTyping','reject_untyped',{'hw','hz','ht'})]
    for mod,name,expected in expected_premises:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Compiler typing hidden premise: '+mod+'.'+name)
        if any(x in h.group(0) for x in ['Promise','Consistent','ProjectSourceCodeSyntax.sourceCode']):
            raise RuntimeError('Compiler typing unrequested external promise: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in ['compilerChildTypingFromMemberIH', 'compilerTwelveCasesTargetTyped', 'compilerOutputTypedFromMemberIH', 'compilerTypingPropertyStep', 'compilerTypingProgressive', 'compilerAllInternalOutputsTargetTyped', 'compilerInputTypingProperty', 'compilerActualOutputTargetTyped', 'compilerUntypedOutputRejected']:
        if 'Internal.ObjectProjectCompilerTyping.native_'+name not in check:
            raise RuntimeError('Missing compiler typing native fixture: '+name)
    return {'all_twelve_actual_case_outputs_target_typed_under_explicit_object_child_condition':True,
            'actual_successor_scope_and_all_constructor_witnesses_object_eliminated':True,
            'actual_child_condition_derived_from_object_member_IH':True,
            'original_Foundation_Separation_and_transitive_cover_discharge_all_IH':True,
            'all_internal_actual_outputs_target_FormulaCode_without_IH_or_source_promise':True,
            'empty_zero_witnesses_aligned_by_original_extensionality':True,
            'only_omega_premise_in_final_ALL4_typing_law':True,
            'source_completeness_scalar_uniqueness_full_schema_Proof_Con_proved':False}


def check_Project_compiler_source_completeness() -> dict:
    modules = ['ProjectCompilerCompleteSyntax', 'ProjectCompilerCompleteIntro', 'ProjectCompilerCompleteConstructors', 'ProjectCompilerCompleteQuerySyntax', 'ProjectCompilerCompleteQueries', 'ProjectCompilerCompleteFields', 'ProjectCompilerCompleteAtoms', 'ProjectCompilerCompleteCases', 'ProjectCompilerCompleteStep', 'ProjectCompilerComplete', 'ObjectProjectCompilerComplete']
    required = {'ProjectCompilerCompleteSyntax': ['def existsOutput', 'ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)', 'def propertyBody', 'ProjectSourceCodeSyntax.sourceCode (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)', 'def correct', 'def allIH', 'theorem at_correct', 'theorem below_correct'], 'ProjectCompilerCompleteIntro': ['ProjectCompilerRecursive.recursive_iff', 'theorem of_cases', 'Derives.exI z', 'ProjectCompilerCodeProperties.guards', 'theorem check_output_natural'], 'ProjectCompilerCompleteConstructors': ['theorem single_cases', 'theorem binary_cases', 'theorem single_output', 'theorem binary_output', 'SyntaxConstructors.exists_constructor hZ 1', 'SyntaxConstructors.exists_constructor hZ 2', 'ProjectCompilerCaseIntro.single_case', 'ProjectCompilerCaseIntro.binary_case', 'ProjectCompilerCompleteIntro.of_cases'], 'ProjectCompilerCompleteQuerySyntax': ['def someCheck', 'check advance codeMatrix', 'theorem query_of_output', 'theorem intro_advanced', 'Derives.exI B'], 'ProjectCompilerCompleteQueries': ['theorem child_output', 'below_correct', 'theorem ordinary_query', 'theorem source_check_output', 'ProjectSourceCodeSyntax.sourceCode w.castSucc x.castSucc (Fin.last m) f.castSucc', 'intro_advanced', 'intro_someCheck true'], 'ProjectCompilerCompleteFields': ['ProjectCompilerCompleteQueries.source_check_output', 'ProjectCompilerCompleteConstructors.single_output', 'ProjectCompilerCompleteConstructors.binary_output'], 'ProjectCompilerCompleteAtoms': ['ProjectCompilerBase.constant_compiled', 'ProjectCompilerBase.atomic_exists_typed', 'HornBinderRules.eliminate_many 2', 'theorem all_atoms'], 'ProjectCompilerCompleteCases': ['HornBinderRules.eliminate_many 1', 'HornBinderRules.eliminate_many 2', 'singleCase 4 false', 'singleCase 9 true', 'singleCase 10 true', 'binaryCase 0', 'binaryCase 1', 'binaryCase 2', 'binaryCase 3', 'ProjectCompilerCompleteAtoms.all_atoms'], 'ProjectCompilerCompleteStep': ['ProjectSourceCodeRecursive.recursive_iff', 'ProjectCompilerCompleteCases.all_cases', 'theorem from_induction'], 'ProjectCompilerComplete': ['SetInduction.all_holds', 'ZFContext.separation hZ inductionMatrix.neg', '.base.foundation', 'ObjectTransitiveCover.source_cover', 'theorem output_exists_without_zero', '(.conjL (.conjL hw))', 'def allSourceLaw', 'theorem all_source_outputs', 'theorem typed_output_exists', 'ProjectCompilerTyping.output_type'], 'ObjectProjectCompilerComplete': ['TheoryTransport.sentence', 'ZFReplay.replay', 'native_compilerSourceInputActualOutputExists', 'native_compilerAllInternalSourceOutputsExist', 'native_compilerSourceInputActualTypedOutputExists']}
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b', text):
            raise RuntimeError('Compiler completeness forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Compiler completeness proof drift: '+mod+': '+clause)
    expected_premises = [
        ('ProjectCompilerCompleteQueries','child_output',{'hz','hI','hx','hc'}),
        ('ProjectCompilerCompleteQueries','source_check_output',{'hz','hI','hx','hc'}),
        ('ProjectCompilerCompleteStep','output_from_induction',{'hw','hz','hI','hc'}),
        ('ProjectCompilerCompleteStep','from_induction',{'hw','hI'}),
        ('ProjectCompilerComplete','progressive',{'hw'}),
        ('ProjectCompilerComplete','all_correct',{'hw'}),
        ('ProjectCompilerComplete','output_exists_without_zero',{'hw','hc'}),
        ('ProjectCompilerComplete','all_source_outputs',{'hw'}),
        ('ProjectCompilerComplete','typed_output_exists',{'hw','hz','hc'})]
    for mod,name,expected in expected_premises:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Compiler completeness hidden premise: '+mod+'.'+name)
        if any(x in h.group(0) for x in ['Promise','Consistent','hExistence','hCompiled']):
            raise RuntimeError('Compiler completeness output oracle: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in ['compilerSourceAtomsActualOutput', 'compilerSourceChildOutputFromMemberIH', 'compilerSourceOutputFromMemberIH', 'compilerCompletenessPropertyStep', 'compilerCompletenessProgressive', 'compilerAllInternalCompletenessProperty', 'compilerSourceInputActualOutputExists', 'compilerAllInternalSourceOutputsExist', 'compilerSourceInputActualTypedOutputExists']:
        if 'Internal.ObjectProjectCompilerComplete.native_'+name not in check:
            raise RuntimeError('Missing compiler completeness native fixture: '+name)
    return {'all_twelve_source_constructors_obtain_actual_compiler_outputs':True,
            'actual_source_free_scope_is_arbitrary_internal_parameter':True,
            'strict_child_guards_and_actual_quantifier_successor_scopes_preserved':True,
            'all_target_codes_and_source_child_witnesses_object_existentially_constructed_and_eliminated':True,
            'original_Foundation_Separation_and_transitive_cover_discharge_all_completeness_IH':True,
            'empty_zero_exists_in_omega_and_is_discharged_in_final_source_law':True,
            'only_omega_premise_in_final_ALL3_source_to_EX_output_law':True,
            'actual_output_existence_combined_with_independent_global_target_typing':True,
            'scalar_output_uniqueness_full_schema_Proof_Con_proved':False}


def check_Project_compiler_scalar_uniqueness() -> dict:
    modules = ['ProjectCompilerUniqueSyntax', 'ProjectCompilerUniqueTransport', 'ProjectCompilerUniqueMatrixSyntax', 'ProjectCompilerUniqueMatrixHead', 'ProjectCompilerUniqueActualSyntax', 'ProjectCompilerUniquePadding', 'ProjectCompilerUniqueQueries', 'ProjectCompilerUniqueAtoms', 'ProjectCompilerUniqueLogical', 'ProjectCompilerUniqueMatrices', 'ProjectCompilerUniquePairs', 'ProjectCompilerUniqueStep', 'ProjectCompilerUnique', 'ProjectCompilerUniqueFiberSyntax', 'ProjectCompilerUniqueFiber', 'ObjectProjectCompilerUnique']
    required = {'ProjectCompilerUniqueSyntax': ['def propertyBody', 'def functional', 'OriginalUniversalBlock.allMany 3', '(ProjectCompilerCodeSyntax.compiled (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).imp', '(.equal (slot 3 1) (slot 3 2))', 'def allIH', 'theorem unique_at', 'theorem below_functional'], 'ProjectCompilerUniqueTransport': ['Derives.eqSubst', 'theorem atomic_left', 'theorem atomic_right', 'theorem check_input', 'theorem single_input', 'theorem binary_left', 'theorem binary_right', 'theorem cases_zero'], 'ProjectCompilerUniqueMatrixSyntax': ['inductive Mode', 'theorem tag_injective', 'def matrix', 'constant false', 'constant true', 'ProjectAtomicSyntax.compiled 0', 'ProjectAtomicSyntax.compiled 1', 'ProjectAtomicSyntax.compiled 2', 'singleMatrix 4 false', 'singleMatrix 9 true', 'singleMatrix 10 true', 'binaryMatrix 0', 'binaryMatrix 1', 'binaryMatrix 2', 'binaryMatrix 3', 'existsMany 4 (body mode', 'LogicalAllPatterns.disjoin'], 'ProjectCompilerUniqueMatrixHead': ['theorem source_head', 'SyntaxConstructors.disjoint', 'theorem different_modes'], 'ProjectCompilerUniqueActualSyntax': ['def actualCase', 'constant false', 'constant true', 'atomicCase 0', 'atomicCase 1', 'atomicCase 2', 'singleCase 4 false', 'singleCase 9 true', 'singleCase 10 true', 'binaryCase 0', 'binaryCase 1', 'binaryCase 2', 'binaryCase 3'], 'ProjectCompilerUniquePadding': ['theorem intro_uniform', 'HornBinderRules.intro_many 4', 'theorem from_actual_mode', 'HornBinderRules.eliminate_many 2', 'theorem actual_cases_to_choices', 'FormulaCodeCaseLogic.disj_imp h10 h11'], 'ProjectCompilerUniqueQueries': ['below_functional', 'unique_at', 'OmegaUniversal.successor_unique', 'ProjectCompilerCodeTransport.code_bound', 'theorem check_unique'], 'ProjectCompilerUniqueAtoms': ['eq_trans', 'SyntaxNodeInjective.constructor_input_eq', 'ProjectCompilerUniqueTransport.atomic_left', 'ProjectCompilerUniqueTransport.atomic_right', 'ProjectAtomicLaws.compiled_unique'], 'ProjectCompilerUniqueLogical': ['SyntaxNodeInjective.constructor_input_eq', 'ProjectCompilerUniqueQueries.check_unique', 'ProjectCompilerUniqueQueries.query_unique', 'SyntaxConstructors.unique'], 'ProjectCompilerUniqueMatrices': ['theorem same_mode', 'theorem any_modes', 'ProjectCompilerUniqueMatrixHead.different_modes'], 'ProjectCompilerUniquePairs': ['HornBinderRules.eliminate_many 4', 'theorem uniform_unique', 'theorem choices_unique', 'ProofTreeRootSyntax.disjoin_elim', 'ProjectCompilerUniquePadding.actual_cases_to_choices'], 'ProjectCompilerUniqueStep': ['ProjectCompilerRecursive.recursive_iff', 'OmegaUniversal.empty_unique', 'ProjectCompilerUniqueTransport.cases_zero', 'ProjectCompilerUniquePairs.actual_cases_unique', 'theorem from_induction'], 'ProjectCompilerUnique': ['SetInduction.all_holds', 'ZFContext.separation hZ inductionMatrix.neg', '.base.foundation', 'ObjectTransitiveCover.source_cover', 'theorem all_functional', 'theorem unique_outputs'], 'ProjectCompilerUniqueFiberSyntax': ['def uniqueOutput', 'def typedFiber', 'ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)', 'FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) b.castSucc z.castSucc', 'def allSourceTypedUniqueLaw', 'OriginalUniversalBlock.allMany 4'], 'ProjectCompilerUniqueFiber': ['ProjectCompilerUnique.unique_outputs', 'ProjectCompilerComplete.typed_output_exists', 'theorem typed_unique_exists', 'theorem all_source_typed_unique'], 'ObjectProjectCompilerUnique': ['TheoryTransport.sentence', 'ZFReplay.replay', 'native_compilerAllInternalOutputsScalarUnique', 'native_compilerAllInternalSourceTypedUniqueOutputExists']}
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b', text):
            raise RuntimeError('Compiler scalar uniqueness forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Compiler scalar uniqueness proof drift: '+mod+': '+clause)
    expected_premises = [
        ('ProjectCompilerUniqueQueries','query_unique',{'hI','hq','hr'}),
        ('ProjectCompilerUniqueQueries','advanced_unique',{'hI','hq','hr'}),
        ('ProjectCompilerUniqueStep','outputs_from_induction',{'hw','hI','hq','hr'}),
        ('ProjectCompilerUniqueStep','from_induction',{'hw','hI'}),
        ('ProjectCompilerUnique','progressive',{'hw'}),
        ('ProjectCompilerUnique','all_functional',{'hw'}),
        ('ProjectCompilerUnique','unique_outputs',{'hw','hq','hr'}),
        ('ProjectCompilerUniqueFiber','typed_unique_exists',{'hw','hz','hc'}),
        ('ProjectCompilerUniqueFiber','all_source_typed_unique',{'hw'})]
    for mod,name,expected in expected_premises:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Compiler scalar uniqueness hidden premise: '+mod+'.'+name)
        if any(x in h.group(0) for x in ['Promise','Consistent','hUnique','hFunctionality']):
            raise RuntimeError('Compiler scalar uniqueness oracle: '+mod+'.'+name)
    names = ['falseCase','trueCase','memberCase','equalCase','subsetCase','negCase','conjCase','disjCase','impCase','iffCase','forallCase','existsCase']
    actual = re.search(r'def modes : List Mode := \[([^\]]+)\]', texts['ProjectCompilerUniqueMatrixSyntax'])
    if not actual or re.findall(r'\.(\w+)',actual.group(1)) != names:
        raise RuntimeError('Compiler finite template coverage drift')
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in ['compilerGuardedChildScalarUnique', 'compilerSuccessorChildScalarUnique', 'compilerAllCasesScalarUnique', 'compilerOutputsUniqueFromMemberIH', 'compilerScalarFunctionalityProgressive', 'compilerAllInternalOutputsScalarUnique', 'compilerActualOutputsScalarUnique', 'compilerActualUniqueOutputFiber', 'compilerSourceActualTypedUniqueOutputExists', 'compilerAllInternalSourceTypedUniqueOutputExists']:
        if 'Internal.ObjectProjectCompilerUnique.native_'+name not in check:
            raise RuntimeError('Missing compiler scalar uniqueness native fixture: '+name)
    return {'all_twelve_actual_matrices_scalar_unique_under_object_member_IH':True,
            'different_source_constructor_tags_rejected_in_original_kernel':True,
            'source_field_equality_recovered_by_original_constructor_injectivity':True,
            'independent_successor_scopes_and_empty_zeros_aligned_by_object_uniqueness':True,
            'both_internal_EX4_field_blocks_and_all_actual_cases_eliminated':True,
            'original_Foundation_Separation_transitive_cover_discharge_scalar_IH':True,
            'all_internal_actual_inputs_scalar_functional_with_only_omega':True,
            'every_legal_source_has_actual_target_typed_output_unique_among_all_outputs':True,
            'finite_modes_are_external_proof_templates_not_internal_code_restrictions':True,
            'scalar_uniqueness_stage_alone_proves_source_validity_converse':False,
            'original_byte_bridge_full_schema_Proof_Con_proved':False}


def check_Project_compiler_source_validity() -> dict:
    modules = ['ProjectCompilerSourceSyntax', 'ProjectCompilerSourceQueries', 'ProjectCompilerSourceMatrix', 'ProjectCompilerSourceCases', 'ProjectCompilerSourceIH', 'ProjectCompilerSourceStep', 'ProjectCompilerSourceValid', 'ProjectCompilerSourceAcceptedSyntax', 'ProjectCompilerSourceAccepted', 'ObjectProjectCompilerSourceValid']
    required = {'ProjectCompilerSourceSyntax': ['def queryBody', 'sourceCode (old 3 w) (slot 3 0) (slot 3 1) (old 3 f)', 'def propertyBody', '(Formula.mem (slot 3 2) (old 3 w)).imp', 'sourceCode (old 3 w) (old 3 n) (slot 3 0) (slot 3 2)', 'def correct', 'def allIH', 'theorem at_correct'], 'ProjectCompilerSourceQueries': ['theorem advanced_source', 'theorem check_source', 'theorem check_child_member', 'sourceCode_rename', 'Derives.exE', 'Derives.exI'], 'ProjectCompilerSourceMatrix': ['ProjectSourceAtomSyntax.intro_binary', 'ProjectSourceCodeRecursiveSyntax.intro_single', 'ProjectSourceCodeRecursiveSyntax.intro_binary', 'ProjectCompilerSourceQueries.check_source', 'ProjectCompilerSourceQueries.check_child_member', 'theorem mode_source_cases', 'constant_source false', 'constant_source true', 'atomic_source 0', 'atomic_source 1', 'atomic_source 2', 'single_source 4 false', 'single_source 9 true', 'single_source 10 true', 'binary_source 0', 'binary_source 1', 'binary_source 2', 'binary_source 3'], 'ProjectCompilerSourceCases': ['HornBinderRules.eliminate_many 4', 'ProjectCompilerSourceMatrix.mode_source_cases', 'ProofTreeRootSyntax.disjoin_elim', 'ProjectCompilerUniquePadding.actual_cases_to_choices'], 'ProjectCompilerSourceIH': ['theorem supply_queries', 'below_correct', 'codeMatrix_at', 'at_correct', 'HornBinderRules.under_body 3 hf'], 'ProjectCompilerSourceStep': ['ProjectCompilerRecursive.recursive_iff', 'ProjectCompilerSourceIH.supply_queries', 'ProjectCompilerSourceCases.actual_source_cases', 'ProjectSourceCodeRecursive.recursive_iff', 'theorem from_induction'], 'ProjectCompilerSourceValid': ['SetInduction.all_holds', 'ZFContext.separation hZ inductionMatrix.neg', '.base.foundation', 'ObjectTransitiveCover.source_cover', 'theorem all_correct', 'theorem valid_input'], 'ProjectCompilerSourceAcceptedSyntax': ['def accepted', '(Formula.mem f w).conj (ProjectCompilerCompleteSyntax.existsOutput w n b)', 'def typedAccepted', '(Formula.mem f w).conj (ProjectCompilerUniqueFiberSyntax.typedFiber w n b z)', 'def allAcceptanceLaw', 'def allTypedAcceptanceLaw', 'OriginalUniversalBlock.allMany 3', 'OriginalUniversalBlock.allMany 4'], 'ProjectCompilerSourceAccepted': ['ProjectSourceCodeProperties.guards', 'ProjectCompilerComplete.output_exists_without_zero', 'ProjectCompilerSourceValid.valid_input', 'ProjectCompilerUniqueFiber.typed_unique_exists', 'theorem all_source_iff_exists', 'theorem all_source_iff_typed_fiber', 'OmegaStructureAlgebra.zero_member', 'theorem reject_invalid_source'], 'ObjectProjectCompilerSourceValid': ['TheoryTransport.sentence', 'ZFReplay.replay', 'native_compilerAllInternalActualInputsValid', 'native_compilerAllInternalSourceAcceptanceIff', 'native_compilerAllInternalSourceTypedUniqueAcceptanceIff']}
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b', text):
            raise RuntimeError('Compiler source validity forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Compiler source validity proof drift: '+mod+': '+clause)
    expected_premises = [
        ('ProjectCompilerSourceIH','supply_queries',{'hf','hI'}),
        ('ProjectCompilerSourceStep','input_from_induction',{'hw','hf','hI','hc'}),
        ('ProjectCompilerSourceStep','from_induction',{'hw','hI'}),
        ('ProjectCompilerSourceValid','progressive',{'hw'}),
        ('ProjectCompilerSourceValid','all_correct',{'hw'}),
        ('ProjectCompilerSourceValid','valid_input',{'hw','hf','hc'}),
        ('ProjectCompilerSourceAccepted','source_iff_exists',{'hw'}),
        ('ProjectCompilerSourceAccepted','source_iff_typed_fiber',{'hw','hz'}),
        ('ProjectCompilerSourceAccepted','all_source_iff_exists',{'hw'}),
        ('ProjectCompilerSourceAccepted','all_source_iff_typed_fiber',{'hw'}),
        ('ProjectCompilerSourceAccepted','reject_invalid_source',{'hw','hf','hs'})]
    for mod,name,expected in expected_premises:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Compiler source validity hidden premise: '+mod+'.'+name)
        if any(x in h.group(0) for x in ['Promise','Consistent','hSourceValid','hAccept']):
            raise RuntimeError('Compiler source validity oracle: '+mod+'.'+name)
    if 'FormulaCodeSyntax.formulaCode' in texts['ProjectCompilerSourceMatrix']:
        raise RuntimeError('Source matrix validity must not be inferred from target typing')
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in ['compilerSourceChildValidityFromMemberIH', 'compilerActualCasesRecoverSourceGrammar', 'compilerInputValidFromMemberIH', 'compilerSourceValidityProgressive', 'compilerAllInternalActualInputsValid', 'compilerActualInputValid', 'compilerSourceAcceptanceIff', 'compilerSourceTypedUniqueAcceptanceIff', 'compilerAllInternalSourceAcceptanceIff', 'compilerAllInternalSourceTypedUniqueAcceptanceIff', 'compilerClosedSourceTypedUniqueAcceptanceIff', 'compilerInvalidSourceRejected']:
        if 'Internal.ObjectProjectCompilerSourceValid.native_'+name not in check:
            raise RuntimeError('Missing compiler source-validity native fixture: '+name)
    return {'all_twelve_actual_cases_recover_independent_source_grammar':True,
            'source_child_input_root_not_target_output_is_validated':True,
            'actual_successor_scope_and_strict_child_guard_preserved':True,
            'original_Foundation_Separation_transitive_cover_discharge_source_validation_IH':True,
            'actual_Compiled_implies_SourceCode_for_any_internal_natural_source_context':True,
            'exact_source_acceptance_iff_context_natural_and_actual_output_exists':True,
            'exact_source_acceptance_iff_context_natural_and_actual_typed_unique_fiber':True,
            'invalid_internal_context_candidates_kept_and_rejected_by_explicit_right_guard':True,
            'only_omega_premise_in_final_ALL3_acceptance_and_ALL4_typed_acceptance_laws':True,
            'all_twelve_structural_tree_code_compiler_interface_complete':True,
            'original_NatPacket_Horn_schema_Proof_interpretation_Con_proved':False}






























def main(source_check_only: bool = False) -> None:
    pure_syntax_definition = check_pure_syntax_definition()
    pure_proof_query_definition = check_pure_proof_query_definitions()
    raw_projection_definition = check_raw_projection_definitions()
    raw_field_definition = check_raw_field_definitions()
    projection_trace_definition = check_projection_trace_definitions()
    projection_rule_partition = check_projection_rule_partition()
    pure_substitution_node_definition = check_pure_substitution_node_definitions()
    pure_mp_node_definition = check_pure_mp_node_definitions()
    pure_strengthening_node_definition = check_pure_strengthening_node_definitions()
    original_mode_one_scalar_definition = check_original_mode_one_scalar_definitions()
    mode_one_variable_numeric_values = check_mode_one_variable_numeric_values()
    small_mode_arguments_and_pure_term_values = check_small_mode_arguments_and_pure_term_values()
    actual_abstract_pure_term_operation = check_actual_abstract_pure_term_operation()
    actual_abstract_argument_operation = check_actual_abstract_argument_operation()
    actual_abstract_frame = check_actual_abstract_frame()
    actual_abstract_frame_programs = check_actual_abstract_frame_programs()
    small_mode_formula_and_abstract_atomic_programs = check_small_mode_formula_and_abstract_atomic_programs()
    mode_one_full_formula_correctness = check_mode_one_full_formula_correctness()
    actual_top_formula_and_forall_node = check_actual_top_formula_and_forall_node()
    mode_two_variables_and_frame_terms = check_mode_two_variables_and_frame_terms()
    mode_two_actual_root = check_mode_two_actual_root()
    mode_two_actual_binder = check_mode_two_actual_binder()
    mode_two_full_formula = check_mode_two_full_formula()
    logical_instantiation_nodes = check_logical_instantiation_nodes()
    static_logical_nodes = check_static_logical_nodes()
    abstract_logical_nodes_and_exact_table = check_abstract_logical_nodes_and_exact_table()
    base_proof_nodes_and_parameterized_six_table = check_base_proof_nodes_and_parameterized_six_table()
    proof_tree_checked_trace_equation = check_proof_tree_checked_trace_equation()
    proof_tree_root_closed_fields = check_proof_tree_root_closed_fields()
    proof_tree_six_node_equation = check_proof_tree_six_node_equation()
    proof_tree_internal_induction = check_proof_tree_internal_induction()
    proof_tree_equation_unique = check_proof_tree_equation_unique()
    fixed_axiom_partial_test = check_fixed_axiom_partial_test()
    all_internal_forall_closure = check_all_internal_forall_closure()
    three_schema_index_system = check_three_schema_index_system()
    Project_atomic_compile = check_Project_atomic_compile()
    Project_source_recursive_grammar = check_Project_source_recursive_grammar()
    Project_actual_compiler = check_Project_actual_compiler()
    Project_compiler_recursive_equation = check_Project_compiler_recursive_equation()
    Project_compiler_output_typing = check_Project_compiler_output_typing()
    Project_compiler_source_completeness = check_Project_compiler_source_completeness()
    Project_compiler_scalar_uniqueness = check_Project_compiler_scalar_uniqueness()
    Project_compiler_source_validity = check_Project_compiler_source_validity()
    mode_three_scope = check_mode_three_scope()
    OUT.mkdir(exist_ok=True)
    sources = sorted([ROOT / "PPAC.lean", ROOT / "Audit.lean", ROOT / "Check.lean", ROOT / "CheckStep2.lean", ROOT / "CheckStep3.lean", ROOT / "CheckStep4.lean", *ROOT.glob("PPAC/**/*.lean")])
    # .axiom is the upstream Kind constructor; declaration-level axiom remains forbidden.
    forbidden = re.compile(r"\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b")
    for path in sources:
        if forbidden.search(strip_comments(path.read_text(encoding="utf-8-sig"))):
            raise RuntimeError(f"Forbidden token in {path.relative_to(ROOT)}")
    audit_source = strip_comments((ROOT / "Audit.lean").read_text(encoding="utf-8-sig"))
    expected = re.findall(r"^#print axioms (\S+)", audit_source, re.MULTILINE)
    if not expected or len(expected) != len(set(expected)):
        raise RuntimeError("Empty or duplicate audit declarations")
    internal_explicit: set[str] = set()
    for path in sorted((ROOT / "PPAC/Migration/Internal").glob("*.lean")):
        body = strip_comments(path.read_text(encoding="utf-8-sig"))
        namespace = "PPAC.Migration.Internal." + path.stem
        if re.findall(r"^namespace (\S+)", body, re.MULTILINE) != [namespace]:
            raise RuntimeError(f"Internal audit requires an explicit namespace review: {path.name}")
        names = re.findall(r"^(?:def|theorem|abbrev|structure|inductive)\s+([A-Za-z_][A-Za-z_0-9]*)", body, re.MULTILINE)
        internal_explicit.update(namespace + "." + name for name in names)
    missing_internal = internal_explicit - set(expected)
    if missing_internal:
        raise RuntimeError(f"Internal explicit declarations missing from Audit.lean: {sorted(missing_internal)}")
    # Formula-indexed relativization is a new interpretation primitive, not a
    # packet module. Require complete declaration coverage and the standard
    # three host logical axioms only; no inherited native certificate additions.
    relativization_body = strip_comments((ROOT / "PPAC/Migration/Relativization.lean").read_text(encoding="utf-8"))
    relativization_names = {"PPAC.Migration.Relativization." + n for n in
                            re.findall(r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)", relativization_body, re.MULTILINE)}
    if not relativization_names or not relativization_names <= set(expected):
        raise RuntimeError("Incomplete relativization declaration audit")
    source_lock = json.loads((ROOT / "docs/SOURCE_LOCK.json").read_text(encoding="utf-8"))
    if source_lock.get("source_hash_policy") != POLICY:
        raise RuntimeError("Source lock hash convention changed")
    forcing_name_lock = source_lock["source_proof_adaptations"]["forcing_name_induction"]
    if source_lock["files"][forcing_name_lock["source_file"]] != forcing_name_lock["source_sha256"]:
        raise RuntimeError("Original forcing-name source lock changed")
    forcing_name_body = strip_comments((ROOT / forcing_name_lock["adapter"]).read_text(encoding="utf-8"))
    forcing_name_names = {"PPAC.Migration.ForcingNameInduction." + n for n in
                          re.findall(r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)", forcing_name_body, re.MULTILINE)}
    if len(forcing_name_names) != 18 or forcing_name_names != set(forcing_name_lock["exact_declaration_footprints"]) or not forcing_name_names <= set(expected):
        raise RuntimeError("Incomplete original Child induction audit")
    names_lock = source_lock["source_proof_adaptations"]["forcing_names"]
    if source_lock["files"][names_lock["source_file"]] != names_lock["source_sha256"]:
        raise RuntimeError("Original IsName source lock changed")
    names_body = strip_comments((ROOT / names_lock["adapter"]).read_text(encoding="utf-8"))
    names_names = {"PPAC.Migration.ForcingNames." + n for n in
                   re.findall(r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)", names_body, re.MULTILINE)}
    if len(names_names) != 37 or names_names != set(names_lock["exact_declaration_footprints"]) or not names_names <= set(expected):
        raise RuntimeError("Incomplete original IsName definition and equation audit")
    eval_lock = source_lock["source_proof_adaptations"]["forcing_evaluation"]
    if source_lock["files"][eval_lock["source_file"]] != eval_lock["source_sha256"]:
        raise RuntimeError("Original evaluate source lock changed")
    eval_body = strip_comments((ROOT / eval_lock["adapter"]).read_text(encoding="utf-8"))
    eval_names = {"PPAC.Migration.ForcingEvaluation." + n for n in
                  re.findall(r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)", eval_body, re.MULTILINE)}
    if len(eval_names) != 44 or eval_names != set(eval_lock["exact_declaration_footprints"]) or not eval_names <= set(expected):
        raise RuntimeError("Incomplete original evaluate declaration audit")
    map_recursion_footprints = {}
    for key, module, count in (("forcing_name_recursion", "ForcingNameRecursion", 25),
                               ("forcing_map_conditions", "ForcingMapConditions", 44),
                               ("forcing_map_laws", "ForcingMapLaws", 33),
                               ("forcing_class_evaluation", "ForcingClassEvaluation", 34),
                               ("forcing_evaluation_covariance", "ForcingEvaluationCovariance", 9),
                               ("forcing_condition_graphs", "ForcingConditionGraphs", 33),
                               ("forcing_condition_action", "ForcingConditionAction", 37),
                               ("forcing_pair_name", "ForcingPairName", 32),
                               ("forcing_union_name", "ForcingUnionName", 32),
                               ("forcing_union_action", "ForcingUnionAction", 13),
                               ("forcing_check_name", "ForcingCheckName", 40),
                               ("forcing_check_name_laws", "ForcingCheckNameLaws", 22),
                               ("forcing_pair_induction", "ForcingPairInduction", 14),
                               ("forcing_atomic_step", "ForcingAtomicStep", 30),
                               ("forcing_atomic_graphs", "ForcingAtomicGraphs", 23),
                               ("forcing_atomic_recursion", "ForcingAtomicRecursion", 13),
                               ("forcing_atomic_relations", "ForcingAtomicRelations", 21),
                               ("forcing_atomic_basic", "ForcingAtomicBasic", 31),
                               ("forcing_triple_induction", "ForcingTripleInduction", 8),
                               ("forcing_atomic_laws", "ForcingAtomicLaws", 16),
                               ("forcing_atomic_symmetry", "ForcingAtomicSymmetry", 20),
                               ("forcing_formula", "ForcingFormula", 39),
                               ("forcing_sound", "ForcingSound", 9),
                               ("forcing_formula_symmetry", "ForcingFormulaSymmetry", 13),
                               ("forcing_stabilizer", "ForcingStabilizer", 19),
                               ("forcing_hs", "ForcingHS", 32),
                               ("forcing_hs_check", "ForcingHSCheck", 8),
                               ("forcing_name_conjugacy", "ForcingNameConjugacy", 16),
                               ("forcing_stabilizer_transport", "ForcingStabilizerTransport", 21),
                               ("forcing_hs_action", "ForcingHSAction", 11),
                               ("forcing_label_permutations", "ForcingLabelPermutations", 32),
                               ("forcing_label_conjugacy", "ForcingLabelConjugacy", 9),
                               ("forcing_conjugation_graph", "ForcingConjugationGraph", 30),
                               ("forcing_support_size", "ForcingSupportSize", 19),
                               ("forcing_support_filter", "ForcingSupportFilter", 25),
                               ("existing_cardinal_bounds", "ExistingCardinalBounds", 5),
                               ("forcing_support_intersection", "ForcingSupportIntersection", 7),
                               ("forcing_normal_filter", "ForcingNormalFilter", 18),
                               ("forcing_diagram_action", "ForcingDiagramAction", 17),
                               ("forcing_diagram_carrier", "ForcingDiagramCarrier", 23),
                               ("forcing_diagram_order", "ForcingDiagramOrder", 27),
                               ("forcing_cohen_coordinates", "ForcingCohenCoordinates", 17),
                               ("forcing_cohen_conditions", "ForcingCohenConditions", 26),
                               ("forcing_cohen_order_action", "ForcingCohenOrderAction", 17),
                               ("forcing_cohen_action_laws", "ForcingCohenActionLaws", 14),
                               ("forcing_product_action", "ForcingProductAction", 32),
                               ("forcing_withtop_carrier", "ForcingWithTopCarrier", 24),
                               ("forcing_withtop_action", "ForcingWithTopAction", 34),
                               ("forcing_product_family", "ForcingProductFamily", 36),
                               ("forcing_product_covariance", "ForcingProductCovariance", 20),
                               ("forcing_product_symmetry", "ForcingProductSymmetry", 11),
                               ("forcing_product_parameters", "ForcingProductParameters", 7),
                               ("forcing_diagram_poset", "ForcingDiagramPoset", 19),
                               ("forcing_product_poset", "ForcingProductPoset", 17),
                               ("forcing_product_stabilizer", "ForcingProductStabilizer", 4),
                               ("forcing_product_hs_pair", "ForcingProductHSPair", 5),
                               ("forcing_product_hs_union", "ForcingProductHSUnion", 4),
                               ("forcing_pair_union", "ForcingPairUnion", 12),
                               ("forcing_basic_set_axioms", "ForcingBasicSetAxioms", 7),
                               ("forcing_foundation", "ForcingFoundation", 13),
                               ("forcing_infinity", "ForcingInfinity", 9),
                               ("forcing_collected_name", "ForcingCollectedName", 16),
                               ("forcing_collected_hs", "ForcingCollectedHS", 17),
                               ("forcing_tuple_stabilizer", "ForcingTupleStabilizer", 12),
                               ("forcing_separation", "ForcingSeparation", 28),
                               ("forcing_separation_axiom", "ForcingSeparationAxiom", 8),
                               ("forcing_power_name", "ForcingPowerName", 27),
                               ("forcing_power_axiom", "ForcingPowerAxiom", 5),
                               ("forcing_replacement_orbit", "ForcingReplacementOrbit", 12),
                               ("forcing_replacement_witness", "ForcingReplacementWitness", 15),
                               ("forcing_replacement_image", "ForcingReplacementImage", 8),
                               ("forcing_replacement_axiom", "ForcingReplacementAxiom", 6),
                               ("forcing_zf_axioms", "ForcingZFAxioms", 4),
                               ("construction_base_monoid", "ConstructionBaseMonoid", 23),
                               ("construction_base_weights", "ConstructionBaseWeights", 41),
                               ("construction_fraction_order", "ConstructionFractionOrder", 50),
                               ("construction_fraction_density", "ConstructionFractionDensity", 17),
                               ("construction_real_cuts", "ConstructionRealCuts", 43),
                               ("construction_cut_weights", "ConstructionCutWeights", 32),
                               ("construction_fraction_addition", "ConstructionFractionAddition", 32),
                               ("construction_principal_addition", "ConstructionPrincipalAddition", 30),
                               ("construction_fraction_difference", "ConstructionFractionDifference", 16),
                               ("construction_base_cost_bound", "ConstructionBaseCostBound", 25),
                               ("construction_base_height_gap", "ConstructionBaseHeightGap", 23),
                               ("construction_probe_path", "ConstructionProbePath", 49),
                               ("construction_probe_transitions", "ConstructionProbeTransitions", 44),
                               ("construction_probe_letters", "ConstructionProbeLetters", 41),
                               ("construction_probe_action", "ConstructionProbeAction", 35),
                               ("construction_probe_target", "ConstructionProbeTarget", 22),
                               ("construction_probe_alphabet", "ConstructionProbeAlphabet", 28),
                               ("construction_probe_cones", "ConstructionProbeCones", 26),
                               ("construction_probe_cardinality", "ConstructionProbeCardinality", 5),
                               ("construction_probe_raw", "ConstructionProbeRaw", 43),
                               ("construction_probe_raw_action", "ConstructionProbeRawAction", 14),
                               ("construction_probe_raw_action_syntax", "ConstructionProbeRawActionSyntax", 22),
                               ("construction_probe_reduced", "ConstructionProbeReduced", 20),
                               ("construction_probe_word", "ConstructionProbeWord", 15),
                               ("construction_probe_word_quotient", "ConstructionProbeWordQuotient", 33),
                               ("construction_probe_letter_action", "ConstructionProbeLetterAction", 20),
                               ("construction_probe_evaluation", "ConstructionProbeEvaluation", 21),
                               ("construction_probe_evaluation_syntax", "ConstructionProbeEvaluationSyntax", 14),
                               ("construction_probe_evaluation_laws", "ConstructionProbeEvaluationLaws", 9),
                               ("construction_probe_word_monoid", "ConstructionProbeWordMonoid", 14),
                               ("construction_probe_word_monoid_syntax", "ConstructionProbeWordMonoidSyntax", 6),
                               ("construction_probe_old_embedding", "ConstructionProbeOldEmbedding", 13),
                               ("construction_probe_old_embedding_syntax", "ConstructionProbeOldEmbeddingSyntax", 11),
                               ("construction_probe_generator", "ConstructionProbeGenerator", 10),
                               ("construction_probe_generator_syntax", "ConstructionProbeGeneratorSyntax", 11),
                               ("construction_probe_hom_evaluation", "ConstructionProbeHomEvaluation", 29),
                               ("construction_probe_hom_evaluation_syntax", "ConstructionProbeHomEvaluationSyntax", 8),
                               ("construction_probe_lift_hom", "ConstructionProbeLiftHom", 13),
                               ("construction_probe_lift_hom_syntax", "ConstructionProbeLiftHomSyntax", 21),
                               ("construction_probe_hom_ext", "ConstructionProbeHomExt", 10),
                               ("construction_probe_hom_ext_syntax", "ConstructionProbeHomExtSyntax", 9),
                               ("construction_probe_indexed_generators", "ConstructionProbeIndexedGenerators", 8),
                               ("construction_probe_indexed_generators_syntax", "ConstructionProbeIndexedGeneratorsSyntax", 10),
                               ("construction_probe_presentation_transitions", "ConstructionProbePresentationTransitions", 12),
                               ("construction_probe_presentation_transitions_syntax", "ConstructionProbePresentationTransitionsSyntax", 9),
                               ("construction_probe_interpreted_letters", "ConstructionProbeInterpretedLetters", 11),
                               ("construction_probe_interpreted_letters_syntax", "ConstructionProbeInterpretedLettersSyntax", 9),
                               ("construction_probe_presented_lift", "ConstructionProbePresentedLift", 7),
                               ("construction_probe_presented_lift_syntax", "ConstructionProbePresentedLiftSyntax", 12),
                               ("existing_finite_sequence_bounds", "ExistingFiniteSequenceBounds", 33),
                               ("construction_probe_word_cardinality", "ConstructionProbeWordCardinality", 9),
                               ("construction_probe_mapped_path", "ConstructionProbeMappedPath", 10),
                               ("construction_probe_mapped_path_syntax", "ConstructionProbeMappedPathSyntax", 12),
                               ("construction_probe_letters_map", "ConstructionProbeLettersMap", 12),
                               ("construction_probe_letters_map_syntax", "ConstructionProbeLettersMapSyntax", 10),
                               ("construction_probe_alphabet_map", "ConstructionProbeAlphabetMap", 13),
                               ("construction_probe_alphabet_map_syntax", "ConstructionProbeAlphabetMapSyntax", 18),
                               ("construction_probe_raw_transport", "ConstructionProbeRawTransport", 18),
                               ("construction_probe_raw_transport_syntax", "ConstructionProbeRawTransportSyntax", 19),
                               ("construction_probe_word_transport", "ConstructionProbeWordTransport", 8),
                               ("construction_probe_transport_hom", "ConstructionProbeTransportHom", 11),
                               ("construction_probe_transport_hom_syntax", "ConstructionProbeTransportHomSyntax", 6),
                               ("construction_probe_conservative", "ConstructionProbeConservative", 7),
                               ("construction_probe_conservative_syntax", "ConstructionProbeConservativeSyntax", 12),
                               ("construction_probe_gates", "ConstructionProbeGates", 22),
                               ("construction_probe_gates_syntax", "ConstructionProbeGatesSyntax", 21),
                               ("construction_probe_head_transport", "ConstructionProbeHeadTransport", 10),
                               ("construction_probe_shared_intersections", "ConstructionProbeSharedIntersections", 13),
                               ("construction_probe_shared_gates", "ConstructionProbeSharedGates", 9),
                               ("construction_probe_transport_factors", "ConstructionProbeTransportFactors", 14),
                               ("construction_probe_transport_common", "ConstructionProbeTransportCommon", 11),
                               ("construction_probe_conservative_simulation", "ConstructionProbeConservativeSimulation", 5),
                               ("construction_probe_simulation", "ConstructionProbeSimulation", 11),
                               ("construction_probe_conditional_joins", "ConstructionProbeConditionalJoins", 22),
                               ("construction_probe_profiles", "ConstructionProbeProfiles", 22),
                               ("construction_persistent_profiles", "ConstructionPersistentProfiles", 26),
                               ("construction_probe_pushout", "ConstructionProbePushout", 15),
                               ("construction_probe_pushout_syntax", "ConstructionProbePushoutSyntax", 15),
                               ("construction_probe_letter_floor", "ConstructionProbeLetterFloor", 20),
                               ("construction_probe_letter_floor_syntax", "ConstructionProbeLetterFloorSyntax", 12),
                               ("construction_cut_addition", "ConstructionCutAddition", 21),
                               ("construction_probe_cost_bounds", "ConstructionProbeCostBounds", 7),
                               ("construction_probe_cost_bounds_syntax", "ConstructionProbeCostBoundsSyntax", 12),
                               ("construction_base_point_bound", "ConstructionBasePointBound", 7),
                               ("construction_base_point_bound_syntax", "ConstructionBasePointBoundSyntax", 3),
                               ("construction_cut_arithmetic", "ConstructionCutArithmetic", 21),
                               ("construction_cut_arithmetic_syntax", "ConstructionCutArithmeticSyntax", 18),
                               ("construction_fraction_scaling", "ConstructionFractionScaling", 10),
                               ("construction_cut_division", "ConstructionCutDivision", 17),
                               ("construction_cut_division_syntax", "ConstructionCutDivisionSyntax", 12),
                               ("construction_cut_quarter_sum", "ConstructionCutQuarterSum", 9),
                               ("construction_cut_quarter_sum_syntax", "ConstructionCutQuarterSumSyntax", 6),
                               ("construction_cut_associativity", "ConstructionCutAssociativity", 8),
                               ("construction_cut_associativity_syntax", "ConstructionCutAssociativitySyntax", 3),
                               ("construction_cut_locatedness", "ConstructionCutLocatedness", 7),
                               ("construction_cut_difference", "ConstructionCutDifference", 21),
                               ("construction_cut_difference_syntax", "ConstructionCutDifferenceSyntax", 6),
                               ("construction_probe_intervals", "ConstructionProbeIntervals", 9),
                               ("construction_probe_letter_intervals", "ConstructionProbeLetterIntervals", 6),
                               ("construction_probe_intervals_syntax", "ConstructionProbeIntervalsSyntax", 24),
                               ("construction_probe_cost_supremum", "ConstructionProbeCostSupremum", 16),
                               ("construction_probe_interval_choices", "ConstructionProbeIntervalChoices", 16),
                               ("construction_probe_height_interval_graphs", "ConstructionProbeHeightIntervalGraphs", 13),
                               ("construction_probe_height_intervals_syntax", "ConstructionProbeHeightIntervalsSyntax", 12),
                               ("construction_principal_sum_bridge", "ConstructionPrincipalSumBridge", 1),
                               ("construction_base_uniform_margin", "ConstructionBaseUniformMargin", 4),
                               ("construction_base_uniform_margin_syntax", "ConstructionBaseUniformMarginSyntax", 9),
                               ("construction_fraction_product", "ConstructionFractionProduct", 14),
                               ("construction_cut_product", "ConstructionCutProduct", 23),
                               ("construction_cut_minimum", "ConstructionCutMinimum", 11),
                               ("construction_word_arithmetic_syntax", "ConstructionWordArithmeticSyntax", 12),
                               ("construction_probe_height_operation", "ConstructionProbeHeightOperation", 18),
                               ("construction_probe_height_fold", "ConstructionProbeHeightFold", 7),
                               ("construction_probe_height_fold_syntax", "ConstructionProbeHeightFoldSyntax", 6),
                               ("construction_probe_gatecap", "ConstructionProbeGateCap", 28),
                               ("construction_probe_gatecap_syntax", "ConstructionProbeGateCapSyntax", 3),
                               ("construction_probe_cost_operation", "ConstructionProbeCostOperation", 28),
                               ("construction_probe_cost_fold", "ConstructionProbeCostFold", 21),
                               ("construction_probe_cost_fold_syntax", "ConstructionProbeCostFoldSyntax", 9),
                               ('construction_cut_product_unit', 'ConstructionCutProductUnit', 4),
                               ('construction_cut_product_unit_syntax', 'ConstructionCutProductUnitSyntax', 3),
                               ('construction_probe_weight_bounds', 'ConstructionProbeWeightBounds', 7),
                               ('construction_probe_weight_bounds_syntax', 'ConstructionProbeWeightBoundsSyntax', 3),
                               ('construction_probe_old_cost_factors', 'ConstructionProbeOldCostFactors', 5),
                               ('construction_probe_old_cost_factors_syntax', 'ConstructionProbeOldCostFactorsSyntax', 3),
                               ('construction_probe_cost_margins', 'ConstructionProbeCostMargins', 4),
                               ('construction_probe_cost_margins_syntax', 'ConstructionProbeCostMarginsSyntax', 3),
                               ('construction_probe_old_new_margin', 'ConstructionProbeOldNewMargin', 2),
                               ('construction_probe_old_new_margin_syntax', 'ConstructionProbeOldNewMarginSyntax', 3),
                               ('construction_probe_new_old_margin', 'ConstructionProbeNewOldMargin', 3),
                               ('construction_probe_new_old_margin_syntax', 'ConstructionProbeNewOldMarginSyntax', 3),
                               ('construction_probe_old_cost_supremum', 'ConstructionProbeOldCostSupremum', 3),
                               ('construction_probe_old_cost_supremum_syntax', 'ConstructionProbeOldCostSupremumSyntax', 3),
                               ('construction_fraction_product_arithmetic', 'ConstructionFractionProductArithmetic', 4),
                               ('construction_cut_product_arithmetic', 'ConstructionCutProductArithmetic', 4),
                               ('construction_probe_same_head_margin', 'ConstructionProbeSameHeadMargin', 2),
                               ('construction_probe_uniform_margins', 'ConstructionProbeUniformMargins', 5),
                               ('construction_probe_height_cost', 'ConstructionProbeHeightCost', 1),
                               ('construction_probe_height_cost_syntax', 'ConstructionProbeHeightCostSyntax', 3),
                               ('construction_probe_successor', 'ConstructionProbeSuccessor', 1),
                               ('construction_probe_successor_syntax', 'ConstructionProbeSuccessorSyntax', 3),
                               ('construction_probe_parent', 'ConstructionProbeParent', 4),
                               ('construction_probe_parent_syntax', 'ConstructionProbeParentSyntax', 3),
                               ('construction_merger_relations', 'ConstructionMergerRelations', 19),
                               ('construction_merger_copies', 'ConstructionMergerCopies', 35),
                               ('construction_merger_action', 'ConstructionMergerAction', 28),
                               ('construction_merger_action_syntax', 'ConstructionMergerActionSyntax', 3),
                               ('construction_merger_word_action', 'ConstructionMergerWordAction', 19),
                               ('construction_merger_word_operation', 'ConstructionMergerWordOperation', 19),
                               ('construction_merger_word_product', 'ConstructionMergerWordProduct', 21),
                               ('construction_merger_word_product_syntax', 'ConstructionMergerWordProductSyntax', 3),
                               ('construction_merger_word_monoid', 'ConstructionMergerWordMonoid', 12),
                               ('construction_merger_word_length', 'ConstructionMergerWordLength', 15),
                               ('construction_merger_word_cancellation', 'ConstructionMergerWordCancellation', 6),
                               ('construction_merger_word_cancellation_syntax', 'ConstructionMergerWordCancellationSyntax', 3),
                               ('construction_merger_copy_cones', 'ConstructionMergerCopyCones', 17),
                               ('construction_merger_copy_cones_syntax', 'ConstructionMergerCopyConesSyntax', 3),
                               ('construction_merger_word_divisibility', 'ConstructionMergerWordDivisibility', 16),
                               ('construction_merger_word_cones', 'ConstructionMergerWordCones', 12),
                               ('construction_merger_word_cones_syntax', 'ConstructionMergerWordConesSyntax', 3),
                               ('construction_merger_old_embedding', 'ConstructionMergerOldEmbedding', 6),
                               ('construction_merger_roots', 'ConstructionMergerRoots', 16),
                               ('construction_merger_roots_syntax', 'ConstructionMergerRootsSyntax', 3),
                               ('construction_merger_coordinates', 'ConstructionMergerCoordinates', 19),
                               ('construction_merger_coordinate_laws', 'ConstructionMergerCoordinateLaws', 10),
                               ('construction_merger_coordinate_syntax', 'ConstructionMergerCoordinateSyntax', 3),
                               ('construction_merger_finite_weights', 'ConstructionMergerFiniteWeights', 26),
                               ('construction_merger_finite_weights_syntax', 'ConstructionMergerFiniteWeightsSyntax', 3),
                               ('construction_merger_weight_estimates', 'ConstructionMergerWeightEstimates', 13),
                               ('construction_merger_weight_estimates_syntax', 'ConstructionMergerWeightEstimatesSyntax', 3),
                               ('construction_merger_height_comparison', 'ConstructionMergerHeightComparison', 11),
                               ('construction_merger_height_comparison_syntax', 'ConstructionMergerHeightComparisonSyntax', 3),
                               ('construction_merger_height_upper', 'ConstructionMergerHeightUpper', 9),
                               ('construction_merger_height_upper_syntax', 'ConstructionMergerHeightUpperSyntax', 3),
                               ('construction_merger_average_gap', 'ConstructionMergerAverageGap', 9),
                               ('construction_merger_average_gap_syntax', 'ConstructionMergerAverageGapSyntax', 3),
                               ('construction_merger_coordinate_margin', 'ConstructionMergerCoordinateMargin', 3),
                               ('construction_merger_coordinate_margin_syntax', 'ConstructionMergerCoordinateMarginSyntax', 3),
                               ('construction_merger_uniform_margin', 'ConstructionMergerUniformMargin', 20),
                               ('construction_merger_uniform_margin_syntax', 'ConstructionMergerUniformMarginSyntax', 3),
                               ('construction_merger_heightCost', 'ConstructionMergerHeightCost', 6),
                               ('construction_merger_heightCost_syntax', 'ConstructionMergerHeightCostSyntax', 3),
                               ('construction_merger_word_parameters', 'ConstructionMergerWordParameters', 20),
                               ('construction_merger_word_heights', 'ConstructionMergerWordHeights', 15),
                               ('construction_merger_word_costs', 'ConstructionMergerWordCosts', 12),
                               ('construction_merger_word_weights_syntax', 'ConstructionMergerWordWeightsSyntax', 3),
                               ('construction_merger_word_margins', 'ConstructionMergerWordMargins', 9),
                               ('construction_merger_word_heightCost', 'ConstructionMergerWordHeightCost', 1),
                               ('construction_merger_word_heightCost_syntax', 'ConstructionMergerWordHeightCostSyntax', 3),
                               ('construction_merger_cardinality', 'ConstructionMergerCardinality', 5),
                               ('construction_merger_parent', 'ConstructionMergerParent', 1),
                               ('construction_merger_parent_syntax', 'ConstructionMergerParentSyntax', 3),
                               ('construction_directed_system', 'ConstructionDirectedSystem', 29),
                               ('construction_directed_limit_carrier', 'ConstructionDirectedLimitCarrier', 47),
                               ('construction_directed_limit_carrier_syntax', 'ConstructionDirectedLimitCarrierSyntax', 3),
                               ('construction_directed_monoid_data', 'ConstructionDirectedMonoidData', 33),
                               ('construction_directed_product', 'ConstructionDirectedProduct', 16),
                               ('construction_directed_monoid', 'ConstructionDirectedMonoid', 13),
                               ('construction_directed_monoid_syntax', 'ConstructionDirectedMonoidSyntax', 3),
                               ('construction_directed_conservative_data', 'ConstructionDirectedConservativeData', 11),
                               ('construction_directed_factors', 'ConstructionDirectedFactors', 4),
                               ('construction_directed_conservative', 'ConstructionDirectedConservative', 4),
                               ('construction_directed_conservative_syntax', 'ConstructionDirectedConservativeSyntax', 3),
                               ('construction_directed_profiles', 'ConstructionDirectedProfiles', 13),
                               ('construction_directed_profiles_syntax', 'ConstructionDirectedProfilesSyntax', 3),
                               ('construction_directed_weight_data', 'ConstructionDirectedWeightData', 24),
                               ('construction_directed_weights', 'ConstructionDirectedWeights', 15),
                               ('construction_directed_height_cost', 'ConstructionDirectedHeightCost', 18),
                               ('construction_directed_height_cost_syntax', 'ConstructionDirectedHeightCostSyntax', 3),
                               ('existing_small_union', 'ExistingSmallUnion', 6),
                               ('construction_directed_cardinality', 'ConstructionDirectedCardinality', 18),
                               ('construction_directed_marks', 'ConstructionDirectedMarks', 13),
                               ('construction_directed_object', 'ConstructionDirectedObject', 1),
                               ('construction_directed_object_syntax', 'ConstructionDirectedObjectSyntax', 3),
                               ('construction_directed_lift', 'ConstructionDirectedLift', 17),
                               ('construction_directed_lift_syntax', 'ConstructionDirectedLiftSyntax', 21),
                               ('construction_directed_cocone', 'ConstructionDirectedCocone', 11),
                               ('construction_directed_colimit', 'ConstructionDirectedColimit', 5),
                               ('construction_directed_colimit_syntax', 'ConstructionDirectedColimitSyntax', 3),
                               ('construction_merger_prescription_map', 'ConstructionMergerPrescriptionMap', 18),
                               ('construction_merger_prescription_map_syntax', 'ConstructionMergerPrescriptionMapSyntax', 9),
                               ('construction_request_maps', 'ConstructionRequestMaps', 4),
                               ('construction_request_maps_syntax', 'ConstructionRequestMapsSyntax', 6),
                               ('construction_round_fields', 'ConstructionRoundFields', 9),
                               ('construction_round_successors', 'ConstructionRoundSuccessors', 4),
                               ('construction_round_step', 'ConstructionRoundStep', 5),
                               ('construction_round_step_syntax', 'ConstructionRoundStepSyntax', 30),
                               ('construction_request_schedule', 'ConstructionRequestSchedule', 42),
                               ('construction_request_schedule_syntax', 'ConstructionRequestScheduleSyntax', 3),
                               ('construction_request_carrier', 'ConstructionRequestCarrier', 23),
                               ('construction_complete_schedule', 'ConstructionCompleteSchedule', 17),
                               ('construction_complete_schedule_syntax', 'ConstructionCompleteScheduleSyntax', 6),
                               ('existing_ordinal_enumeration', 'ExistingOrdinalEnumeration', 9),
                               ('construction_schedule_order', 'ConstructionScheduleOrder', 8),
                               ('construction_schedule_order_syntax', 'ConstructionScheduleOrderSyntax', 6),
                               ('construction_ordinal_schedule', 'ConstructionOrdinalSchedule', 4),
                               ('construction_ordinal_schedule_syntax', 'ConstructionOrdinalScheduleSyntax', 6),
                               ('existing_l_choice_bridge', 'ExistingLChoiceBridge', 4),
                               ('constructible_ground', 'ConstructibleGround', 8),
                               ('constructible_source', 'ConstructibleSource', 17),
                               ('construction_round_selection', 'ConstructionRoundSelection', 30),
                               ('construction_tower_successor', 'ConstructionTowerSuccessor', 53),
                               ('construction_tower_limit', 'ConstructionTowerLimit', 33),
                               ('construction_tower_canonical_limit', 'ConstructionTowerCanonicalLimit', 14),
                               ('construction_tower_initial', 'ConstructionTowerInitial', 11),
                               ('construction_tower_canonical_successor', 'ConstructionTowerCanonicalSuccessor', 9),
                               ('construction_tower_history', 'ConstructionTowerHistory', 35),
                               ('construction_tower_transitions', 'ConstructionTowerTransitions', 37),
                               ('construction_tower_validity', 'ConstructionTowerValidity', 23),
                               ('construction_tower_diagram', 'ConstructionTowerDiagram', 9),
                               ('construction_tower_history_limit', 'ConstructionTowerHistoryLimit', 9),
                               ('construction_tower_history_initial', 'ConstructionTowerHistoryInitial', 9),
                               ('construction_tower_history_successor', 'ConstructionTowerHistorySuccessor', 10),
                               ('construction_tower_append', 'ConstructionTowerAppend', 6),
                               ('construction_tower_history_closure', 'ConstructionTowerHistoryClosure', 18),
                               ('construction_tower_iteration_cases', 'ConstructionTowerIterationCases', 15),
                               ('construction_tower_iteration', 'ConstructionTowerIteration', 29),
                               ('construction_tower_iteration_validity', 'ConstructionTowerIterationValidity', 12),
                               ('construction_tower_map_succ', 'ConstructionTowerMapSucc', 17),
                               ('construction_request_padding', 'ConstructionRequestPadding', 14),
                               ('construction_request_cardinality', 'ConstructionRequestCardinality', 16),
                               ('construction_schedule_cardinality', 'ConstructionScheduleCardinality', 15),
                               ('construction_tower_cardinality', 'ConstructionTowerCardinality', 17),
                               ('construction_round_fresh', 'ConstructionRoundFresh', 12),
                               ('construction_operation_source', 'ConstructionOperationSource', 12),
                               ('construction_round_source', 'ConstructionRoundSource', 6),
                               ('construction_probe_independent', 'ConstructionProbeIndependent', 17),
                               ('construction_merger_root_system', 'ConstructionMergerRootSystem', 20),
                               ('construction_cone_transport', 'ConstructionConeTransport', 13),
                               ('construction_tower_request_cones', 'ConstructionTowerRequestCones', 8),
                               ('construction_tower_execution', 'ConstructionTowerExecution', 19),
                               ('construction_tower_probe_family', 'ConstructionTowerProbeFamily', 18),
                               ('construction_tower_probe_independence', 'ConstructionTowerProbeIndependence', 10),
                               ('construction_complete_round', 'ConstructionCompleteRound', 24),
                               ('construction_saturation_step', 'ConstructionSaturationStep', 16),
                               ('construction_saturation_successor', 'ConstructionSaturationSuccessor', 9),
                               ('construction_saturation_iteration_cases', 'ConstructionSaturationIterationCases', 11),
                               ('construction_saturation_iteration', 'ConstructionSaturationIteration', 22),
                               ('construction_saturation_iteration_validity', 'ConstructionSaturationIterationValidity', 15),
                               ('existing_ordinal_image', 'ExistingOrdinalImage', 5),
                               ('existing_successor_regularity', 'ExistingSuccessorRegularity', 1),
                               ('construction_saturation_index', 'ConstructionSaturationIndex', 30),
                               ('construction_saturation_boundedness', 'ConstructionSaturationBoundedness', 15),
                               ('construction_saturation_cover', 'ConstructionSaturationCover', 31),
                               ('construction_saturation_probe_stage', 'ConstructionSaturationProbeStage', 4),
                               ('construction_saturation_probes', 'ConstructionSaturationProbes', 22),
                               ('construction_saturation_prescription_stage', 'ConstructionSaturationPrescriptionStage', 11),
                               ('construction_saturation_mergers', 'ConstructionSaturationMergers', 30),
                               ('construction_saturation_complement', 'ConstructionSaturationComplement', 22),
                               ('construction_saturation_cardinals', 'ConstructionSaturationCardinals', 27),
                               ('existing_indexed_choice', 'ExistingIndexedChoice', 8),
                               ('construction_ideal_approximation', 'ConstructionIdealApproximation', 10),
                               ('construction_ideal_cofinal', 'ConstructionIdealCofinal', 8),
                               ('construction_ideal_probes', 'ConstructionIdealProbes', 29),
                               ('construction_concrete_cardinals', 'ConstructionConcreteCardinals', 14),
                               ('construction_concrete_tower', 'ConstructionConcreteTower', 8),
                               ('construction_concrete_base', 'ConstructionConcreteBase', 24),
                               ('construction_placement_freshness', 'ConstructionPlacementFreshness', 38),
                               ('construction_placement_extensions', 'ConstructionPlacementExtensions', 26),
                               ('construction_placement_pasting', 'ConstructionPlacementPasting', 37),
                               ('construction_placement_triple', 'ConstructionPlacementTriple', 34),
                               ('construction_diagram_placements', 'ConstructionDiagramPlacements', 47),
                               ('construction_diagram_prescription', 'ConstructionDiagramPrescription', 50),
                               ('construction_diagram_amalgamation', 'ConstructionDiagramAmalgamation', 28),
                               ('construction_diagram_three', 'ConstructionDiagramThree', 9),
                               ('construction_cohen_compatibility', 'ConstructionCohenCompatibility', 77),
                               ('construction_descent_placement', 'ConstructionDescentPlacement', 30),
                               ('construction_countable_hull', 'ConstructionCountableHull', 31),
                               ('construction_conservative_hull', 'ConstructionConservativeHull', 29),
                               ('construction_countable_conservative_hull', 'ConstructionCountableConservativeHull', 53),
                               ('construction_ideal_contraction', 'ConstructionIdealContraction', 11),
                               ('construction_component_vertices', 'ConstructionComponentVertices', 30),
                               ('construction_component_carrier', 'ConstructionComponentCarrier', 21),
                               ('construction_component_cofinal', 'ConstructionComponentCofinal', 23),
                               ('forcing_mix_name', 'ForcingMixName', 25),
                               ('forcing_mix_laws', 'ForcingMixLaws', 20),
                               ('forcing_equivariant_mix', 'ForcingEquivariantMix', 14),
                               ('forcing_supported_names', 'ForcingSupportedNames', 14),
                               ('construction_compatible_placement', 'ConstructionCompatiblePlacement', 19),
                               ('forcing_supporting_root', 'ForcingSupportingRoot', 15),
                               ('forcing_active_independent', 'ForcingActiveIndependent', 7),
                               ('forcing_active_equality', 'ForcingActiveEquality', 5),
                               ('forcing_support_orbit', 'ForcingSupportOrbit', 13),
                               ('forcing_support_descent', 'ForcingSupportDescent', 6),
                               ('forcing_product_bits', 'ForcingProductBits', 25),
                               ('forcing_label_names', 'ForcingLabelNames', 40),
                               ('forcing_label_set', 'ForcingLabelSet', 26),
                               ('forcing_label_bound', 'ForcingLabelBound', 17),
                               ('forcing_local_names', 'ForcingLocalNames', 23),
                               ('forcing_local_normalize', 'ForcingLocalNormalize', 10),
                               ('forcing_local_name_descent', 'ForcingLocalNameDescent', 6),
                               ('forcing_local_atomic', 'ForcingLocalAtomic', 10),
                               ('forcing_local_quotient', 'ForcingLocalQuotient', 24),
                               ('forcing_local_restriction', 'ForcingLocalRestriction', 23),
                               ('forcing_local_injectivity', 'ForcingLocalInjectivity', 5),
                               ('forcing_local_intersection', 'ForcingLocalIntersection', 6),
                               ('forcing_eligibility', 'ForcingEligibility', 21),
                               ('forcing_eligibility_reflection', 'ForcingEligibilityReflection', 5),
                               ('forcing_eligible_objects', 'ForcingEligibleObjects', 8),
                               ('forcing_eligible_restriction', 'ForcingEligibleRestriction', 18),
                               ('forcing_eligible_intersection', 'ForcingEligibleIntersection', 6),
                               ('forcing_eligible_laws', 'ForcingEligibleLaws', 10),
                               ('forcing_eligible_family', 'ForcingEligibleFamily', 17),
                               ('forcing_eligible_map_family', 'ForcingEligibleMapFamily', 24),
                               ('forcing_eligible_system', 'ForcingEligibleSystem', 28),
                               ('forcing_system_availability', 'ForcingSystemAvailability', 24),
                               ('forcing_system_fibers', 'ForcingSystemFibers', 22),
                               ('forcing_component_fibers', 'ForcingComponentFibers', 27),
                               ('forcing_component_matches', 'ForcingComponentMatches', 42),
                               ('forcing_component_gluing', 'ForcingComponentGluing', 46),
                               ('forcing_label_system', 'ForcingLabelSystem', 30),
                               ('forcing_label_cardinality', 'ForcingLabelCardinality', 9),
                               ('forcing_concrete_labels', 'ForcingConcreteLabels', 28),
                               ('forcing_reindex_system', 'ForcingReindexSystem', 23),
                               ('forcing_label_transport', 'ForcingLabelTransport', 17),
                               ('forcing_component_move', 'ForcingComponentMove', 25),
                               ('forcing_glued_transport', 'ForcingGluedTransport', 30),
                               ('forcing_local_transport', 'ForcingLocalTransport', 22),
                               ('forcing_local_name_transport', 'ForcingLocalNameTransport', 19),
                               ('forcing_local_quotient_transport', 'ForcingLocalQuotientTransport', 22),
                               ('forcing_eligible_transport', 'ForcingEligibleTransport', 22),
                               ('forcing_eligible_reindex', 'ForcingEligibleReindex', 16),
                               ('forcing_tail_codes', 'ForcingTailCodes', 33),
                               ('forcing_component_rebase', 'ForcingComponentRebase', 13),
                               ('forcing_tail_transport', 'ForcingTailTransport', 6),
                               ('forcing_tail_covariance', 'ForcingTailCovariance', 9),
                               ('forcing_persistent_selection', 'ForcingPersistentSelection', 17),
                               ('forcing_principal_filter', 'ForcingPrincipalFilter', 23),
                               ('forcing_persistent_codes', 'ForcingPersistentCodes', 17),
                               ('forcing_persistent_works', 'ForcingPersistentWorks', 38),
                               ('forcing_persistent_covariance', 'ForcingPersistentCovariance', 9),
                               ('forcing_works_covariance', 'ForcingWorksCovariance', 13),
                               ('forcing_forced_availability', 'ForcingForcedAvailability', 17),
                               ('forcing_stable_codes', 'ForcingStableCodes', 8),
                               ('forcing_ordinal_ranks', 'ForcingOrdinalRanks', 35),
                               ('forcing_ordinal_fixed', 'ForcingOrdinalFixed', 21),
                               ('forcing_ordinal_membership', 'ForcingOrdinalMembership', 28),
                               ('forcing_ordinal_transitivity', 'ForcingOrdinalTransitivity', 25),
                               ('forcing_check_reflection', 'ForcingCheckReflection', 8),
                               ('forcing_raw_rank', 'ForcingRawRank', 20),
                               ('forcing_ordinal_decision', 'ForcingOrdinalDecision', 17),
                               ('forcing_ordinal_coding', 'ForcingOrdinalCoding', 13),
                               ('forcing_ordinal_root', 'ForcingOrdinalRoot', 13),
                               ('forcing_cohen_selection', 'ForcingCohenSelection', 20),
                               ('forcing_cohen_rank_consumers', 'ForcingCohenRankConsumers', 16),
                               ('forcing_tail_group', 'ForcingTailGroup', 21),
                               ('forcing_code_selection', 'ForcingCodeSelection', 16),
                               ('forcing_code_ranks', 'ForcingCodeRanks', 6),
                               ('forcing_code_rank_consumers', 'ForcingCodeRankConsumers', 6),
                               ('forcing_code_links', 'ForcingCodeLinks', 16),
                               ('forcing_code_link_representation', 'ForcingCodeLinkRepresentation', 5),
                               ('forcing_linked_stability', 'ForcingLinkedStability', 6),
                               ('forcing_linked_working', 'ForcingLinkedWorking', 4),
                               ('forcing_code_link_closure', 'ForcingCodeLinkClosure', 11),
                               ('forcing_code_link_covariance', 'ForcingCodeLinkCovariance', 10),
                               ('forcing_ordinal_table', 'ForcingOrdinalTable', 20),
                               ('forcing_germ_preliminary', 'ForcingGermPreliminary', 15),
                               ('forcing_germ_equality', 'ForcingGermEquality', 4),
                               ('forcing_germ_locality', 'ForcingGermLocality', 8),
                               ('forcing_germ_covariance', 'ForcingGermCovariance', 4),
                               ('forcing_germ_density', 'ForcingGermDensity', 16),
                               ('forcing_chain_bound', 'ForcingChainBound', 25),
                               ('forcing_countable_tree_evaluation', 'ForcingCountableTreeEvaluation', 43),
                               ('forcing_countable_tree_algebra', 'ForcingCountableTreeAlgebra', 35),
                               ('existing_tree_addresses', 'ExistingTreeAddresses', 29),
                               ('forcing_countable_tree_codes', 'ForcingCountableTreeCodes', 24),
                               ('forcing_countable_tree_graft', 'ForcingCountableTreeGraft', 31),
                               ('forcing_countable_tree_cardinality', 'ForcingCountableTreeCardinality', 21),
                               ('forcing_countable_tree_values', 'ForcingCountableTreeValues', 37),
                               ('forcing_countable_tree_graft_values', 'ForcingCountableTreeGraftValues', 19),
                               ('forcing_countable_hull', 'ForcingCountableHull', 16),
                               ('forcing_cohen_codes', 'ForcingCohenCodes', 37),
                               ('forcing_cohen_compatible_choice', 'ForcingCohenCompatibleChoice', 13),
                               ('forcing_cohen_restriction', 'ForcingCohenRestriction', 25),
                               ('forcing_cohen_flip', 'ForcingCohenFlip', 40),
                               ('forcing_cohen_operation', 'ForcingCohenOperation', 15),
                               ('forcing_cohen_antichain', 'ForcingCohenAntichain', 12),
                               ('forcing_cohen_counting', 'ForcingCohenCounting', 10),
                               ('forcing_cohen_chain_bound', 'ForcingCohenChainBound', 14),
                               ('forcing_local_record_pullback', 'ForcingLocalRecordPullback', 24),
                               ('forcing_local_record_equality', 'ForcingLocalRecordEquality', 15),
                               ('forcing_relation_class', 'ForcingRelationClass', 30),
                               ('forcing_relation_class_move', 'ForcingRelationClassMove', 21),
                               ('forcing_label_density', 'ForcingLabelDensity', 8),
                               ('construction_diagram_coverage', 'ConstructionDiagramCoverage', 6),
                               ('forcing_class_representation', 'ForcingClassRepresentation', 9),
                               ('forcing_code_record_witness', 'ForcingCodeRecordWitness', 9),
                               ('forcing_code_cardinals', 'ForcingCodeCardinals', 14),
                               ('forcing_probe_density', 'ForcingProbeDensity', 22),
                               ('forcing_local_list', 'ForcingLocalList', 10),
                               ('forcing_outside_local', 'ForcingOutsideLocal', 12),
                               ('forcing_class_profile', 'ForcingClassProfile', 13),
                               ('forcing_outside_copies', 'ForcingOutsideCopies', 29),
                               ('forcing_probe_row_hits', 'ForcingProbeRowHits', 27),
                               ('forcing_probe_stable', 'ForcingProbeStable', 7),
                               ('forcing_probe_total', 'ForcingProbeTotal', 6),
                               ('forcing_probe_single', 'ForcingProbeSingle', 5),
                               ('forcing_probe_rows', 'ForcingProbeRows', 11),
                               ('forcing_concrete_ordinal_count', 'ForcingConcreteOrdinalCount', 6),
                               ('forcing_ideal_probe_count', 'ForcingIdealProbeCount', 6),
                               ('forcing_concrete_germ_density', 'ForcingConcreteGermDensity', 8),
                               ('forcing_germ_alignments', 'ForcingGermAlignments', 32),
                               ('construction_cell_descent', 'ConstructionCellDescent', 30),
                               ('construction_finite_descent', 'ConstructionFiniteDescent', 31),
                               ('construction_pushout_pasting', 'ConstructionPushoutPasting', 22),
                               ('construction_pushout_identification', 'ConstructionPushoutIdentification', 20),
                               ('construction_cell_preimage', 'ConstructionCellPreimage', 20),
                               ('construction_merger_evaluation', 'ConstructionMergerEvaluation', 23),
                               ('construction_merger_presented_lift', 'ConstructionMergerPresentedLift', 32),
                               ('construction_merger_pushout', 'ConstructionMergerPushout', 24),
                               ('construction_merger_copies_map', 'ConstructionMergerCopiesMap', 25),
                               ('construction_merger_word_transport', 'ConstructionMergerWordTransport', 27),
                               ('construction_cell_generation', 'ConstructionCellGeneration', 35),
                               ('construction_cell_coefficients', 'ConstructionCellCoefficients', 29),
                               ('construction_attachment_coefficients', 'ConstructionAttachmentCoefficients', 32),
                               ('construction_attachment_dependencies', 'ConstructionAttachmentDependencies', 38),
                               ('construction_cell_parameters', 'ConstructionCellParameters', 40),
                               ('construction_first_appearance', 'ConstructionFirstAppearance', 44),
                               ('construction_block_stages', 'ConstructionBlockStages', 63),
                               ('construction_block_traces', 'ConstructionBlockTraces', 29),
                               ('construction_block_index', 'ConstructionBlockIndex', 40),
                               ('construction_block_cuts', 'ConstructionBlockCuts', 45),
                               ('construction_actual_blocks', 'ConstructionActualBlocks', 15),
                               ('construction_block_boundary', 'ConstructionBlockBoundary', 19),
                               ('construction_block_continuity', 'ConstructionBlockContinuity', 18),
                               ('construction_cut_limits', 'ConstructionCutLimits', 29),
                               ('construction_flat_stages', 'ConstructionFlatStages', 33),
                               ('construction_flat_outer', 'ConstructionFlatOuter', 23),
                               ('construction_flat_timeline', 'ConstructionFlatTimeline', 16),
                               ('construction_cell_simulation_equiv', 'ConstructionCellSimulationEquiv', 26),
                               ('construction_executed_cell_presentation', 'ConstructionExecutedCellPresentation', 27),
                               ('construction_range_object', 'ConstructionRangeObject', 10),
                               ('construction_mapped_merger', 'ConstructionMappedMerger', 10),
                               ('construction_mapped_probe', 'ConstructionMappedProbe', 10),
                               ('construction_selected_attachments', 'ConstructionSelectedAttachments', 25),
                               ('construction_block_attachments', 'ConstructionBlockAttachments', 17),
                               ('construction_flat_attachments', 'ConstructionFlatAttachments', 25),
                               ('construction_step_cell', 'ConstructionStepCell', 31),
                               ('construction_step_cell_selection', 'ConstructionStepCellSelection', 28),
                               ('construction_global_dependencies', 'ConstructionGlobalDependencies', 28),
                               ('construction_selected_cell_words', 'ConstructionSelectedCellWords', 15),
                               ('construction_selected_cell_restriction', 'ConstructionSelectedCellRestriction', 13),
                               ('construction_restricted_cell_simulation', 'ConstructionRestrictedCellSimulation', 16),
                               ('construction_restricted_cell_pushout', 'ConstructionRestrictedCellPushout', 9),
                               ('construction_cell_restriction', 'ConstructionCellRestriction', 40),
                               ('construction_subobject_union', 'ConstructionSubobjectUnion', 41),
                               ('construction_union_pushout', 'ConstructionUnionPushout', 33),
                               ('construction_cell_base_change', 'ConstructionCellBaseChange', 22),
                               ('construction_intermediate', 'ConstructionIntermediate', 16),
                               ('construction_future_family', 'ConstructionFutureFamily', 52),
                               ('construction_future_cut', 'ConstructionFutureCut', 24),
                               ('construction_future_limit', 'ConstructionFutureLimit', 26),
                               ('construction_future_selected', 'ConstructionFutureSelected', 16),
                               ('construction_future_induction', 'ConstructionFutureInduction', 9),
                               ('construction_future_tower', 'ConstructionFutureTower', 7),
                               ('construction_reordered', 'ConstructionReordered', 24),
                               ('construction_countable_reordering', 'ConstructionCountableReordering', 8),
                               ('construction_reordered_descent', 'ConstructionReorderedDescent', 6),
                               ('construction_countable_alignments', 'ConstructionCountableAlignments', 20),
                               ('construction_germ_cosets', 'ConstructionGermCosets', 53),
                               ('construction_countable_quotient', 'ConstructionCountableQuotient', 4),
                               ('construction_countable_germs', 'ConstructionCountableGerms', 6),
                               ('construction_germ_detectors', 'ConstructionGermDetectors', 38),
                               ('construction_germ_detector_sites', 'ConstructionGermDetectorSites', 19),
                               ('construction_germ_separation', 'ConstructionGermSeparation', 17),
                               ('construction_cohen_fill', 'ConstructionCohenFill', 11),
                               ('construction_germ_complete', 'ConstructionGermComplete', 13),
                               ('construction_cohen_fusion', 'ConstructionCohenFusion', 13),
                               ('construction_cohen_separation', 'ConstructionCohenSeparation', 15),
                               ('construction_cohen_pair_separation', 'ConstructionCohenPairSeparation', 15),
                               ('construction_germ_bounded_rows', 'ConstructionGermBoundedRows', 9),
                               ('construction_cohen_rows', 'ConstructionCohenRows', 17),
                               ('construction_germ_eventual', 'ConstructionGermEventual', 36),
                               ('construction_germ_raw_pattern', 'ConstructionGermRawPattern', 31),
                               ('construction_germ_pattern_congruence', 'ConstructionGermPatternCongruence', 9),
                               ('construction_germ_pattern', 'ConstructionGermPattern', 19),
                               ('construction_germ_pattern_injectivity', 'ConstructionGermPatternInjectivity', 5),
                               ('construction_germ_good_dense', 'ConstructionGermGoodDense', 8),
                               ('construction_germ_pattern_stability', 'ConstructionGermPatternStability', 17),
                               ('construction_germ_row_covariance', 'ConstructionGermRowCovariance', 18),
                               ('construction_germ_left_action', 'ConstructionGermLeftAction', 18),
                               ('construction_germ_pattern_covariance', 'ConstructionGermPatternCovariance', 15),
                               ('construction_germ_least_bound', 'ConstructionGermLeastBound', 32),
                               ('construction_germ_best_coset', 'ConstructionGermBestCoset', 18),
                               ('construction_germ_pattern_order', 'ConstructionGermPatternOrder', 20),
                               ('construction_germ_selected', 'ConstructionGermSelected', 31),
                               ('construction_germ_condition_selector', 'ConstructionGermConditionSelector', 17),
                               ('construction_concrete_selector', 'ConstructionConcreteSelector', 22),
                               ('forcing_assignment_covariance', 'ForcingAssignmentCovariance', 8),
                               ('forcing_assignment_invariant', 'ForcingAssignmentInvariant', 6),
                               ('forcing_assignment_cosets', 'ForcingAssignmentCosets', 5),
                               ('forcing_germ_corrected', 'ForcingGermCorrected', 16),
                               ('forcing_germ_corrected_stability', 'ForcingGermCorrectedStability', 8),
                               ('forcing_germ_corrected_congruence', 'ForcingGermCorrectedCongruence', 4),
                               ('forcing_germ_corrected_equality', 'ForcingGermCorrectedEquality', 5),
                               ('forcing_germ_corrected_permutation', 'ForcingGermCorrectedPermutation', 4),
                               ('forcing_germ_corrected_descent', 'ForcingGermCorrectedDescent', 4),
                               ('forcing_forced_availability_transport', 'ForcingForcedAvailabilityTransport', 8),
                               ('forcing_stable_at', 'ForcingStableAt', 10),
                               ('forcing_germ_corrected_stable', 'ForcingGermCorrectedStable', 5),
                               ('forcing_germ_corrected_density', 'ForcingGermCorrectedDensity', 9),
                               ('forcing_germ_corrected_onto', 'ForcingGermCorrectedOnto', 5),
                               ('forcing_orbit_assignment', 'ForcingOrbitAssignment', 30),
                               ('forcing_orbit_permutation', 'ForcingOrbitPermutation', 4),
                               ('forcing_orbit_congruence', 'ForcingOrbitCongruence', 4),
                               ('forcing_orbit_descent', 'ForcingOrbitDescent', 4),
                               ('forcing_orbit_stable', 'ForcingOrbitStable', 4),
                               ('forcing_orbit_equality', 'ForcingOrbitEquality', 5),
                               ('forcing_orbit_quotient', 'ForcingOrbitQuotient', 31),
                               ('forcing_orbit_representatives', 'ForcingOrbitRepresentatives', 9),
                               ('forcing_orbit_chains', 'ForcingOrbitChains', 8),
                               ('forcing_orbit_density', 'ForcingOrbitDensity', 5),
                               ('forcing_orbit_onto', 'ForcingOrbitOnto', 4),
                               ('forcing_orbit_index', 'ForcingOrbitIndex', 4),
                               ('forcing_orbit_counts', 'ForcingOrbitCounts', 9),
                               ('forcing_orbit_representative_density', 'ForcingOrbitRepresentativeDensity', 9),
                               ('forcing_assigned', 'ForcingAssigned', 24),
                               ('forcing_assigned_equality', 'ForcingAssignedEquality', 4),
                               ('forcing_assigned_density', 'ForcingAssignedDensity', 8),
                               ('forcing_assigned_transport', 'ForcingAssignedTransport', 8),
                               ('forcing_assigned_laws', 'ForcingAssignedLaws', 8),
                               ('forcing_assigned_stable', 'ForcingAssignedStable', 4),
                               ('forcing_orbit_code_parameters', 'ForcingOrbitCodeParameters', 8),
                               ('construction_selector_presentation', 'ConstructionSelectorPresentation', 4),
                               ('forcing_orbit_parameter_record', 'ForcingOrbitParameterRecord', 8),
                               ('forcing_orbit_parameter_family', 'ForcingOrbitParameterFamily', 12),
                               ('forcing_assigned_parameter_fields', 'ForcingAssignedParameterFields', 19),
                               ('forcing_assigned_parameters', 'ForcingAssignedParameters', 12),
                               ('forcing_assigned_parameter_construction', 'ForcingAssignedParameterConstruction', 4),
                               ('forcing_forced_availability_congruence', 'ForcingForcedAvailabilityCongruence', 5),
                               ('forcing_assigned_ideal', 'ForcingAssignedIdeal', 4),
                               ('forcing_label_vertices', 'ForcingLabelVertices', 14),
                               ('forcing_assigned_extension', 'ForcingAssignedExtension', 4),
                               ('forcing_assigned_compatibility', 'ForcingAssignedCompatibility', 10),
                               ('forcing_assigned_graph', 'ForcingAssignedGraph', 18),
                               ('forcing_ordered_pair_name', 'ForcingOrderedPairName', 23),
                               ('forcing_product_entries', 'ForcingProductEntries', 16),
                               ('forcing_ordered_pair_forcing', 'ForcingOrderedPairForcing', 11),
                               ('forcing_relation_graph', 'ForcingRelationGraph', 14),
                               ('forcing_relation_graph_support', 'ForcingRelationGraphSupport', 14),
                               ('forcing_relation_graph_forcing', 'ForcingRelationGraphForcing', 21),
                               ('forcing_pair_formula', 'ForcingPairFormula', 9),
                               ('forcing_relation_graph_application', 'ForcingRelationGraphApplication', 7),
                               ('forcing_relation_graph_functions', 'ForcingRelationGraphFunctions', 19),
                               ('forcing_assigned_relation', 'ForcingAssignedRelation', 8),
                               ('forcing_quotient_name', 'ForcingQuotientName', 22),
                               ('forcing_assigned_graph_bounds', 'ForcingAssignedGraphBounds', 6),
                               ('forcing_assigned_graph_move', 'ForcingAssignedGraphMove', 5),
                               ('forcing_label_separation', 'ForcingLabelSeparation', 7),
                               ('forcing_assigned_graph_one', 'ForcingAssignedGraphOne', 4),
                               ('forcing_assigned_graph_inj', 'ForcingAssignedGraphInj', 4),
                               ('forcing_assigned_graph_total', 'ForcingAssignedGraphTotal', 8),
                               ('construction_ideal_stability', 'ConstructionIdealStability', 8),
                               ('forcing_forced_availability_stable', 'ForcingForcedAvailabilityStable', 5),
                               ('forcing_assigned_graph_onto', 'ForcingAssignedGraphOnto', 4),
                               ('forcing_assigned_graph_bijection', 'ForcingAssignedGraphBijection', 6),
                               ('forcing_concrete_quotient_bijection', 'ForcingConcreteQuotientBijection', 6),
                                ('forcing_check_ordinal', 'ForcingCheckOrdinal', 14),
                                ('forcing_uniform_inverse', 'ForcingUniformInverse', 25),
                                ('forcing_uniform_inverse_graph', 'ForcingUniformInverseGraph', 22),
                                ('forcing_outside_class_set', 'ForcingOutsideClassSet', 10),
                                ('forcing_assigned_parent_system', 'ForcingAssignedParentSystem', 9),
                                ('forcing_nonwellorderable_quotient', 'ForcingNonwellorderableQuotient', 8),
                                ('forcing_concrete_system', 'ForcingConcreteSystem', 15),
                                ('forcing_kernel_image', 'ForcingKernelImage', 45),
                                ('forcing_image_quotient', 'ForcingImageQuotient', 17),
                                ('forcing_map_calculus', 'ForcingMapCalculus', 38),
                                ('forcing_nonwellorderable_image', 'ForcingNonwellorderableImage', 12),
                                ('forcing_choice_failure', 'ForcingChoiceFailure', 21),
                                ('forcing_root_probes', 'ForcingRootProbes', 13),
                                ('forcing_ordinal_choice', 'ForcingOrdinalChoice', 16),
                                ('forcing_witness_placement', 'ForcingWitnessPlacement', 14),
                                ('forcing_localized_existential', 'ForcingLocalizedExistential', 7),
                                ('forcing_maximal_antichain', 'ForcingMaximalAntichain', 32),
                                ('forcing_localized_maximum', 'ForcingLocalizedMaximum', 14),
                                ('forcing_indexed_graph', 'ForcingIndexedGraph', 36),
                                ('forcing_ground_family_choice', 'ForcingGroundFamilyChoice', 13),
                                ('forcing_actual_ordinal_choice', 'ForcingActualOrdinalChoice', 10),
                                ('forcing_default_relation', 'ForcingDefaultRelation', 26),
                                ('forcing_completion_graph', 'ForcingCompletionGraph', 35),
                                ('forcing_partial_orbit_graph', 'ForcingPartialOrbitGraph', 24),
                                ('forcing_presentation_family', 'ForcingPresentationFamily', 27),
                                ('forcing_presentation_cover', 'ForcingPresentationCover', 10),
                                ('forcing_subset_image', 'ForcingSubsetImage', 12),
                                ('forcing_least_occurrence', 'ForcingLeastOccurrence', 18),
                                ('forcing_ordered_sections', 'ForcingOrderedSections', 15),
                                ('forcing_least_relation', 'ForcingLeastRelation', 36),
                                ('forcing_indexed_image', 'ForcingIndexedImage', 17),
                                ('forcing_uniform_maximum', 'ForcingUniformMaximum', 17),
                                ('forcing_section_injection', 'ForcingSectionInjection', 28),
                                ('forcing_wellordered_target', 'ForcingWellorderedTarget', 14),
                                ('forcing_slice_selection', 'ForcingSliceSelection', 19),
                                ('forcing_slice_geometry', 'ForcingSliceGeometry', 40),
                                ('forcing_slice_graphs', 'ForcingSliceGraphs', 22),
                                ('forcing_slice_coverage', 'ForcingSliceCoverage', 18),
                                ('forcing_empty_domain', 'ForcingEmptyDomain', 17),
                                ('forcing_slice_parameters', 'ForcingSliceParameters', 11),
                                ('forcing_slice_candidate', 'ForcingSliceCandidate', 12),
                                ('forcing_slice_assembly', 'ForcingSliceAssembly', 18),
                                ('forcing_slice_presentation', 'ForcingSlicePresentation', 5),
                                ('forcing_reverse_injection', 'ForcingReverseInjection', 5),
                                ('forcing_target_theory', 'ForcingTargetTheory', 7),
                                ('schema_axiom_assembly', 'SchemaAxiomAssembly', 17),
                                ('schema_axiom_compilation', 'SchemaAxiomCompilation', 29),
                                ('schema_closure_typing', 'SchemaClosureTyping', 19),
                                ('schema_shell_typing', 'SchemaShellTyping', 11),
                                ('schema_axiom_unique', 'SchemaAxiomUnique', 17),
                                ('original_axiom_code_test', 'OriginalAxiomCodeTest', 51),
                                ('project_compiler_quotation', 'ProjectCompilerQuotation', 5),
                                ('schema_closure_quotation', 'SchemaClosureQuotation', 14),
                                ('schema_template_quotation', 'SchemaTemplateQuotation', 12),
                                ('schema_index_quotation', 'Internal.SchemaIndexQuotation', 6),
                                ('index_image_quotation', 'Internal.IndexImageQuotation', 2),
                                ('native_index_formula_quotation', 'Internal.NativeIndexFormulaQuotation', 8),
                                ('project_native_renaming', 'ProjectNativeRenaming', 5),
                                ('schema_matrix_quotation', 'SchemaMatrixQuotation', 7),
                                ('schema_axiom_quotation', 'SchemaAxiomQuotation', 6),
                                ('original_axiom_typing', 'OriginalAxiomTyping', 6),
                                ('internal_consistency_closing', 'InternalConsistency', 8),
                                ('internal_axiom_proof', 'InternalAxiomProof', 5),
                                ('forcing_atomic_code', 'ForcingAtomicCode', 28),
                                ('forcing_atom_code', 'ForcingAtomCode', 15),
                                ('forcing_condition_rebind', 'ForcingConditionRebind', 19),
                                ('forcing_guard_code', 'ForcingGuardCode', 21)):
        adapter_lock = source_lock["source_proof_adaptations"][key]
        retained_entries = list(adapter_lock.get("retained_existing_producers", []))
        if "retained_existing_producer" in adapter_lock:
            retained_entries.append(adapter_lock["retained_existing_producer"])
        for retained in retained_entries:
            producer_path = ROOT / retained["producer_file"]
            if source_sha256(producer_path) != retained["producer_sha256"]:
                raise RuntimeError("Existing retained producer source changed")
            producer = producer_path.read_text(encoding="utf-8")
            selected = producer[producer.index(retained["source_start"]):producer.index(retained["source_end"], producer.index(retained["source_start"]))]
            for original, adapted in retained["replacements"]:
                if selected.count(original) != 1:
                    raise RuntimeError("Retained producer adaptation is ambiguous")
                selected = selected.replace(original, adapted, 1)
            target_body = (ROOT / adapter_lock["adapter"]).read_text(encoding="utf-8")
            actual = target_body[target_body.index(retained["target_start"]):target_body.index(retained["target_end"], target_body.index(retained["target_start"]))]
            if selected.strip() != actual.strip() or hashlib.sha256(actual.strip().encode()).hexdigest() != retained["normalized_body_sha256"]:
                raise RuntimeError("Retained producer proof differs beyond exact output-certificate packaging")

        if "native_source_file" in adapter_lock:
            native_path = ROOT / adapter_lock["native_source_file"]
            if source_sha256(native_path) != adapter_lock["native_source_sha256"]:
                raise RuntimeError("Native condition-graph constructor source changed")
        if source_lock["files"][adapter_lock["source_file"]] != adapter_lock["source_sha256"]:
            raise RuntimeError("Original condition-map source lock changed")
        for extra_source, extra_digest in adapter_lock.get("additional_source_sha256", {}).items():
            if source_lock["files"][extra_source] != extra_digest:
                raise RuntimeError("Additional forcing source lock changed: " + extra_source)
        for native_file, native_digest in adapter_lock.get("certificate_source_files", {}).items():
            if source_sha256(ROOT / native_file) != native_digest:
                raise RuntimeError("Native certificate source changed: " + native_file)
        for axiom in adapter_lock.get("additional_native_certificate_axioms", []):
            if "`" + axiom not in (ROOT / "Check.lean").read_text(encoding="utf-8"):
                raise RuntimeError("Missing inherited certificate reevaluation: " + axiom)
        body = strip_comments((ROOT / adapter_lock["adapter"]).read_text(encoding="utf-8"))
        prefix = "PPAC.Migration." + module + "."
        if module == "ExistingLChoiceBridge":
            prefix = "YesMetaZFC.SetTheory.ZFC."
        names = {prefix + n for n in re.findall(
            r"^(?:def|theorem|abbrev|structure)\s+([A-Za-z_][A-Za-z_0-9]*)", body, re.MULTILINE)}
        if module in ("ExistingFiniteSequenceBounds", "ExistingOrdinalEnumeration", "ExistingOrdinalImage", "ExistingIndexedChoice", "ConstructionCountableHull", "ForcingChainBound", "ForcingCountableTreeEvaluation", "ForcingCountableTreeAlgebra", "ExistingTreeAddresses", "ForcingCountableTreeCodes", "ForcingCountableTreeGraft", "ForcingCountableTreeCardinality", "ForcingCountableTreeValues", "ForcingCountableTreeGraftValues", "ForcingCountableHull", "ForcingCohenCodes", "ForcingCohenCompatibleChoice", "ForcingCohenRestriction", "ForcingCohenFlip", "ForcingCohenOperation", "ForcingCohenAntichain"):
            names |= {prefix + n + "_freeClosed" for n in re.findall(r"^derive_free_closed\s+(\w+)", body, re.MULTILINE)}
        if module == "ForcingFormula":
            names |= {prefix + "Basic"} | {prefix + "Basic." + n for n in ("bot", "mem", "equal", "conj", "neg", "ex", "rec")}
        if module == "ForcingNameRecursion":
            names |= {prefix + "OperatorFacts." + n for n in ("mk", "total", "unique", "child_congr")}
        if len(names) != count or names != set(adapter_lock["exact_declaration_footprints"]) or not names <= set(expected):
            raise RuntimeError("Incomplete condition-map declaration audit: " + module)
        map_recursion_footprints.update(adapter_lock["exact_declaration_footprints"])
    l_reuse = source_lock["companion_reuse"]["native_internal_L"]
    l_manifest_path = ROOT / l_reuse["manifest"]
    if source_sha256(l_manifest_path) != l_reuse["manifest_sha256"]:
        raise RuntimeError("Native L reuse manifest changed")
    l_manifest = json.loads(l_manifest_path.read_text(encoding="utf-8"))
    if len(l_manifest["proof_modules"]) != 140 or len(l_manifest["exact_declaration_footprints"]) != 2818:
        raise RuntimeError("Incomplete actual L dependency/declaration slice")
    l_paths = set()
    for entry in l_manifest["proof_modules"]:
        target = ROOT / entry["adapter"]
        if source_sha256(target) != entry["adapter_sha256"]:
            raise RuntimeError("Reused L adapter changed: " + entry["adapter"])
        normalized = re.sub(r"^import\s+.*\n", "", target.read_text(encoding="utf-8"), flags=re.MULTILINE)
        if hashlib.sha256(normalized.encode("utf-8")).hexdigest() != entry["normalized_nonimport_body_sha256"]:
            raise RuntimeError("Reused L mathematical proof body changed: " + entry["adapter"])
        l_paths.add(target.resolve())
    if l_paths != {f.resolve() for f in (ROOT / "PPAC/Companion").rglob("*.lean")}:
        raise RuntimeError("Unreviewed or missing companion L proof module")
    for name, digest in (l_manifest["native_existing_dependency_files"] | l_manifest["auxiliary_files"]).items():
        if source_sha256(ROOT / name) != digest:
            raise RuntimeError("Native L dependency/notice changed: " + name)
    if not set(l_manifest["exact_declaration_footprints"]) <= set(expected):
        raise RuntimeError("Incomplete L public/generated declaration audit")
    map_recursion_footprints.update(l_manifest["exact_declaration_footprints"])
    fseq_reuse = source_lock["companion_reuse"]["native_finite_sequence_bound"]
    fseq_text = (ROOT / fseq_reuse["adapter"]).read_text(encoding="utf-8")
    fseq_blocks = {m[1]: m[2].strip() for m in re.finditer(
        r"(?ms)^-- BEGIN DONOR ([A-Za-z0-9_.]+)\n(.*?)^-- END DONOR \1\n", fseq_text)}
    if {k: hashlib.sha256(v.encode("utf-8")).hexdigest() for k, v in fseq_blocks.items()} != fseq_reuse["literal_blocks_sha256"]:
        raise RuntimeError("Reused donor finite-sequence proof bodies changed")
    cardinal_reuse = source_lock["companion_reuse"]["native_infinite_union"]
    cardinal_text = (ROOT / cardinal_reuse["adapter"]).read_text(encoding="utf-8")
    cardinal_blocks = {m[1]: m[2].strip() for m in re.finditer(
        r"(?ms)^-- BEGIN DONOR ([A-Za-z0-9_.]+)\n(.*?)^-- END DONOR \1\n", cardinal_text)}
    if {k: hashlib.sha256(v.encode("utf-8")).hexdigest() for k, v in cardinal_blocks.items()} != cardinal_reuse["literal_blocks_sha256"]:
        raise RuntimeError("Reused donor cardinal proof bodies changed")
    small_union_reuse = source_lock["companion_reuse"]["native_small_family_union"]
    small_union_text = (ROOT / small_union_reuse["adapter"]).read_text(encoding="utf-8")
    small_union_blocks = {m[1]: m[2].strip() for m in re.finditer(
        r"(?ms)^-- BEGIN DONOR ([A-Za-z0-9_.]+)\n(.*?)^-- END DONOR \1\n", small_union_text)}
    if {k: hashlib.sha256(v.encode("utf-8")).hexdigest() for k, v in small_union_blocks.items()} != small_union_reuse["literal_blocks_sha256"]:
        raise RuntimeError("Reused donor internal small-family union proof bodies changed")
    ordinal_reuse = source_lock["companion_reuse"]["native_ordinal_enumeration"]
    ordinal_text = (ROOT / ordinal_reuse["adapter"]).read_text(encoding="utf-8")
    ordinal_blocks = {m[1]: m[2].strip() for m in re.finditer(
        r"(?ms)^-- BEGIN DONOR ([A-Za-z0-9_.]+)\n(.*?)^-- END DONOR \1\n", ordinal_text)}
    if {k: hashlib.sha256(v.encode("utf-8")).hexdigest() for k, v in ordinal_blocks.items()} != ordinal_reuse["literal_blocks_sha256"]:
        raise RuntimeError("Reused donor internal ordinal enumeration proof bodies changed")
    indexed_reuse = source_lock["companion_reuse"]["native_indexed_choice"]
    if indexed_reuse["commit"] != "79793365c2145c53db37eaf8ab23a64826bd9738":
        raise RuntimeError("Indexed choice donor revision changed")
    indexed_expected = ""
    for block in indexed_reuse["blocks"]:
        path = ROOT / block["donor_file"]
        if source_sha256(path) != block["donor_sha256"]:
            raise RuntimeError("Indexed choice donor source changed")
        source = path.read_text(encoding="utf-8")
        start = source.index(block["start_marker"])
        selected = source[start:source.index(block["end_marker"], start)]
        if hashlib.sha256(selected.encode()).hexdigest() != block["selected_source_sha256"]:
            raise RuntimeError("Indexed choice source slice changed")
        for original, adapted in block["replacements"]:
            selected = selected.replace(original, adapted)
        if hashlib.sha256(selected.encode()).hexdigest() != block["normalized_selected_sha256"]:
            raise RuntimeError("Indexed choice reference adaptation changed")
        indexed_expected += selected
    indexed_target = (ROOT / indexed_reuse["adapter"]).read_text(encoding="utf-8")
    indexed_actual = indexed_target[indexed_target.index(indexed_reuse["actual_body_start"]):
        indexed_target.index(indexed_reuse["actual_body_end"])]
    if indexed_actual != indexed_expected or hashlib.sha256(indexed_actual.encode()).hexdigest() != indexed_reuse["normalized_body_sha256"]:
        raise RuntimeError("Indexed choice mathematical proof body changed beyond exact adaptations")
    if re.findall(r"^import (.+)$", indexed_target, re.MULTILINE) != indexed_reuse["exact_imports"]:
        raise RuntimeError("Indexed choice adapter imports changed")
    successor_reuse = source_lock["companion_reuse"]["native_successor_regularity"]
    if successor_reuse["commit"] != "79793365c2145c53db37eaf8ab23a64826bd9738":
        raise RuntimeError("Successor regularity donor revision changed")
    for module, reuse in successor_reuse["modules"].items():
        donor_path = ROOT / reuse["donor_file"]
        if source_sha256(donor_path) != reuse["donor_sha256"]:
            raise RuntimeError("Successor regularity donor source changed: " + module)
        donor = donor_path.read_text(encoding="utf-8")
        namespace = reuse["donor_namespace"]
        body = donor[donor.index("namespace " + namespace):]
        prefix = "namespace PPAC.Migration." + module + "\nopen YesMetaZFC SetTheory"
        if module == "ExistingSuccessorRegularity":
            prefix += "\nopen ExistingSmallUnion (models_zf_l union_bound_l)"
        body = body.replace("namespace " + namespace, prefix, 1).replace(
            "end " + namespace, "end PPAC.Migration." + module)
        for original, adapted in reuse["replacements"]:
            body = body.replace(original, adapted)
        target = (ROOT / reuse["adapter"]).read_text(encoding="utf-8")
        if target[target.index("namespace PPAC.Migration." + module):] != body:
            raise RuntimeError("Successor regularity proof differs beyond explicit path adaptations: " + module)
        if hashlib.sha256(body.encode("utf-8")).hexdigest() != reuse["normalized_donor_body_sha256"]:
            raise RuntimeError("Successor regularity normalized proof hash mismatch")
        if re.findall(r"^import (.+)$", target, re.MULTILINE) != reuse["exact_imports"]:
            raise RuntimeError("Successor regularity adapter imports changed")
    normalized_enum = ordinal_blocks["Choice.OrdinalEnumeration"].replace(
        "exists_hartogsNumber_kernel hZF I S", "ZF.exists_hartogsNumber hZF I S")
    if hashlib.sha256(normalized_enum.encode("utf-8")).hexdigest() != ordinal_reuse["original_donor_block_sha256"]:
        raise RuntimeError("Ordinal enumeration deviates from original donor body")
    native_block = re.search(r"(?ms)^-- BEGIN NATIVE Hartogs.Exists\n(.*?)^-- END NATIVE Hartogs.Exists\n", ordinal_text)[1].strip()
    if hashlib.sha256(native_block.encode("utf-8")).hexdigest() != ordinal_reuse["native_hartogs_adapter_block_sha256"]:
        raise RuntimeError("Kernel-checked Hartogs adapter proof changed")
    normalized_hartogs = native_block.replace("theorem exists_hartogsNumber_kernel\n", "theorem exists_hartogsNumber\n").replace(
        "    exact hZF.1.eq_of_same_members first second\n      (fun x => (hFirstSuccessor x).trans (hSecondSuccessor x).symm)", "    prove_auto")
    native_hartogs_text = (ROOT / ".lake/packages/YesMetaZFC/YesMetaZFC/SetTheory/Card/Aleph/Hartogs.lean").read_text(encoding="utf-8")
    original_hartogs = native_hartogs_text.split("theorem exists_hartogsNumber\n", 1)[1].split("\nend ZF", 1)[0]
    original_hartogs = ("theorem exists_hartogsNumber\n" + original_hartogs).strip()
    if normalized_hartogs != original_hartogs or hashlib.sha256(original_hartogs.encode("utf-8")).hexdigest() != ordinal_reuse["native_hartogs_original_block_sha256"]:
        raise RuntimeError("Hartogs proof differs beyond the one explicit successor-extensionality step")
    for name, digest in cardinal_reuse["certificate_source_files"].items():
        if source_sha256(ROOT / ".lake/packages/YesMetaZFC" / name) != digest:
            raise RuntimeError("Pinned cardinal certificate source changed")
    for name in cardinal_reuse["additional_native_certificate_axioms"]:
        if "`" + name not in (ROOT / "Check.lean").read_text(encoding="utf-8"):
            raise RuntimeError("Missing cardinal certificate reevaluation: " + name)
    interpreted_body = strip_comments((ROOT / "PPAC/Migration/InterpretedZF.lean").read_text(encoding="utf-8"))
    interpreted_names = {"PPAC.Migration.InterpretedZF." + n for n in
                         re.findall(r"^theorem\s+([A-Za-z_][A-Za-z_0-9]*)", interpreted_body, re.MULTILINE)}
    if len(interpreted_names) != 4 or not interpreted_names <= set(expected):
        raise RuntimeError("Incomplete interpreted full-ZF declaration audit")
    # The existing semantics/completeness bridge is reused with the exact ZF
    # background, not the concrete ZFC expansion. Audit every added declaration.
    model_transfer_body = strip_comments((ROOT / "PPAC/Migration/ModelTransfer.lean").read_text(encoding="utf-8"))
    model_transfer_names = {"PPAC.Migration.ModelTransfer." + n for n in
                            re.findall(r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)", model_transfer_body, re.MULTILINE)}
    if not model_transfer_names or not model_transfer_names <= set(expected):
        raise RuntimeError("Incomplete model transfer declaration audit")
    minima_body = strip_comments((ROOT / "PPAC/Migration/DefinableMinimaChoice.lean").read_text(encoding="utf-8"))
    minima_names = {"PPAC.Migration.DefinableMinimaChoice." + n for n in
                    re.findall(r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)", minima_body, re.MULTILINE)}
    if not minima_names or not minima_names <= set(expected):
        raise RuntimeError("Incomplete definable minima choice audit")
    for module in ("KuratowskiZF", "InternalWellOrderChoice"):
        bridge_body = strip_comments((ROOT / "PPAC/Migration" / (module + ".lean")).read_text(encoding="utf-8"))
        bridge_names = {"PPAC.Migration." + module + "." + n for n in
                        re.findall(r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)", bridge_body, re.MULTILINE)}
        if not bridge_names or not bridge_names <= set(expected):
            raise RuntimeError("Incomplete internal order bridge audit: " + module)
    # Existing constructible syntax is a literal dependency slice; guard its
    # original bodies independently of the new output construction proof.
    syntax_lock = json.loads((ROOT / "docs/SOURCE_LOCK.json").read_text(encoding="utf-8"))["companion_reuse"]["godel_def_syntax"]
    syntax_text = (ROOT / syntax_lock["adapter"]).read_text(encoding="utf-8")
    literal_blocks = {m[1]: m[2].strip() for m in re.finditer(
        r"(?ms)^-- BEGIN ORIGINAL ([A-Za-z0-9_.]+)\n(.*?)^-- END ORIGINAL \1\n", syntax_text)}
    if set(literal_blocks) != set(syntax_lock["declarations"]):
        raise RuntimeError("Incomplete original constructible syntax slice")
    for original, body in literal_blocks.items():
        if hashlib.sha256(body.encode("utf-8")).hexdigest() != syntax_lock["declarations"][original]["body_sha256"]:
            raise RuntimeError("Original constructible declaration changed: " + original)
    syntax_names = {syntax_lock["namespace_prefix"] + n for n in literal_blocks}
    output_body = strip_comments((ROOT / syntax_lock["proof"]).read_text(encoding="utf-8"))
    output_names = {"PPAC.Migration.GodelDefOutput." + n for n in
                    re.findall(r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)", output_body, re.MULTILINE)}
    if not (syntax_names | output_names) <= set(expected):
        raise RuntimeError("Incomplete fixed Godel Def output declaration audit")
    history_names = {"PPAC.Migration.ConstructibleHistory." + n for n in re.findall(
        r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)",
        strip_comments((ROOT / syntax_lock["history_adapter"]).read_text(encoding="utf-8")), re.MULTILINE)}
    if history_names != set(syntax_lock["history_exact_declaration_footprints"]) or not history_names <= set(expected):
        raise RuntimeError("Incomplete original constructible history audit")
    # Reuse the pinned internal three-way recursion, with exact inherited native certificates.
    recursion_lock = json.loads((ROOT / "docs/SOURCE_LOCK.json").read_text(encoding="utf-8"))["companion_reuse"]["native_godel_recursion"]
    for source, digest in recursion_lock["sources"].items():
        if source_sha256(ROOT / ".lake/packages/YesMetaZFC" / source) != digest:
            raise RuntimeError("Pinned native recursion source changed: " + source)
    recursion_names = {"PPAC.Migration.GodelDefRecursion." + n for n in re.findall(
        r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)",
        strip_comments((ROOT / recursion_lock["adapter"]).read_text(encoding="utf-8")), re.MULTILINE)}
    if recursion_names != set(recursion_lock["exact_declaration_footprints"]) or not recursion_names <= set(expected):
        raise RuntimeError("Incomplete native Godel recursion declaration audit")
    parameter_lock = json.loads((ROOT / "docs/SOURCE_LOCK.json").read_text(encoding="utf-8"))["companion_reuse"]["canonical_constructible_parameters"]
    parameter_names = {"PPAC.Migration.ConstructibleParameters." + n for n in re.findall(
        r"^(?:def|theorem)\s+([A-Za-z_][A-Za-z_0-9]*)",
        strip_comments((ROOT / parameter_lock["adapter"]).read_text(encoding="utf-8")), re.MULTILINE)}
    if parameter_names != set(parameter_lock["exact_declaration_footprints"]) or not parameter_names <= set(expected):
        raise RuntimeError("Incomplete canonical constructible parameter audit")
    # The independent compiler core may use proved numeric libraries, but cannot call
    # the legacy full formula judgment, step specification, operator or evaluator.
    formula_program_core_modules = ('FormulaAtomicProgramSyntax', 'FormulaTransformHistorySyntax', 'FormulaTransformAtomSyntax', 'FormulaTransformLogicalSyntax', 'FormulaTransformProgramSyntax', 'FormulaTransformOperatorSyntax', 'FormulaTransformRecursionSyntax', 'FormulaTransformEvaluationSyntax', 'FormulaTransformExecutionSyntax')
    legacy_formula_oracle = re.compile(r"SyntaxMixedFormula(?:Judgment|Recursive|Local|Operator|Recursion|Evaluation)(?:Syntax)?\.|SyntaxCodedMixedTermSyntax\.")
    for module in formula_program_core_modules:
        body = strip_comments((ROOT / "PPAC/Migration/Internal" / (module + ".lean")).read_text(encoding="utf-8-sig"))
        if legacy_formula_oracle.search(body):
            raise RuntimeError(f"Legacy judgment used as independent program primitive: {module}")
    # The compiled four-atom subprogram cannot call the original full trace or
    # a legacy substitution judgment as an execution primitive.
    atomic_core = strip_comments((ROOT / "PPAC/Migration/Internal/FormulaAtomicProgramSyntax.lean").read_text(encoding="utf-8-sig"))
    atomic_oracle = re.compile(r"OriginalTransformRowSyntax\.|OriginalAtomic\w*\.|Expr\.eval|SyntaxTransform\.|SyntaxMixedFormula\w*\.|SyntaxCodedMixedTermSyntax\.")
    for name in ("program", "run"):
        found = re.search(r"(?ms)^def " + name + r"\b.*?(?=^(?:def|theorem|abbrev|structure|inductive|end)\b|\Z)", atomic_core)
        if not found or atomic_oracle.search(found.group(0)):
            raise RuntimeError(f"Original/comparison oracle in independent atomic subprogram: {name}")
    # Strict lookup executes a real tail recursor and a partial Cons match;
    # it cannot use the old total-default field relation as an execution primitive.
    lookup_core = strip_comments((ROOT / "PPAC/Migration/Internal/StrictLookupSyntax.lean").read_text(encoding="utf-8-sig"))
    if re.search(r"StructuralListField(?:Syntax|Values)\.|SyntaxTransform\.lookup", lookup_core):
        raise RuntimeError("Legacy field/host lookup used as strict program primitive")
    # The table-code lookup program builds its own state sets and actual graphs.
    # Comparisons may cite the old judgment; the execution core cannot call it.
    lookup_table_core = ('LookupTableProgramSyntax', 'LookupTableOperatorSyntax', 'LookupTableRecursionSyntax', 'LookupTableEvaluationSyntax', 'LookupTableExecutionSyntax')
    lookup_table_oracle = re.compile(r"StrictLookup(?:\w*)\.|StructuralListField(?:\w*)\.|SyntaxTransform\.lookup")
    for module in lookup_table_core:
        body = strip_comments((ROOT / "PPAC/Migration/Internal" / (module + ".lean")).read_text(encoding="utf-8-sig"))
        if lookup_table_oracle.search(body):
            raise RuntimeError(f"Old lookup used as table-program primitive: {module}")
    # Compile the original Expr/Rule AST relationally; runtime values remain objects.
    # No host numeric evaluator or earlier full lookup judgment is an oracle.
    horn_core = ('HornExprSyntax', 'HornRuleSyntax')
    horn_oracle = re.compile(r"Expr\.eval|SyntaxTransform\.lookup\b|LookupTableExecutionSyntax\.|StrictLookupSyntax\.returned")
    for module in horn_core:
        body = strip_comments((ROOT / "PPAC/Migration/Internal" / (module + ".lean")).read_text(encoding="utf-8-sig"))
        if horn_oracle.search(body):
            raise RuntimeError(f"Host/legacy oracle used in original Horn compiler: {module}")
    # Original finite rule arities become actual object existential assignments.
    bounded_search_core = ('HornApplicationSyntax', 'HornStepSyntax', 'HornSearchSyntax')
    for module in bounded_search_core:
        body = strip_comments((ROOT / "PPAC/Migration/Internal" / (module + ".lean")).read_text(encoding="utf-8-sig"))
        if horn_oracle.search(body):
            raise RuntimeError(f"Host/legacy oracle used in bounded search compiler: {module}")
    # Inspect execution definitions, not the separate correctness/witness proofs.
    # The canonical Separation witness may use the proved program specification;
    # the independent trace condition and success graph cannot use that oracle.
    lookup_trace_execution_defs = {'HornLookupRowSyntax': ['row', 'existsRow'], 'HornLookupSoundSyntax': ['closed'], 'HornLookupConditionSyntax': ['witness', 'condition'], 'HornLookupSearchCondition': ['closed', 'witness', 'condition'], 'HornLookupSomeSyntax': ['returned', 'hasOutput', 'noOutput'], 'HornLookupPowerCondition': ['atPower', 'condition'], 'FreeReplaceResultSyntax': ['root', 'existsRoot', 'run', 'returned', 'guard', 'hasOutput', 'noOutput'], 'FreeWeakenValueSyntax': ['shifted', 'hasShifted'], 'FreeWeakenResultSyntax': ['root', 'existsRoot', 'run', 'returned', 'guard', 'hasOutput', 'noOutput'], 'OriginalTermTraceSyntax': ['root', 'existsRoot', 'run', 'metadata', 'inputGuard', 'checked'], 'HornUniversalTraceRules': ['tracedPremise', 'tracedPremises', 'tracedMatrix'], 'OriginalTransformRowSyntax': ['row', 'run'], 'OriginalArgumentCaseSyntax': ['nilData', 'consData', 'consBody', 'consCase', 'outcomes']}
    for module, declarations in lookup_trace_execution_defs.items():
        body = strip_comments((ROOT / "PPAC/Migration/Internal" / (module + ".lean")).read_text(encoding="utf-8-sig"))
        for declaration in declarations:
            found = re.search(r"(?ms)^def " + re.escape(declaration) + r"\b.*?(?=^(?:def|theorem|abbrev|structure|inductive|end)\b|\Z)", body)
            term_oracle = re.compile(r"OriginalScalarValues\.valueSpec|TermTransformProgramSyntax\.|SyntaxCodedMixedTermSyntax\.|SyntaxTransform\.(?:boundValue|freeValue)")
            if found is None or horn_oracle.search(found.group(0)) or (module in ("OriginalTermTraceSyntax", "HornUniversalTraceRules", "OriginalTransformRowSyntax", "OriginalArgumentCaseSyntax") and term_oracle.search(found.group(0))):
                raise RuntimeError(f"Legacy/host oracle in lookup trace definition: {module}.{declaration}")
    # The independent all-index field-image specification may call the term program,
    # but cannot define its answer using the original list run or its proofs.
    argument_field_image_oracle = re.compile(r"OriginalTransformRowSyntax\.|OriginalArgument(?:Field|Value|Program|Full|Candidate|Mode)\w*\.|HornLookupConditionSyntax\.|SyntaxTransform\.|SyntaxCodedMixedTermSyntax\.")
    argument_field_body = strip_comments((ROOT / "PPAC/Migration/Internal/ArgumentProgramFieldSyntax.lean").read_text(encoding="utf-8-sig"))
    for declaration in ("fields", "mapped"):
        found = re.search(r"(?ms)^def " + declaration + r"\b.*?(?=^(?:def|theorem|abbrev|structure|inductive|end)\b|\Z)", argument_field_body)
        if not found or argument_field_image_oracle.search(found.group(0)):
            raise RuntimeError(f"Original run/legacy oracle in independent argument field image: {declaration}")
    # Finite-forest and two-argument output specifications use only the independent term program.
    argument_forest_pair_defs = {"ArgumentForestProgramSyntax": ("typedInputs", "runs"), "ArgumentPairOutput": ("body", "output"), "ArgumentPairProgramSyntax": ("body", "returned")}
    for module, declarations in argument_forest_pair_defs.items():
        body = strip_comments((ROOT / "PPAC/Migration/Internal" / (module + ".lean")).read_text(encoding="utf-8-sig"))
        for declaration in declarations:
            found = re.search(r"(?ms)^def " + declaration + r"\b.*?(?=^(?:def|theorem|abbrev|structure|inductive|end)\b|\Z)", body)
            if not found or argument_field_image_oracle.search(found.group(0)) or re.search(r"FormulaTransform\w*Syntax\.", found.group(0)):
                raise RuntimeError(f"Original/legacy answer oracle in independent argument forest specification: {module}.{declaration}")
    # Member result specifications are independent of original formula runs and comparison premises.
    member_program_body = strip_comments((ROOT / "PPAC/Migration/Internal/MemberProgramSyntax.lean").read_text(encoding="utf-8-sig"))
    for declaration in ("body", "returned"):
        found = re.search(r"(?ms)^def " + declaration + r"\b.*?(?=^(?:def|theorem|abbrev|structure|inductive|end)\b|\Z)", member_program_body)
        if not found or re.search(r"OriginalTransformRowSyntax\.|OriginalFormula\w*\.|MemberPairAgreement\w*\.|HornLookupConditionSyntax\.|SyntaxTransform\.|SyntaxCodedMixedTermSyntax\.|FormulaTransform\w*Syntax\.", found.group(0)):
            raise RuntimeError(f"Original/legacy answer oracle in independent member program: {declaration}")
    # Formula application and local case formulas stay independent of legacy answers.
    formula_local_defs = {"OriginalFormulaApplicationSyntax": ("body", "application"), "OriginalFormulaLocalData": ("constant", "binary", "unary", "application"), "OriginalFormulaCaseSyntax": ("binaryBody", "binaryCase", "unaryBody", "unaryCase", "binderBody", "binderCase", "applicationBody", "applicationCase"), "OriginalFormulaTraceEquation": ("outcomes",), "OriginalFormulaMemberCaseSyntax": ("body", "membershipCase")}
    formula_local_oracle = re.compile(r"Expr\.eval|TermTransformProgramSyntax\.|FormulaTransform\w*Syntax\.|SyntaxCodedMixedTermSyntax\.|OriginalScalarValues\.valueSpec|SyntaxTransform\.(?:lookup|weaken|freeReplace|boundValue|freeValue)")
    for module, declarations in formula_local_defs.items():
        body = strip_comments((ROOT / "PPAC/Migration/Internal" / (module + ".lean")).read_text(encoding="utf-8-sig"))
        for declaration in declarations:
            found = re.search(r"(?ms)^def " + declaration + r"\b.*?(?=^(?:def|theorem|abbrev|structure|inductive|end)\b|\Z)", body)
            if not found or formula_local_oracle.search(found.group(0)):
                raise RuntimeError(f"Legacy/host oracle in pure numeric formula case: {module}.{declaration}")
    if source_check_only:
        # A fresh LF checkout can exercise every source/dependency guard without
        # requiring or trusting any local Lean build cache.
        subprocess.run([sys.executable, "scripts/check_source_rules.py"], cwd=ROOT, check=True)
        subprocess.run([sys.executable, "scripts/check_source_theory.py"], cwd=ROOT, check=True)
        print("PASS: source/dependency preflight (no Lean build or declaration audit); " + POLICY)
        return
    (OUT / "summary.json").unlink(missing_ok=True)
    run([sys.executable, "scripts/check_source_rules.py"], "source-rules.log")
    run([sys.executable, "scripts/check_source_theory.py"], "source-theory.log")
    version = run(["lake", "env", "lean", "--version"], "lean-version.log").strip()
    build = run(["lake", "--no-cache", "--wfail", "build"], "build.log")
    run(["lake", "env", "lean", "--trust=0", "Check.lean"], "check.log")
    if "Rechecked 15 pinned native recursion Bool certificates" not in (OUT / "check.log").read_text(encoding="utf-8"):
        raise RuntimeError("Inherited native recursion Bool checks were not executed")
    if "Rechecked 9 pinned native cardinal Bool certificates" not in (OUT / "check.log").read_text(encoding="utf-8"):
        raise RuntimeError("Inherited native cardinal Bool checks were not executed")
    if "Rechecked 6 pinned native sequence restriction Bool certificates" not in (OUT / "check.log").read_text(encoding="utf-8"):
        raise RuntimeError("Inherited native sequence restriction Bool checks were not executed")
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
    if source_sha256(choice_source) != choice_baseline["source_sha256"]:
        raise RuntimeError("Native-choice original source hash changed")
    contracts = {x for x in footprints if x.startswith("PPAC.Migration.target_derives_")} | {
        "PPAC.Migration.consistent_ZF_of_target", "PPAC.Migration.no_AC_of_target_consistent"}
    fixed_exact = fixed_axiom_expected_footprints(inherited)
    for name, dependencies in footprints.items():
        if name in map_recursion_footprints:
            if set(dependencies) != set(map_recursion_footprints[name]):
                raise RuntimeError("Unexpected condition-map dependency: " + name)
            continue
        if name in forcing_name_names:
            if set(dependencies) != set(forcing_name_lock["exact_declaration_footprints"][name]):
                raise RuntimeError("Unexpected original Child induction dependency: " + name)
            continue
        if name in names_names:
            if set(dependencies) != set(names_lock["exact_declaration_footprints"][name]):
                raise RuntimeError("Unexpected original IsName dependency: " + name)
            continue
        if name in eval_names:
            if set(dependencies) != set(eval_lock["exact_declaration_footprints"][name]):
                raise RuntimeError("Unexpected original evaluate dependency: " + name)
            continue
        if name in interpreted_names:
            if set(dependencies) != {"propext", "Quot.sound", "Classical.choice"} | inherited:
                raise RuntimeError("Unexpected interpreted-ZF dependency: " + name)
            continue
        if name.startswith("PPAC.Migration.ConstructibleParameters."):
            if set(dependencies) != set(parameter_lock["exact_declaration_footprints"].get(name, [])):
                raise RuntimeError("Unexpected canonical constructible parameter dependency: " + name)
            continue
        if name.startswith("PPAC.Migration.ConstructibleHistory."):
            if set(dependencies) != set(syntax_lock["history_exact_declaration_footprints"].get(name, [])):
                raise RuntimeError("Unexpected original constructible history dependency: " + name)
            continue
        if name.startswith("PPAC.Migration.GodelDefRecursion."):
            if set(dependencies) != set(recursion_lock["exact_declaration_footprints"].get(name, [])):
                raise RuntimeError("Unexpected native Godel recursion dependency: " + name)
            continue
        if name.startswith("PPAC.Migration.ExistingConstructible."):
            if not set(dependencies) <= {"propext", "Quot.sound"}:
                raise RuntimeError("Unexpected existing constructible syntax dependency: " + name)
            continue
        if name.startswith("PPAC.Migration.GodelDefOutput."):
            suffix = name.rsplit(".", 1)[1]
            native = {"exists_unique", "existence_models", "uniqueness_models",
                      "existence_kernel_certificate", "uniqueness_kernel_certificate",
                      "source_existence_certificate", "source_uniqueness_certificate"}
            data = {"toSource_rename", "evaluator", "output", "query", "existenceSentence",
                    "otherIndex", "uniquenessSentence"}
            expected_output = ({"propext", "Quot.sound"} if suffix in data else
                               set() if suffix == "toSource" else
                               {"propext", "Quot.sound", "Classical.choice"})
            if suffix in native:
                expected_output |= inherited
            if set(dependencies) != expected_output:
                raise RuntimeError("Unexpected fixed Godel Def output dependency: " + name)
            continue
        if name.startswith(("PPAC.Migration.KuratowskiZF.", "PPAC.Migration.InternalWellOrderChoice.")):
            expected_bridge = {"propext", "Quot.sound", "Classical.choice"}
            if name in {'PPAC.Migration.InternalWellOrderChoice.wellOrderCover', 'PPAC.Migration.InternalWellOrderChoice.graph', 'PPAC.Migration.InternalWellOrderChoice.projectCover'}:
                expected_bridge = {"propext", "Quot.sound"}
            elif name not in {'PPAC.Migration.KuratowskiZF.source_edge', 'PPAC.Migration.KuratowskiZF.source_code', 'PPAC.Migration.KuratowskiZF.source_pair'}:
                expected_bridge |= inherited
            if set(dependencies) != expected_bridge:
                raise RuntimeError("Unexpected internal order bridge dependency: " + name)
            continue
        if name.startswith("PPAC.Migration.DefinableMinimaChoice."):
            simple = {"propext", "Quot.sound", "Classical.choice"}
            closed = {"selector_models", "selector_kernel_certificate", "kernel_certificate",
                      "source_certificate", "relative_kernel_certificate"}
            suffix = name.rsplit(".", 1)[1]
            if suffix in {"least", "minimumPrinciple", "selected"}:
                if set(dependencies) != {"propext", "Quot.sound"}:
                    raise RuntimeError("Unexpected minima formula construction dependency: " + name)
            elif suffix in closed:
                if set(dependencies) != simple | inherited:
                    raise RuntimeError("Unexpected minima choice certificate dependency: " + name)
            elif not set(dependencies) <= simple:
                raise RuntimeError("Unexpected minima semantics dependency: " + name)
            continue
        if name.startswith("PPAC.Migration.ModelTransfer."):
            expected_model = {"propext", "Quot.sound", "Classical.choice"}
            if name != "PPAC.Migration.ModelTransfer.derives":
                expected_model |= inherited
            if set(dependencies) != expected_model:
                raise RuntimeError("Unexpected model transfer dependency: " + name)
            continue
        if name.startswith("PPAC.Migration.Relativization."):
            if not set(dependencies) <= {"propext", "Quot.sound", "Classical.choice"}:
                raise RuntimeError("Unexpected relativization dependency: " + name)
            continue
        if name in fixed_exact:
            if set(dependencies) != fixed_exact[name]: raise RuntimeError("Fixed axiom footprint changed: "+name)
            continue
        extra = set(dependencies) - allowed
        expected_extra = inherited if name in contracts else ({"Classical.choice"} if name.startswith("PPAC.Migration.Translation.") else set())
        is_step2 = any(name.startswith("PPAC.Migration." + prefix) for prefix in
            ["Syntax.", "Compile.", "FiniteSupport.", "TheoryTransport."]) or name in {
                # Prop AST equalities inherit the already-audited source-last/native-head bridge.
                "PPAC.Migration.PureSyntaxOperations.source_instantiate",
                "PPAC.Migration.PureSyntaxOperations.source_fresh_abstract"}
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
                    "PPAC.Migration.Internal.ObjectNaturalMultiplication.native_leftZero",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionAlgebra.native_leftSuccessor",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionAlgebra.native_commutative",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionAlgebra.native_associative",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionAlgebra.native_cancelRight",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionAlgebra.native_cancelLeft",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionOrder.native_bounds",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionOrder.native_zero",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionOrder.native_strictRight",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionOrder.native_strictLeft",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionReassociation.native_swap",
                    "PPAC.Migration.Internal.ObjectNaturalAdditionReassociation.native_interchange",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicationAlgebra.native_sumRight",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicationAlgebra.native_sumLeft",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicationAlgebra.native_leftSuccessor",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicationAlgebra.native_commutative",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicationAlgebra.native_associative",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicationAlgebra.native_unit",
                    "PPAC.Migration.Internal.ObjectNaturalOrder.native_total",
                    "PPAC.Migration.Internal.ObjectNaturalOrder.native_transitive",
                    "PPAC.Migration.Internal.ObjectNaturalOrder.native_antisymmetric",
                    "PPAC.Migration.Internal.ObjectNaturalOrder.native_successor",
                    "PPAC.Migration.Internal.ObjectNaturalDifference.native_order",
                    "PPAC.Migration.Internal.ObjectNaturalDifference.native_fiber",
                    "PPAC.Migration.Internal.ObjectNaturalDifference.native_strict",
                    "PPAC.Migration.Internal.ObjectNaturalDifference.native_zero",
                    "PPAC.Migration.Internal.ObjectNaturalAdditiveOrder.native_rightWeak",
                    "PPAC.Migration.Internal.ObjectNaturalAdditiveOrder.native_rightStrict",
                    "PPAC.Migration.Internal.ObjectNaturalAdditiveOrder.native_leftWeak",
                    "PPAC.Migration.Internal.ObjectNaturalAdditiveOrder.native_leftStrict",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder.native_zero",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder.native_rightMonotone",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder.native_rightWeak",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder.native_rightStrict",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder.native_rightCancel",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder.native_leftMonotone",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder.native_leftWeak",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder.native_leftStrict",
                    "PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder.native_leftCancel",
                    "PPAC.Migration.Internal.ObjectNaturalNumericBounds.native_unit",
                    "PPAC.Migration.Internal.ObjectNaturalNumericBounds.native_factors",
                    "PPAC.Migration.Internal.ObjectNaturalNumericBounds.native_square",
                    "PPAC.Migration.Internal.ObjectNaturalNumericBounds.native_squareStrict",
                    "PPAC.Migration.Internal.ObjectNaturalNumericBounds.native_squareInjective",
                    "PPAC.Migration.Internal.ObjectGodelPair.native_fiber",
                    "PPAC.Migration.Internal.ObjectGodelPair.native_closure",
                    "PPAC.Migration.Internal.ObjectGodelPair.native_valueUnique",
                    "PPAC.Migration.Internal.ObjectGodelPair.native_components",
                    "PPAC.Migration.Internal.ObjectGodelPair.native_injective",
                    "PPAC.Migration.Internal.ObjectGodelPair.native_lowerBand",
                    "PPAC.Migration.Internal.ObjectGodelPair.native_upperBand",
                    "PPAC.Migration.Internal.ObjectGodelUnpair.native_zero",
                    "PPAC.Migration.Internal.ObjectGodelUnpair.native_successor",
                    "PPAC.Migration.Internal.ObjectGodelUnpair.native_total",
                    "PPAC.Migration.Internal.ObjectGodelUnpair.native_characterization",
                    "PPAC.Migration.Internal.ObjectGodelUnpair.native_fiber",
                    "PPAC.Migration.Internal.ObjectGodelUnpair.native_bounded",
                    "PPAC.Migration.Internal.ObjectStructuralNode.native_encodeFiber",
                    "PPAC.Migration.Internal.ObjectStructuralNode.native_closure",
                    "PPAC.Migration.Internal.ObjectStructuralNode.native_positive",
                    "PPAC.Migration.Internal.ObjectStructuralNode.native_components",
                    "PPAC.Migration.Internal.ObjectStructuralNode.native_injective",
                    "PPAC.Migration.Internal.ObjectStructuralNode.native_positiveIff",
                    "PPAC.Migration.Internal.ObjectStructuralNode.native_decodeTotal",
                    "PPAC.Migration.Internal.ObjectStructuralNode.native_decodeFiber",
                    "PPAC.Migration.Internal.ObjectStructuralNode.native_decodeBounds",
                    "PPAC.Migration.Internal.ObjectStructuralList.native_nilValue",
                    "PPAC.Migration.Internal.ObjectStructuralList.native_nilFiber",
                    "PPAC.Migration.Internal.ObjectStructuralList.native_consTag",
                    "PPAC.Migration.Internal.ObjectStructuralList.native_consFiber",
                    "PPAC.Migration.Internal.ObjectStructuralList.native_closure",
                    "PPAC.Migration.Internal.ObjectStructuralList.native_bounds",
                    "PPAC.Migration.Internal.ObjectStructuralList.native_injective",
                    "PPAC.Migration.Internal.ObjectStructuralList.native_disjoint",
                    "PPAC.Migration.Internal.ObjectStructuralList.native_leafZero",
                    "PPAC.Migration.Internal.ObjectStructuralListTrace.native_base",
                    "PPAC.Migration.Internal.ObjectStructuralListTrace.native_append",
                    "PPAC.Migration.Internal.ObjectStructuralListTrace.native_nilValid",
                    "PPAC.Migration.Internal.ObjectStructuralListTrace.native_consValid",
                    "PPAC.Migration.Internal.ObjectStructuralListTrace.native_range",
                    "PPAC.Migration.Internal.ObjectStructuralListTrace.native_recursive",
                    "PPAC.Migration.Internal.ObjectStructuralListTrace.native_consIff",
                    "PPAC.Migration.Internal.ObjectStructuralListTrace.native_positive",
                    "PPAC.Migration.Internal.ObjectStructuralListTrace.native_zeroRejected",
                    "PPAC.Migration.Internal.ObjectStructuralListTrace.native_prefix",
                    "PPAC.Migration.Internal.ObjectStructuralListLength.native_prefixTrace",
                    "PPAC.Migration.Internal.ObjectStructuralListLength.native_knownTailEdge",
                    "PPAC.Migration.Internal.ObjectStructuralListLength.native_nilEmpty",
                    "PPAC.Migration.Internal.ObjectStructuralListLength.native_consPredecessor",
                    "PPAC.Migration.Internal.ObjectStructuralListLength.native_unique",
                    "PPAC.Migration.Internal.ObjectStructuralListLength.native_traceUnique",
                    "PPAC.Migration.Internal.ObjectStructuralListLength.native_fiber",
                    "PPAC.Migration.Internal.ObjectStructuralListLength.native_range",
                    "PPAC.Migration.Internal.ObjectStructuralListLength.native_exists",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_total",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_functional",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_range",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_cons",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_nil",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_offCons",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_recursors",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_fiber",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_closure",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_zero",
                    "PPAC.Migration.Internal.ObjectStructuralListProjection.native_next",
                    "PPAC.Migration.Internal.ObjectStructuralListEnd.native_coupled",
                    "PPAC.Migration.Internal.ObjectStructuralListEnd.native_shiftEqual",
                    "PPAC.Migration.Internal.ObjectStructuralListEnd.native_shiftIff",
                    "PPAC.Migration.Internal.ObjectStructuralListEnd.native_consShift",
                    "PPAC.Migration.Internal.ObjectStructuralListEnd.native_terminal",
                    "PPAC.Migration.Internal.ObjectStructuralListEnd.native_existsTerminal",
                    "PPAC.Migration.Internal.ObjectStructuralListEnd.native_uniquePair",
                    "PPAC.Migration.Internal.ObjectStructuralListEnd.native_traceSeed",
                    "PPAC.Migration.Internal.ObjectStructuralListEnd.native_traceRecovery",
                    "PPAC.Migration.Internal.ObjectStructuralListPositions.native_reverseStep",
                    "PPAC.Migration.Internal.ObjectStructuralListPositions.native_advance",
                    "PPAC.Migration.Internal.ObjectStructuralListPositions.native_oldIndex",
                    "PPAC.Migration.Internal.ObjectStructuralListPositions.native_swap",
                    "PPAC.Migration.Internal.ObjectStructuralListPositions.native_allPositions",
                    "PPAC.Migration.Internal.ObjectStructuralListPositions.native_at",
                    "PPAC.Migration.Internal.ObjectStructuralListPositions.native_iff",
                    "PPAC.Migration.Internal.ObjectStructuralListPositions.native_reverseExists",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_valueFiber",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_valueRange",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_zero",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_successor",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_pairFiber",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_rawExists",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_edgeLaw",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_complete",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_graphUnique",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_fiber",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_atLength",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_decode",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_decodeIff",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_decodeUnique",
                    "PPAC.Migration.Internal.ObjectStructuralListFields.native_traceHead",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_nilLength",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_consLength",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_emptyLength",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_offset",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_suffixZero",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_suffixCons",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_suffix",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_fullSuffix",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_graphRecovery",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_zeroFields",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_exists",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_valid",
                    "PPAC.Migration.Internal.ObjectStructuralListEncode.native_readback",
                    "PPAC.Migration.Internal.ObjectStructuralListRoundTrip.native_predecessor",
                    "PPAC.Migration.Internal.ObjectStructuralListRoundTrip.native_consView",
                    "PPAC.Migration.Internal.ObjectStructuralListRoundTrip.native_heads",
                    "PPAC.Migration.Internal.ObjectStructuralListRoundTrip.native_tails",
                    "PPAC.Migration.Internal.ObjectStructuralListRoundTrip.native_codeUnique",
                    "PPAC.Migration.Internal.ObjectStructuralListRoundTrip.native_sameGraph",
                    "PPAC.Migration.Internal.ObjectStructuralListRoundTrip.native_encodedUnique",
                    "PPAC.Migration.Internal.ObjectStructuralListRoundTrip.native_encodingFiber",
                    "PPAC.Migration.Internal.ObjectStructuralListRoundTrip.native_decodeThenEncode",
                    "PPAC.Migration.Internal.ObjectStructuralListRoundTrip.native_roundTrip",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_termination",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_exists",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_fiber",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_indexUnique",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_valueUnique",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_preservesStep",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_invariant",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_acceptValue",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_rejectValue",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_acceptsIff",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_rejectsIff",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_exclusive",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_decodeAccepted",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_nilAccepts",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_zeroRejects",
                    "PPAC.Migration.Internal.ObjectStructuralListCheck.native_classification",
                    "PPAC.Migration.Internal.ObjectStructuralFieldBounds.native_fieldBound",
                    "PPAC.Migration.Internal.ObjectStructuralFieldBounds.native_edgeBound",
                    "PPAC.Migration.Internal.ObjectStructuralFieldBounds.native_rawFieldBound",
                    "PPAC.Migration.Internal.ObjectStructuralFieldBounds.native_rawEdgeBound",
                    "PPAC.Migration.Internal.ObjectStructuralTreeOperator.native_shapeBound",
                    "PPAC.Migration.Internal.ObjectStructuralTreeOperator.native_childrenIff",
                    "PPAC.Migration.Internal.ObjectStructuralTreeOperator.native_leafGood",
                    "PPAC.Migration.Internal.ObjectStructuralTreeOperator.native_positiveGood",
                    "PPAC.Migration.Internal.ObjectStructuralTreeOperator.native_range",
                    "PPAC.Migration.Internal.ObjectStructuralTreeOperator.native_zero",
                    "PPAC.Migration.Internal.ObjectStructuralTreeOperator.native_functional",
                    "PPAC.Migration.Internal.ObjectStructuralTreeOperator.native_recursors",
                    "PPAC.Migration.Internal.ObjectStructuralTreeOperator.native_ordinalFiber",
                    "PPAC.Migration.Internal.ObjectStructuralTreeOperator.native_actualUnits",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_fiber",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_naturalValue",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_valueUnique",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_edgeIff",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_history",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_range",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_goodIff",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_acceptsIff",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_rejectsIff",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_fixedClassification",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_validAccepts",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_invalidRejects",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_markerTransport",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_classification",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_exclusive",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_invalidIffNot",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_recursiveIff",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_decodedFiber",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_decodedIff",
                    "PPAC.Migration.Internal.ObjectStructuralTreeCheck.native_decodeUnique",
                    "PPAC.Migration.Internal.ObjectStructuralTreeEncode.native_exists",
                    "PPAC.Migration.Internal.ObjectStructuralTreeEncode.native_fiber",
                    "PPAC.Migration.Internal.ObjectStructuralTreeEncode.native_range",
                    "PPAC.Migration.Internal.ObjectStructuralTreeEncode.native_unique",
                    "PPAC.Migration.Internal.ObjectStructuralTreeEncode.native_shapeUnique",
                    "PPAC.Migration.Internal.ObjectStructuralTreeEncode.native_validity",
                    "PPAC.Migration.Internal.ObjectStructuralTreeEncode.native_readback",
                    "PPAC.Migration.Internal.ObjectStructuralTreeEncode.native_codeRecovery",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_numeralExists",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_numeralUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_numeralRange",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_numeralLess",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_numeralDifferent",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_forestExists",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_forestUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_forestMember",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_forestLength",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_nodeFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_nodeMember",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_constructorFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_constructorDisjoint",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_constructorMember",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_scalarFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_scalarInjective",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_variableFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxConstructors.native_variableDisjoint",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_forestInput",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_nodeInput",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_constructorInput",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_forestArity",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_nodeArity",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_indexNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_indexInjective",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_variableDecode",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_indexFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_branchScope",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_branchDecode",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_scope",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_termExists",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_termRange",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_termDecode",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_branchExclusive",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_decodedExclusive",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_rejectScope",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_rejectEmpty",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_rejectTag",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_rejectFunction",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_rejectArity",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_rejectScalar",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_branchEmpty",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_rawRejectTag",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_rawRejectFunction",
                    "PPAC.Migration.Internal.ObjectSyntaxTerms.native_rawRejectUnknownTag",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_zeroTwo",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_zeroIndex",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_nullaryContexts",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_falseTwo",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_memberTypes",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_equalTypes",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_nullaryExists",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_memberExists",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_equalExists",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_memberFields",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_equalFields",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_memberValueUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_equalValueUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_memberDecode",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_memberFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_equalDecode",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_equalFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_atomicContexts",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_atomicRange",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_nullaryAtomic",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_memberAtomic",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_equalAtomic",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_symbolCheck",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_badSymbol",
                    "PPAC.Migration.Internal.ObjectSyntaxAtoms.native_unknownAtomicTag",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_readAtValue",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_advancedAtSuccessor",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_successorContext",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_singleTypes",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_negationTypes",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_binaryTypes",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_quantifierTypes",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_singleExists",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_binaryExists",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_quantifierExists",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_singleFields",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_binaryFields",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_singleBound",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_binaryBounds",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_singleUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_binaryUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_singleRange",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_singleDecode",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_binaryRange",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_binaryDecode",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_singleFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_binaryFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_singleNotCheck",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_binaryNotReads",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_quantifierNotRead",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_singleUnknownTag",
                    "PPAC.Migration.Internal.ObjectSyntaxLogical.native_binaryUnknownTag",
                    "PPAC.Migration.Internal.ObjectSyntaxContextCarrier.native_pairSubset",
                    "PPAC.Migration.Internal.ObjectSyntaxContextCarrier.native_orderedMember",
                    "PPAC.Migration.Internal.ObjectSyntaxContextCarrier.native_pairExists",
                    "PPAC.Migration.Internal.ObjectSyntaxContextCarrier.native_stateMember",
                    "PPAC.Migration.Internal.ObjectSyntaxContextCarrier.native_exists",
                    "PPAC.Migration.Internal.ObjectSyntaxContextCarrier.native_unique",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_localContext",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_localRange",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_rowAtPair",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_stateExists",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_stateFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_stateUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_stateSubset",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_stateUniverse",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_noJunk",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_stateEdge",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_badContext",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_offNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_total",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_deterministic",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_recursors",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_ordinalFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_actualCarriers",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_evaluationExists",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_naturalEvaluation",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_evaluationUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_evaluationFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_graphsAgree",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_graphValue",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_history",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_evaluationSubset",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_evaluationUniverse",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_evaluationOffNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_typedAtValue",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_readTyped",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_typedRejectCode",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_typedRejectContext",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_introduceAtomic",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_introduceNegation",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_introduceBinary",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeStates.native_introduceQuantifier",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_read",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_advanced",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_check",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_single",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_binary",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_local",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_atState",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_atValue",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_recursive",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_universal",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_actualSystem",
                    "PPAC.Migration.Internal.ObjectSyntaxTypeRecursive.native_existence",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_carrierExists",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_carrierUnique",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_atCarrier",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_guards",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_rejectCode",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_rejectContext",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_omegaIndependent",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_rootTransport",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_boundTransport",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_freeTransport",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_omegaTransport",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_advancedTransfer",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_singleTransfer",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_binaryTransfer",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_criterionTransfer",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_recursive",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_universal",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_nullaryTypes",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_memberTypes",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_equalTypes",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_negationTypes",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_binary0Types",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_binary1Types",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_binary2Types",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_binary3Types",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_forallTypes",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_existsTypes",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_quantifierTypes",
                    "PPAC.Migration.Internal.ObjectFormulaCode.native_unknownTag",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_fiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_existsOfFiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_nullaryLaw",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_nullaryFiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_nullaryExists",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_memberLaw",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_memberFiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_memberExists",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_equalLaw",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_equalFiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_equalExists",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_negationLaw",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_negationFiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_negationExists",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_forallLaw",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_forallFiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_forallExists",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_existsLaw",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_existsFiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_existsExists",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary0Law",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary0Fiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary0Exists",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary1Law",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary1Fiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary1Exists",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary2Law",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary2Fiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary2Exists",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary3Law",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary3Fiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_binary3Exists",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_membershipFiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_forestValid",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_nodeShape",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_constructorShape",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_shapeUnique",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_acceptedShape",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_reencoding",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_roundTrip",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_forestArity",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_nodeArity",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_constructorArity",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_constructorTag",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_allowedArity",
                    "PPAC.Migration.Internal.ObjectFormulaCodeConstruction.native_rejectArity",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_numeralMembers",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_indexMember",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_forestValue",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_forestEdge",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_forestFull",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_forestAll",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_nodeAll",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_nodeValue",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_constructorAll",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_constructorValue",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_slot",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_checked",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_codeField",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_termField",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_advancedField",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_zeroField",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_memberTyping",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_equalTyping",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_negationTyping",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_binaryTyping",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_quantifierTyping",
                    "PPAC.Migration.Internal.ObjectSyntaxTypedFields.native_quantifierSuccessor",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_graphChildren",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_node",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_constructor",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_scalar",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_variable",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_termBranch",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_term",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_nullary",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_member",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_equal",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_atomic",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_advancedChild",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_singleCase",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_binaryCase",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_atContext",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_property",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_progressive",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_allProperties",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_code",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_rejectNonTree",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_decodedTree",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_treeChildren",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_typedCases",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_typedData",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_typedFiber",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_rejectCases",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_rejectData",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity.native_dataTreeValid",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_slotIndex",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_slotNatural",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_slotInputs",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_slotsFull",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_slotsAll",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_graphEquality",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_fieldsGraphSubst",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_forestRecover",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_constructorRecover",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_knownTypes",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_codeFromSlots",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_rootSlot",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_arity0",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_arity1",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_arity2",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_arity3",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_rootCheck",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_casesCode",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_dataCode",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_dataIff",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_casesIff",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_fiberCode",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_fiberIff",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_rejectFiberIff",
                    "PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode.native_classification",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_sourceContexts",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_targetContexts",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_selectedMap",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_edgeSource",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_edgeTarget",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_valueExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_introBranch",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_sourceBranch",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_targetBranch",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_sourceTerm",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_targetTerm",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_outputNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_oppositeBranches",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_branchUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_unique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_existsAtIndex",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_existsBranch",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_existsTerm",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_fiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_termOfExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_termOfFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_existsIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_fiberIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_knownBranch",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_knownTerm",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_rejectEdge",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_diagonalAt",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_branchIdentity",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_identity",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_outputSubst",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTerm.native_reflexive",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_relationUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_pairTotal",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_pairGraph",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_pairEdge",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_pairComplete",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_graphExists",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_graphFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_graphUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_graphSequence",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_zeroMember",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_successorMember",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_predecessorMember",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_successorInjective",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_zeroOutput",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_successorOutput",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_sourceMember",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_targetMember",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_valueUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_pointExists",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_pointFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_liftTotal",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_liftOutputs",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_targetMap",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_liftExists",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_liftFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_liftUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_liftEdge",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_liftAll",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_liftZero",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_liftSuccessor",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_mapsLifted",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_newBoundFixed",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_oldBoundShifted",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_freePreserved",
                    "PPAC.Migration.Internal.ObjectSyntaxIndexLift.native_liftSystem",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_omegaSequence",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_codeNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_codeValid",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_uniqueCode",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_uniqueGraph",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_sourceGraphRecovery",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_existsMapCode",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_codeFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_mapNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_mapContexts",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_mapValid",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_graphFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_mapFiberIff",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_liftAtSource",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_liftExistsAtSource",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_liftExists",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_liftUniqueAtSource",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_liftInputCode",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_liftOutputCode",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_liftOutputNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_liftCodeUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_liftCodeFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_stateInputs",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_cellNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_fieldNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_sameField",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_sameFields",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_uniqueCell",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_stateFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_uniqueParams",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_actualDecode",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_recognizedNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_stateDecodeIff",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_actualStateSystem",
                    "PPAC.Migration.Internal.ObjectSyntaxMapCodeState.native_introStateRecognition",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_containsAtState",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_queryAtValue",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_queryAtState",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_advancedFreeMap",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_advancedIntro",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_nullaryCase",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_membershipCase",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_equalityCase",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_negationCase",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_binaryCase",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_quantifierCase",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_localGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_rowIntro",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_rowAtState",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_rowRecognized",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_rowSourceNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_valueMember",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_valueExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_valueSubset",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_valueUniverse",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_valueUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_valueFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_memberRecognized",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_valueAtState",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_offNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_operatorTotal",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_operatorDeterministic",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_recursors",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_graphFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_carrierRecursors",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_evaluationExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_naturalEvaluationExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_evaluationUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_evaluationFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_naturalEvaluationFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_graphAgreement",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_graphEdgeValue",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_prefix",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_evaluationSubset",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_evaluationUniverse",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_evaluationOffNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOperator.native_existence",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_intro",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_rejectCode",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_legal",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_targetType",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_containsCriterion",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_atValue",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_read",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_advanced",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_check",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_singleFields",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_singleCase",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_binaryFields",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_binaryCase",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_allCases",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_local",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_recursiveAtValue",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_recursive",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_sourceType",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_universal",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_actualSystem",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameRecursive.native_existence",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_liftSuccessors",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_liftParameters",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_advancedAtLift",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_renamedInput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_renamedNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_inputNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_existsFromFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_existsFromRenamed",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_fiberIntro",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_propertyAt",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_earlierAt",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_atomicFilter",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_nullaryLocal",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_nullarySelf",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_nullaryUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_nullaryFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameOutput.native_nullaryAllParameters",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_graphCases",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_casesFromJudgment",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_atomicFromJudgment",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_introFromCases",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_equalDataUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_equalRelationUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_equalAtOutputs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_equalExistsAtGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_equalUniqueAtGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_equalFiberAtGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_equalFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_equalAllParameters",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_equalBaseProperty",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_memberDataUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_memberRelationUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_memberAtOutputs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_memberExistsAtGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_memberUniqueAtGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_memberFiberAtGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_memberFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_memberAllParameters",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_memberBaseProperty",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_atomicProperty",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_atomicFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameAtomic.native_atomicExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_tagFilter",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_tagJudgment",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_fiberUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_propertyUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_checkTarget",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_checkNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_checkUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_checkExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_singleDataUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_singleRelationUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_binaryDataUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_binaryRelationUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_negationAtOutput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_negationExistsAtGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_negationFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_negationPropertyStep",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_forallAtOutput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_forallExistsAtGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_forallFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_forallPropertyStep",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_existsAtOutput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_existsExistsAtGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_existsFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_existsPropertyStep",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_binaryAtOutputs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_binaryExistsAtGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_binaryFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_binaryPropertyStep",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_codePropertyStep",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_propertyStep",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_progressive",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_allProperties",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_naturalProperty",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_actualFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_actualExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_fiberIffInput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_existsIffInput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_rejectInput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_unique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameTotal.native_uniqueOutput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_introBranch",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_branchTarget",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_sourceCaseIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_checkSource",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_equalityRawIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_membershipRawIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_singleRawIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_binaryRawIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_equalityIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_equalityInput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_membershipIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_membershipInput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_negationIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_negationCodeIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_negationInput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_forallIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_forallCodeIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_forallInput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_existsIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_existsCodeIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_existsInput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_binaryIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_binaryCodeIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_binaryInput",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_nullaryIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameFields.native_quantifiedAtLift",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_graphExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_graphEdges",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_graphUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_graphDiagonal",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_graphIndexMap",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_mapExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_codeExists",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_codeMap",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_codeAtGraph",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_codeEncodedIff",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_liftValueDiagonal",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_liftGraphDiagonal",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_liftCode",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_formulaReflexive",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_formulaIdentity",
                    "PPAC.Migration.Internal.ObjectSyntaxRenameIdentity.native_formulaIdentityIff",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_valueSource",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_valueTarget",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_valueUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_pointExists",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_pointFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_relationTotal",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_graphExists",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_graphFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_graphUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_graphEdges",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_graphTargetMap",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeFirst",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeSecond",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeOutput",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeReadSources",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeReadGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeEncodedIff",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeEdges",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeExistsAtSources",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeExists",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_codeInputIff",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_termBranch",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_termCompose",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_termFactor",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_termCollapse",
                    "PPAC.Migration.Internal.ObjectSyntaxCompose.native_termComposeIff",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_zero",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_shifted",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_valueForward",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_edgeForward",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_includedAgreement",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_included",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_equalGraphs",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_graphComposition",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_graphEdges",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_graphValues",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_liftedIffComposed",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_atSources",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_codedComposition",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_codedIff",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_middleEqual",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_mixedMiddle",
                    "PPAC.Migration.Internal.ObjectSyntaxComposeLift.native_mixedIff",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_targetNegation",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_targetForall",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_targetExists",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_targetBinary",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_targetEquality",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_targetMembership",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_boundDiagramCode",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_freeDiagramCode",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_nullary",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_equalityFields",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_membershipFields",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_equality",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_membership",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_atomic",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_advancedCompose",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_checkCompose",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_negationFields",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_forallFields",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_existsFields",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_binaryFields",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_negation",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_forall",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_exists",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_binary",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_codeStep",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_diagramStep",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_mapCodeStep",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_propertyStep",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_progressive",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_allProperties",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_naturalProperty",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_forward",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_factor",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_collapse",
                    "PPAC.Migration.Internal.ObjectSyntaxFormulaCompose.native_composeIff",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_graphExists",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_graphEdges",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_graphUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_mapExists",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_mapFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_mapUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_mapEdges",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_codeExists",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_codeMap",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_codeNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_codeInput",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_codeAtGraph",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_codeEncodedIff",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_codeUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_codeFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_codeInputIff",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_actualState",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_zeroState",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_codedEdges",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_freshAbsent",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_emptySource",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_emptyGraph",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeShift.native_rangeUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_identityUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_identityLift",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_input",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_sourceType",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_targetType",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_outputNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_existsOutput",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_atCodes",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_outputUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_uniqueOutput",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_actualFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_existsInputIff",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_fiberInputIff",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_actualState",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_negation",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_binary",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_quantified",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_forall",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_exists",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_nullary",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_equality",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_membership",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_boundTerm",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_freeTerm",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_freshFreeAbsent",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_emptyFreeAbsent",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_actualCodes",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_internalNegation",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_internalBinary",
                    "PPAC.Migration.Internal.ObjectSyntaxWeakenFree.native_internalQuantified",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_openTerm",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_decodedTarget",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_encodedNatural",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_encodedFree",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_decodedUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_encodedUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_decodedIndex",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_encodedTerms",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_decodeExists",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_encodeExists",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_decodeGraphUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_encodeGraphUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_encodedAtCode",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_decodedAtCode",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_encodedToDecoded",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_decodedToEncoded",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_indicesUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_termsUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_listProjection",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_mapProjection",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_fromList",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_fromMap",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_mapUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_listUnique",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_mapFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_mapExistsIff",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_mapFiberIff",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_listFiber",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_listExistsIff",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_listFiberIff",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_atGraph",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_fieldAtCode",
                    "PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec.native_fieldIsFree",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_input",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_sourceType",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_targetType",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_outputNatural",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_existsOutput",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_atCodes",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_outputUnique",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_uniqueOutput",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_actualFiber",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_existsInputIff",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_fiberInputIff",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_negation",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_binary",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_quantified",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_forall",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_exists",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_nullary",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_equality",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_membership",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_boundTerm",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_freeTermField",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_actualCodes",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_internalNegation",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_internalBinary",
                    "PPAC.Migration.Internal.ObjectFormulaFreeSubst.native_internalQuantified",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_input",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_sourceType",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_targetType",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_outputNatural",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_existsOutput",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_outputUnique",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_uniqueOutput",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_actualFiber",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_existsInputIff",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_fiberInputIff",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_atCode",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_imageGraphExists",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_pushExists",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_pushUnique",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_pushGuardedEdges",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_pushEdges",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_pushAtValue",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_bothExist",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_bothTarget",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_bothUnique",
                    "PPAC.Migration.Internal.ObjectMixedTerm.native_boundShiftExists",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_prefixExists",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_prefixUnique",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_prefixEdges",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_prefixZero",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_prefixSuccessor",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_valueUnique",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_valueZero",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_valueSuccessor",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_valueTarget",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_valueSource",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_headTerm",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_headCode",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_headExists",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_headUnique",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_preparedExists",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_preparedUnique",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_preparedTarget",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_actualState",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderExists",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderUnique",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderTarget",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderAtWitnesses",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderInput",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderUniquePair",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderFiber",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderExistsIff",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderFiberIff",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderZero",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderBound",
                    "PPAC.Migration.Internal.ObjectMixedBinder.native_binderFree",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_listType",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_fromFields",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_fieldType",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_imageEdges",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_codeExists",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_graphExists",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_codeInputIff",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_graphInputIff",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_codeUnique",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_graphUnique",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_atEncoding",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_codeFiber",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_codeFiberIff",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_graphFiber",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_graphFiberIff",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_pairCodes",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_pairGraphs",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_pairGraphUnique",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_pairCodeUnique",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termInput",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termSource",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termTarget",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termNatural",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termExists",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termAtGraphs",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termUnique",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termUniqueOutput",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termFiber",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termExistsIff",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termFiberIff",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_termField",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderExists",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderUnique",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderAtGraphs",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderInputLists",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderOutputLists",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderInput",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderNatural",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderUniqueOutput",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderFiber",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderExistsIff",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderFiberIff",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderZero",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderBound",
                    "PPAC.Migration.Internal.ObjectMixedEnvironment.native_binderFree",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_stateExists",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_stateInputIff",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_stateNatural",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_stateUnique",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_stateDecode",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_stateParamsUnique",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_containsAtState",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_readAtValue",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_readAtState",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_advancedQuery",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_operatorExists",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_operatorFiber",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_operatorUnique",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_operatorSubset",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_operatorRecognized",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_operatorMembership",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_recursors",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_carrier",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_graphExists",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_evaluationExists",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_evaluationFiber",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_evaluationUnique",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_history",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_judgmentRead",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaSource",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaTarget",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaLegal",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaInput",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaNatural",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_recursiveIff",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaFiber",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaExists",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaUnique",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaUniqueOutput",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaExistsIff",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaFiberIff",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_formulaRejectInvalid",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_nullaryFalse",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_nullaryTrue",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_equalityFields",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_membershipFields",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_negationFields",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_binary0Fields",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_binary1Fields",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_binary2Fields",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_binary3Fields",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_forallFields",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_forallAtLift",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_existsFields",
                    "PPAC.Migration.Internal.ObjectMixedFormula.native_existsAtLift",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_variableImageExists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_variableImageUnique",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_variableImageEdges",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_variableImageAtIndex",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_identityTableExists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_shiftedTableExists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_identityTableUnique",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_shiftedTableUnique",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_identityTableAt",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_shiftedTableAt",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateActualExists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateActualInput",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateActualMaps",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateActualUnique",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeExists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeInput",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeLists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeNatural",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeUnique",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeUniqueOutput",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeFiber",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeExistsIff",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeFiberIff",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateFormulaFiber",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateFormulaExists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateActualZero",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeZero",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateActualBound",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeBound",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateActualFree",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_instantiateCodeFree",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractActualExists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractActualInput",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractActualMaps",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractActualUnique",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeExists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeInput",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeLists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeNatural",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeUnique",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeUniqueOutput",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeFiber",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeExistsIff",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeFiberIff",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractFormulaFiber",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractFormulaExists",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractActualZero",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeZero",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractActualBound",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeBound",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractActualFree",
                    "PPAC.Migration.Internal.ObjectTopEnvironment.native_abstractCodeFree",
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateAtCodes',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateEnvironment',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateSourceType',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateTargetType',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateSourceNatural',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateInput',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateTargetNatural',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateExists',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateUnique',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateUniqueOutput',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateFiber',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateExistsIff',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateFiberIff',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateRejectInput',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateNullary',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateNegation',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateBinary',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateEqual',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateMember',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_instantiateQuantified',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractAtCodes',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractEnvironment',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractSourceType',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractTargetType',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractSourceNatural',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractInput',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractTargetNatural',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractExists',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractUnique',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractUniqueOutput',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractFiber',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractExistsIff',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractFiberIff',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractRejectInput',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractNullary',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractNegation',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractBinary',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractEqual',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractMember',
                    'PPAC.Migration.Internal.ObjectTopFormula.native_abstractQuantified',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_treeExists',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_treeRange',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_treeUnique',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_treeUniqueOutput',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_treeFiber',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_forestExists',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_forestRange',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_forestUnique',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_forestUniqueOutput',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_forestFiber',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_termExists',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_termRange',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_termUnique',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_termFiber',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_formulaExists',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_formulaRange',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_formulaUnique',
                    'PPAC.Migration.Internal.ObjectOriginalQuotation.native_formulaFiber',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_fieldNatural',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_fieldAt',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_forestOfFields',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_forestToFields',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_forestIff',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_treeOfConstructor',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_treeToConstructor',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_treeIff',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_treeOfScalar',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_scalarOfTree',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_scalarIff',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_treeOfVariable',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_variableOfTree',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_variableIff',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_contextsOfLengths',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_termType',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_termTypedExists',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_termTypedUnique',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_termTypedUniqueOutput',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_termTypedFiber',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_formulaType',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_formulaTypedExists',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_formulaTypedUnique',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_formulaTypedUniqueOutput',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_formulaTypedFiber',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_nullaryType',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_equalType',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_memberType',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_negationType',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_binaryType',
                    'PPAC.Migration.Internal.ObjectQuotationFields.native_quantifiedType',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_quotationAtValue',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_forestRead',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_forestLength',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_imageField',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_imageLength',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_imageRange',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_imageUnique',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_imageExists',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_imageTypedFields',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_imageTermList',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_environmentExists',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_environmentFiber',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_environmentUnique',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_environmentUniqueOutput',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_mixedAtIndex',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_mixedTerm',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_shiftAtIndex',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_shiftVariable',
                    'PPAC.Migration.Internal.ObjectTermImageQuotation.native_shiftTerm',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_readingsFromImages',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_readingsAt',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_agreeFromReadings',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_imagesFromReadings',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_zeroField',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_zeroAtNumeral',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_boundAtCode',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_boundValue',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_boundAtNumeral',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_boundReadings',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_freeAtCode',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_freeValue',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_freeReadings',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_environmentAtWitnesses',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_environmentAtMaps',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_environmentAtLifted',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_liftedFromEnvironment',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_liftedIffEnvironment',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_environmentFiber',
                    'PPAC.Migration.Internal.ObjectTermLiftQuotation.native_jointFiber',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_environmentExists',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_environmentFiber',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_environmentAtLifted',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_termIff',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_nullaryStep',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_equalityStep',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_membershipStep',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_negationStep',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_binaryStep',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_quantifiedStep',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_formulaConstruct',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_formulaIff',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_formulaAtCandidate',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_formulaValueUnique',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_formulaUniqueOutput',
                    'PPAC.Migration.Internal.ObjectNativeFormulaQuotation.native_formulaFiber',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_instantiateBoundField',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_instantiateBoundReadings',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_instantiateFreeField',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_instantiateFreeReadings',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_abstractBoundField',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_abstractBoundReadings',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_abstractFreeField',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_abstractFreeReadings',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_instantiateEnvironment',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_abstractEnvironment',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_instantiateAtCodes',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_instantiateIff',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_instantiateOriginalIff',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_instantiateAtCandidate',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_instantiateFiber',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_abstractAtCodes',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_abstractIff',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_abstractOriginalIff',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_abstractAtCandidate',
                    'PPAC.Migration.Internal.ObjectNativeTopQuotation.native_abstractFiber',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_variableRun',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_defaultRun',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_checkedIff',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_rejectEnvironment',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_rejectSource',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_targetType',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_outputNatural',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_rejectTarget',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_rejectOutputNatural',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_unique',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_uniqueOutput',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_atCandidate',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_actualFiber',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_fiberIffInput',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_encodedCheckedIff',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_uniformCorrectness',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_uniqueCode',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_atCode',
                    'PPAC.Migration.Internal.ObjectTermTransformProgram.native_existsCorrectProgram',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_membershipInstructionIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_equalityInstructionIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_compiledStepIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_operatorRowIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_operatorValueIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_graphIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_evaluationIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_executionIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_actualRecursors',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_graphExists',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_evaluationExists',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_inputOfExecution',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_sourceType',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_targetType',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_outputNatural',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_uniqueOutput',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_atCandidate',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_rejectEnvironment',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_rejectSource',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_rejectInput',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_rejectTarget',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_rejectOutputNatural',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_unique',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_actualFiber',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_fiberIffInput',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_encodedExecutionIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_uniformCorrectness',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_uniqueCode',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_atCode',
                    'PPAC.Migration.Internal.ObjectFormulaTransformProgram.native_existsCorrectProgram',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_convertedExists',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_convertedFiber',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_convertedDomainIff',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_convertedUnique',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_environmentExists',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_environmentUnique',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_termProgramIff',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_membershipIff',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_equalityIff',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_binderEnvironment',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_allMetadataAtNatural',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_formulaForward',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_formulaReverse',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_formulaRenameIff',
                    'PPAC.Migration.Internal.ObjectIndexFormulaRename.native_formulaProgramIff',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeImageGraph',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeSameListCode',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeSameListCodeUnique',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_boundIdentityImageExists',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeForward',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeReverse',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeExecutionIff',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeInputOfExecution',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeSourceType',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeTargetType',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeOutputNatural',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeUniqueOutput',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeAtCandidate',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeUnique',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeActualFiber',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeFiberIffInput',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeRejectEnvironment',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeRejectSource',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeRejectInput',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeRejectTarget',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_freeRejectOutputNatural',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakForward',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakReverse',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakExecutionIff',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakInputOfExecution',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakSourceType',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakTargetType',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakOutputNatural',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakUniqueOutput',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakAtCandidate',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakUnique',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakActualFiber',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakFiberIffInput',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakRejectEnvironment',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakRejectSource',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakRejectInput',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakRejectTarget',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakRejectOutputNatural',
                    'PPAC.Migration.Internal.ObjectFreeVariablePrograms.native_weakActualSuccessorState',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_binderFreeCodeStable',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_binderLiftedEnvironment',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_binderChildExecution',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupZeroSelected',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupConsSuccessor',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupOuterRejected',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupNilRejected',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupConsZeroReturns',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupEmptySink',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupExactDomain',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupCheckedDomain',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupUnique',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupUniqueOutput',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupAtCandidate',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupActualFiber',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupFiberIffRange',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupHasOutputIffRange',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupRejectedIffNotRange',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupOutOfBoundsRejected',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupInRangeFieldIff',
                    'PPAC.Migration.Internal.ObjectStrictLookup.native_lookupFreeImageAtEdge',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_operatorActualFiber',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_actualCarrierRecursors',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_allOrdinalRecursors',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_actualGraph',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_evaluationAtNatural',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_evaluationUniqueFiber',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_stateMembershipIff',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_recursiveCriterion',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_allInternalExecutionIff',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_naturalExecutionIff',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_encodedExecutionIff',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_uniformCorrectness',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_uniqueProgramCode',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_existsCorrectProgram',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_hasOutputIff',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_noOutputIff',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_outcomeExhaustive',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_outcomeIncompatible',
                    'PPAC.Migration.Internal.ObjectLookupTableProgram.native_uniqueOutput',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_expressionActualValue',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_expressionNaturalRange',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_expressionActualUniqueFiber',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_expressionUniqueValue',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_expressionCandidateIff',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_rawExpressionIff',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_consExpressionIff',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_premiseAtValue',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_guardAtValues',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_originalLookupHeadExpressionIff',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_originalLookupTailExpressionIff',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_originalLookupPremiseExpressionIff',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_originalLookupHeadMatrixIff',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_originalLookupTailMatrixIff',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_originalLookupChildMemberIff',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_originalLookupHeadAssignmentBound',
                    'PPAC.Migration.Internal.ObjectOriginalLookupRules.native_originalLookupTailAssignmentBound',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_naturalAssignmentFromSearchBound',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_boundedRuleApplication',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_originalLookupHeadApplication',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_originalLookupTailApplication',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_searchBoundMembershipIff',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_originalBoundedMatrixIff',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_originalQuantifiedApplicationIff',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_wholeRuleTableBoundedSearchIff',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_wholeRuleTableActualSearchIff',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_originalOtherRulesRejected',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_originalWholeTableLookupDispatchIff',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_originalActualSearchLookupDispatchIff',
                    'PPAC.Migration.Internal.ObjectBoundedLookupDispatch.native_originalLookupIntoWholeTable',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_actualOriginalLookupRow',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_originalLookupRowNaturalFields',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_originalHeadApplicationSound',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_arbitraryClosedInternalTraceSound',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_canonicalTraceActualSet',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_canonicalTraceSubsetOmega',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_canonicalTraceSuccessfulMember',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_canonicalTraceClosed',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_compiledTraceComplete',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_compiledTraceExecutionIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_compiledTraceCandidateRejectionIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_originalBoundedSearchClosureIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_originalBoundedSearchTraceIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_originalBoundedSearchTraceExecutionIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_actualPowerTraceDomainIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_actualPowerTraceSearchIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_actualPowerTraceExecutionIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_allInternalTraceSomeExecutionIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_allInternalTraceSomeCheckedIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_naturalTraceSomeRawLookupIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_allInternalTraceHasOutputIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_allInternalTraceNoOutputIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_naturalTraceHasOutputStrictIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_naturalTraceNoOutputStrictIff',
                    'PPAC.Migration.Internal.ObjectLookupTrace.native_allInternalTraceOutputUnique',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_ruleMatrixTraceMonotone',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_ruleApplicationTraceMonotone',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_originalWholeTableTraceMonotone',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_insertedTraceIncludes',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_insertedTraceSubsetOmega',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_insertedTraceClosed',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_insertedRootActualTrace',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_boundModeZeroTrace',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_boundModeZeroPowerTrace',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_boundModeThreeTrace',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_boundModeThreePowerTrace',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_freeModeZeroTrace',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_freeModeZeroPowerTrace',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_freeModeThreeTrace',
                    'PPAC.Migration.Internal.ObjectScalarTrace.native_freeModeThreePowerTrace',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalDifferentNodeTags',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalFiveFieldRecovery',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalModeWholeTableDispatchIff',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalVariableWholeTableDispatchIff',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_boundModeZeroDispatchIff',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_boundModeThreeDispatchIff',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_freeModeZeroDispatchIff',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_freeModeThreeDispatchIff',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalVariableActualSearchDispatchIff',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalVariableCandidateRejectionIff',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_arbitraryClosedVariableTraceApplication',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalVariableExprFromCode',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalBoundApplicationIdentity',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalBoundTraceIdentityIff',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalBoundPowerTraceIdentityIff',
                    'PPAC.Migration.Internal.ObjectScalarDispatch.native_originalBoundTraceRejectionIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_originalVariableExprCodeIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_originalVariableCodeNatural',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_originalFreeReplaceLookupPremiseSound',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_originalFreeReplaceMatrixSound',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_originalFreeReplaceApplicationSound',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_originalFreeReplaceTraceExecutionIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_originalFreeReplacePowerTraceExecutionIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_originalFreeReplaceTraceCandidateRejectionIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_actualOriginalFreeReplaceRoot',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_allInternalFreeReplaceReturnedIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_allInternalFreeReplaceCheckedIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_validFreeReplaceReturnedExecutionIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_naturalFreeReplaceReturnedStrictIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_allInternalFreeReplaceCandidateRejectionIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_allInternalFreeReplaceHasOutputGuardedIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_allInternalFreeReplaceNoOutputGuardedIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_validFreeReplaceHasOutputIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_validFreeReplaceNoOutputIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_naturalFreeReplaceStrictNoOutputIff',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_invalidFreeReplaceGuardNoOutput',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_nonNaturalFreeReplaceOutputRejected',
                    'PPAC.Migration.Internal.ObjectFreeReplace.native_allInternalFreeReplaceOutputUnique',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_actualSuccessorVariableValue',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_successorVariableValueExactDomain',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_successorVariableValueAtActualSuccessor',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_successorVariableValueNatural',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_successorVariableValueUnique',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_originalFreeWeakenMatrixSound',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_originalFreeWeakenApplicationSound',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_originalFreeWeakenTraceValueIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_originalFreeWeakenPowerTraceValueIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_originalFreeWeakenTraceCandidateRejectionIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_actualOriginalFreeWeakenRoot',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_allInternalFreeWeakenReturnedIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_validFreeWeakenReturnedValueIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_validFreeWeakenAtActualSuccessorIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_allInternalFreeWeakenCandidateRejectionIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_allInternalFreeWeakenHasOutputIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_allInternalFreeWeakenNoOutputIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_validFreeWeakenActualOutput',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_invalidFreeWeakenGuardNoOutput',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_nonNaturalFreeWeakenParameterNoOutput',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_nonNaturalFreeWeakenDepthNoOutput',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_invalidFreeWeakenInputNoOutput',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_allInternalFreeWeakenOutputNatural',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_nonNaturalFreeWeakenOutputRejected',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_allInternalFreeWeakenOutputUnique',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_allFourOriginalVariableTraceValueIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_allFourOriginalVariablePowerTraceValueIff',
                    'PPAC.Migration.Internal.ObjectFreeWeaken.native_allFourOriginalVariableCandidateRejectionIff',
                    'PPAC.Migration.Internal.ObjectOriginalTermProgram.native_replace_checked_iff',
                    'PPAC.Migration.Internal.ObjectOriginalTermProgram.native_replace_coded_iff',
                    'PPAC.Migration.Internal.ObjectOriginalTermProgram.native_weaken_checked_iff',
                    'PPAC.Migration.Internal.ObjectOriginalTermProgram.native_weaken_coded_iff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_actualUniversalOriginalTrace',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_universalOriginalTraceMembershipIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_everyClosedOriginalTraceIncluded',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_universalOriginalTraceClosed',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_originalFullTraceOneStepIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_originalWholeTableRuleFromTraces',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_originalArgumentFullTableDispatchIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_originalArgumentTraceSelectedIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_originalNilArgumentsTrace',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_originalConsArgumentsTrace',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentsTrace.native_originalConsArgumentActualChildTraces',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_nilModeZeroThreeGuard',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_allCandidateEmptyExprNilIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_nilActualHeadNumericIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_consActualHeadNumericIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_headActualChildTraceNumericIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_tailActualChildTraceNumericIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_nilFullTracedMatrixNumericIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_consFullTracedMatrixNumericIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_consOriginalMatrixNumericIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_nilAllCandidateRowMatrixIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentMatrix.native_consAllCandidateRowMatrixIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentRun.native_originalRunInputNatural',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentRun.native_originalRunOutputNatural',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentRun.native_actualOriginalArgumentRoot',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentRun.native_originalArgumentOutcomesNatural',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentRun.native_originalNilApplicationExactIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentRun.native_originalConsApplicationExactIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentRun.native_originalArgumentTraceCasesExactIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentRun.native_originalArgumentWholeRunCasesExactIff',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_numericTermModeRunIff',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_numericReplaceOnTypedTerm',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_numericWeakenOnTypedTerm',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_typedNilListIntroduction',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_typedConsListIntroduction',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_typedConsActualPredecessor',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_typedConsHead',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_typedConsTail',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_typedNilListIff',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_typedConsListIff',
                    'PPAC.Migration.Internal.ObjectTypedArgumentList.native_typedWholeListCasesIff',
                    'PPAC.Migration.Internal.ObjectOriginalNumericTermFiber.native_replaceWholeTermAgreement',
                    'PPAC.Migration.Internal.ObjectOriginalNumericTermFiber.native_replaceActualOriginalTermFiber',
                    'PPAC.Migration.Internal.ObjectOriginalNumericTermFiber.native_replaceAllInternalTermPromise',
                    'PPAC.Migration.Internal.ObjectOriginalNumericTermFiber.native_weakenWholeTermAgreement',
                    'PPAC.Migration.Internal.ObjectOriginalNumericTermFiber.native_weakenActualOriginalTermFiber',
                    'PPAC.Migration.Internal.ObjectOriginalNumericTermFiber.native_weakenAllInternalTermPromise',
                    'PPAC.Migration.Internal.ObjectOriginalNumericTermFiber.native_originalTermValueTransfer',
                    'PPAC.Migration.Internal.ObjectOriginalNumericTermFiber.native_originalTermFiberTransfer',
                    'PPAC.Migration.Internal.ObjectOriginalNumericTermFiber.native_originalTermValueTargetType',
                    'PPAC.Migration.Internal.ObjectOriginalNumericTermFiber.native_originalTermAllCandidateUnique',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFiber.native_originalRunInputSubstitution',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFiber.native_originalRunOutputSubstitution',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFiber.native_originalListValueTargetType',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFiber.native_originalListAllCandidateUnique',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFiber.native_originalNilListActualValue',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFiber.native_originalConsListActualValue',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFiber.native_originalAllInternalTypedListFiber',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFiber.native_originalAllInternalListCodeProperties',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFiber.native_replaceAllInternalOriginalListFiber',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFiber.native_weakenAllInternalOriginalListFiber',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFields.native_allCandidateOriginalListValue',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFields.native_originalAllInternalArgumentFields',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFields.native_originalAllInternalFieldCodeProperties',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFields.native_allInternalFieldImageOutputUnique',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFields.native_originalRunAllFieldImageIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFields.native_replaceAllInternalProgramFieldsIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFields.native_replaceWholeOriginalArgumentProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFields.native_weakenAllInternalProgramFieldsIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFields.native_weakenWholeOriginalArgumentProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentFields.native_originalConsAllInternalFields',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalKindThreeWholeTableDispatch',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalKindThreeTraceSelectedIff',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaHeadMetadata',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaApplicationNumericIff',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaConstantNumericMatrix',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaBinaryNumericMatrix',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaNonbinderNumericMatrix',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaBinderNumericMatrix',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaApplicationNumericMatrix',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaBinderActualChildRun',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalElevenRuleTraceComposition',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaConstantTraceFromData',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaBinaryTraceFromData',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaNonbinderTraceFromData',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaBinderTraceFromData',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaMatrix.native_originalFormulaApplicationTraceFromData',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaEquation.native_originalFormulaConstantAssignmentEliminated',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaEquation.native_originalFormulaBinaryAssignmentEliminated',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaEquation.native_originalFormulaNonbinderAssignmentEliminated',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaEquation.native_originalFormulaBinderAssignmentEliminated',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaEquation.native_originalFormulaApplicationAssignmentEliminated',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaEquation.native_originalFormulaBinderAtActualSuccessor',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaEquation.native_originalFormulaElevenCasesAtTraceValue',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaEquation.native_originalFormulaElevenCasesAtRow',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaEquation.native_originalFormulaElevenCasesInputOutputNatural',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaEquation.native_originalFormulaWholeRunElevenCases',
                    'PPAC.Migration.Internal.ObjectOriginalMemberApplication.native_originalAppHeadForestConstructorIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberApplication.native_originalAppHeadForestRecovered',
                    'PPAC.Migration.Internal.ObjectOriginalMemberApplication.native_originalMemberScalarAtZeroIndex',
                    'PPAC.Migration.Internal.ObjectOriginalMemberApplication.native_originalMemberAtTwoArgumentForestIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberApplication.native_originalMemberAppZeroAndTwoArgumentsRecovered',
                    'PPAC.Migration.Internal.ObjectOriginalMemberApplication.native_originalMemberAppAtNaturalArgumentsIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberApplication.native_originalMemberCheckedAppIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberApplication.native_originalMemberApplicationCaseIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentPair.native_finiteForestTypedListIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentPair.native_finiteForestAllIndexProgramFieldsIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentPair.native_finiteForestMappedProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentPair.native_replaceOriginalRunAtFiniteForestsIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentPair.native_weakenOriginalRunAtFiniteForestsIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentPair.native_twoArgumentListActualForestWitness',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentPair.native_twoArgumentMappedAllCandidatesIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentPair.native_replaceOriginalTwoArgumentAllCandidatesIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentPair.native_weakenOriginalTwoArgumentAllCandidatesIff',
                    'PPAC.Migration.Internal.ObjectOriginalArgumentPair.native_twoArgumentForestRecoveredFromActualFields',
                    'PPAC.Migration.Internal.ObjectOriginalMemberProgram.native_replaceMemberPairAllInternalAgreement',
                    'PPAC.Migration.Internal.ObjectOriginalMemberProgram.native_weakenMemberPairAllInternalAgreement',
                    'PPAC.Migration.Internal.ObjectOriginalMemberProgram.native_originalMemberWholeElevenCaseDispatchIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberProgram.native_originalMemberWholeRunApplicationIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberProgram.native_originalMembershipCaseProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberProgram.native_originalMemberApplicationProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberProgram.native_replaceOriginalMemberApplicationProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberProgram.native_replaceOriginalMemberWholeRunProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberProgram.native_weakenOriginalMemberApplicationProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalMemberProgram.native_weakenOriginalMemberWholeRunProgramIff',
                    'PPAC.Migration.Internal.ObjectExistingAtomicInterfaces.native_memberResultExistingAtomIff',
                    'PPAC.Migration.Internal.ObjectExistingAtomicInterfaces.native_replaceWholeMemberExistingAtomIff',
                    'PPAC.Migration.Internal.ObjectExistingAtomicInterfaces.native_weakenWholeMemberExistingAtomIff',
                    'PPAC.Migration.Internal.ObjectExistingAtomicInterfaces.native_replaceAllInternalCheckedTermAgreement',
                    'PPAC.Migration.Internal.ObjectExistingAtomicInterfaces.native_weakenAllInternalCheckedTermAgreement',
                    'PPAC.Migration.Internal.ObjectExistingAtomicInterfaces.native_equalityLocalCaseExistingAtomIff',
                    'PPAC.Migration.Internal.ObjectExistingAtomicInterfaces.native_replaceEqualityLocalExistingAtomIff',
                    'PPAC.Migration.Internal.ObjectExistingAtomicInterfaces.native_weakenEqualityLocalExistingAtomIff',
                    'PPAC.Migration.Internal.ObjectExistingAtomicInterfaces.native_constantDataExistingAtomIff',
                    'PPAC.Migration.Internal.ObjectWholeAtomicInterfaces.native_rawApplicationWrongTagRejected',
                    'PPAC.Migration.Internal.ObjectWholeAtomicInterfaces.native_applicationCaseWrongTagRejected',
                    'PPAC.Migration.Internal.ObjectWholeAtomicInterfaces.native_wholeFalseDispatchIff',
                    'PPAC.Migration.Internal.ObjectWholeAtomicInterfaces.native_wholeTrueDispatchIff',
                    'PPAC.Migration.Internal.ObjectWholeAtomicInterfaces.native_wholeEqualityDispatchIff',
                    'PPAC.Migration.Internal.ObjectWholeAtomicInterfaces.native_replaceWholeEqualityExistingAtomIff',
                    'PPAC.Migration.Internal.ObjectWholeAtomicInterfaces.native_weakenWholeEqualityExistingAtomIff',
                    'PPAC.Migration.Internal.ObjectWholeAtomicInterfaces.native_wholeConstantExistingAtomIff',
                    'PPAC.Migration.Internal.ObjectUnifiedAtomicProgram.native_compiledAtomicProgramSource',
                    'PPAC.Migration.Internal.ObjectUnifiedAtomicProgram.native_replaceTypedMembershipWholeRunIff',
                    'PPAC.Migration.Internal.ObjectUnifiedAtomicProgram.native_replaceTypedEqualityWholeRunIff',
                    'PPAC.Migration.Internal.ObjectUnifiedAtomicProgram.native_replaceUnifiedAtomicProgramIff',
                    'PPAC.Migration.Internal.ObjectUnifiedAtomicProgram.native_weakenTypedMembershipWholeRunIff',
                    'PPAC.Migration.Internal.ObjectUnifiedAtomicProgram.native_weakenTypedEqualityWholeRunIff',
                    'PPAC.Migration.Internal.ObjectUnifiedAtomicProgram.native_weakenUnifiedAtomicProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalLogicalProgram.native_logicalHistoryAgreementAt',
                    'PPAC.Migration.Internal.ObjectOriginalLogicalProgram.native_negationChildFormulaCode',
                    'PPAC.Migration.Internal.ObjectOriginalLogicalProgram.native_binaryChildrenFormulaCode',
                    'PPAC.Migration.Internal.ObjectOriginalLogicalProgram.native_negationLocalHistoryIff',
                    'PPAC.Migration.Internal.ObjectOriginalLogicalProgram.native_negationWholeRunDispatchIff',
                    'PPAC.Migration.Internal.ObjectOriginalLogicalProgram.native_negationWholeRunHistoryConditionalIff',
                    'PPAC.Migration.Internal.ObjectOriginalLogicalProgram.native_binaryLocalHistoryIff',
                    'PPAC.Migration.Internal.ObjectOriginalLogicalProgram.native_binaryWholeRunDispatchIff',
                    'PPAC.Migration.Internal.ObjectOriginalLogicalProgram.native_binaryWholeRunHistoryConditionalIff',
                    'PPAC.Migration.Internal.ObjectActualFormulaHistory.native_actualHistoryReadExecutedIff',
                    'PPAC.Migration.Internal.ObjectActualFormulaHistory.native_prefixInductionAt',
                    'PPAC.Migration.Internal.ObjectActualFormulaHistory.native_actualHistoryAgreementFromInduction',
                    'PPAC.Migration.Internal.ObjectActualFormulaHistory.native_agreedActualHistoryExists',
                    'PPAC.Migration.Internal.ObjectActualFormulaHistory.native_negationActualHistoryFromInductionIff',
                    'PPAC.Migration.Internal.ObjectActualFormulaHistory.native_binaryActualHistoryFromInductionIff',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_freeConversionFromActualConverted',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_frameEnvironment',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_weakenFrameFromExistingEnvironment',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_replaceFrameFromFreeConversion',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_frameAtomicWholeProgramIff',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_binderEnvironmentAt',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_binderEnvironmentExists',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_uniformCorrectAt',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_uniformPrefixAt',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_uniformPrefixAtFrame',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_actualHistoryAgreementAtUniformFrame',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_actualHistoryExistsAtUniformFrame',
                    'PPAC.Migration.Internal.ObjectUniformOperationFrames.native_binderPrefixFromUniformInduction',
                    'PPAC.Migration.Internal.ObjectOriginalBinderProgram.native_naturalSuccessorWitness',
                    'PPAC.Migration.Internal.ObjectOriginalBinderProgram.native_liftedChildExecutionAlignmentIff',
                    'PPAC.Migration.Internal.ObjectOriginalBinderProgram.native_quantifierChildReadAtLiftIff',
                    'PPAC.Migration.Internal.ObjectOriginalBinderProgram.native_quantifierStepAdvancedIff',
                    'PPAC.Migration.Internal.ObjectOriginalBinderProgram.native_quantifierLocalCaseIff',
                    'PPAC.Migration.Internal.ObjectOriginalBinderProgram.native_quantifierWholeRunDispatchIff',
                    'PPAC.Migration.Internal.ObjectOriginalBinderProgram.native_quantifierWholeRunFromUniformInductionIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformRootStep.native_recursiveCasesTargetType',
                    'PPAC.Migration.Internal.ObjectFormulaTransformRootStep.native_actualProgramTargetType',
                    'PPAC.Migration.Internal.ObjectFormulaTransformRootStep.native_actualRootGuardedStepIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformRootStep.native_actualRootStepIff',
                    'PPAC.Migration.Internal.ObjectFormulaTransformRootStep.native_actualRootWholeProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness.native_fullElevenProgramFromUniformIff',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness.native_wholeRunExecutedFromUniformIff',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness.native_allParametersCorrectFromUniform',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness.native_allInternalRootsCorrect',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness.native_uniformInductionDischarged',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness.native_allInternalWholeRunExecutedIff',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness.native_allInternalWholeProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness.native_actualHistoryAgreementDischarged',
                    'PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness.native_agreedActualHistoryExistsDischarged',
                    'PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula.native_emptyBoundTermFree',
                    'PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula.native_emptyBoundListsIff',
                    'PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula.native_emptyBoundConversionExists',
                    'PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula.native_modeThreeWholeSubstitutionIff',
                    'PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula.native_modeThreeWholeProgramIff',
                    'PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula.native_modeThreeEmptyBoundArgumentsIff',
                    'PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula.native_modeThreeOutputType',
                    'PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula.native_modeThreeOutputUnique',
                    'PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula.native_modeThreeActualOutput',
                    'PPAC.Migration.Internal.ObjectPureSyntaxTermChecker.native_purePremiseFreeTraceExists',
                    'PPAC.Migration.Internal.ObjectPureSyntaxTermChecker.native_pureVariableExpressionIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxTermChecker.native_pureVariableApplicationSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxTermChecker.native_pureTermClosedTraceSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxTermChecker.native_pureTermCheckSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxTermChecker.native_pureTermCheckComplete',
                    'PPAC.Migration.Internal.ObjectPureSyntaxTermChecker.native_pureTermCheckIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxTermChecker.native_pureEmptyBoundTermCheckFree',
                    'PPAC.Migration.Internal.ObjectPureSyntaxListSteps.native_binaryUnionExists',
                    'PPAC.Migration.Internal.ObjectPureSyntaxListSteps.native_pureTraceInsertionCondition',
                    'PPAC.Migration.Internal.ObjectPureSyntaxListSteps.native_pureTracePairCondition',
                    'PPAC.Migration.Internal.ObjectPureSyntaxListSteps.native_pureNilExpressionIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxListSteps.native_pureNilApplicationSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxListSteps.native_pureNilApplicationComplete',
                    'PPAC.Migration.Internal.ObjectPureSyntaxListSteps.native_pureNilChecked',
                    'PPAC.Migration.Internal.ObjectPureSyntaxListSteps.native_pureTypedNilChecked',
                    'PPAC.Migration.Internal.ObjectPureSyntaxListSteps.native_pureConsApplicationComplete',
                    'PPAC.Migration.Internal.ObjectPureSyntaxListSteps.native_pureConsConditionComplete',
                    'PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker.native_pureConsQueryComplete',
                    'PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker.native_pureConsApplicationFromInductionSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker.native_pureArgumentsFromInductionIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker.native_pureAllArgumentsCorrect',
                    'PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker.native_pureArgumentsInductionDischarged',
                    'PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker.native_pureArgumentsQueryIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker.native_pureArgumentsQuerySound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker.native_pureArgumentsQueryComplete',
                    'PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker.native_pureEmptyBoundArgumentsQueryIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker.native_pureModeThreeFromArgumentsQueryIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms.native_constantInputExpressionIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms.native_constantApplicationIffNullary',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms.native_constantApplicationSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms.native_constantQueryConstructed',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms.native_typedConstantQueryConstructed',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms.native_equalityInputExpressionIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms.native_equalityApplicationSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms.native_equalityQueryConstructed',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms.native_typedEqualityQueryConstructed',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms.native_equalityActualChildTracesMerged',
                    'PPAC.Migration.Internal.ObjectPureSyntaxMembership.native_membershipInputDataIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxMembership.native_membershipAtForestIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxMembership.native_membershipTypedListSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxMembership.native_membershipActualPremiseAtTwo',
                    'PPAC.Migration.Internal.ObjectPureSyntaxMembership.native_membershipApplicationSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxMembership.native_membershipQueryFromList',
                    'PPAC.Migration.Internal.ObjectPureSyntaxMembership.native_membershipQueryAt',
                    'PPAC.Migration.Internal.ObjectPureSyntaxMembership.native_typedMembershipQuery',
                    'PPAC.Migration.Internal.ObjectPureSyntaxMembership.native_fullMembershipQuery',
                    'PPAC.Migration.Internal.ObjectPureSyntaxMembership.native_allFourAtomicQueries',
                    'PPAC.Migration.Internal.ObjectPureSyntaxBinary.native_formulaCorrectInstance',
                    'PPAC.Migration.Internal.ObjectPureSyntaxBinary.native_formulaStrictIHInstance',
                    'PPAC.Migration.Internal.ObjectPureSyntaxBinary.native_binaryInputExpressionIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxBinary.native_binaryKnownTypeIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxBinary.native_binaryActualApplicationSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxBinary.native_binaryActualChildTracesMerged',
                    'PPAC.Migration.Internal.ObjectPureSyntaxBinary.native_binaryQueryFromActualChildren',
                    'PPAC.Migration.Internal.ObjectPureSyntaxBinary.native_binaryQueryFromStrictInduction',

                    'PPAC.Migration.Internal.ObjectPureSyntaxUnary.native_unaryInputExpressionIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxUnary.native_unaryKnownTypeIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxUnary.native_unaryActualApplicationSound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxUnary.native_unaryActualChildTraceExtended',
                    'PPAC.Migration.Internal.ObjectPureSyntaxUnary.native_unaryQueryFromActualChild',
                    'PPAC.Migration.Internal.ObjectPureSyntaxUnary.native_unaryQueryFromInternalStep',
                    'PPAC.Migration.Internal.ObjectPureSyntaxUnary.native_unaryQueryFromStrictInduction',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaChecker.native_formulaFromInductionIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaChecker.native_formulaAllInternalCorrect',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaChecker.native_formulaCorrectAtRoot',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaChecker.native_formulaInductionDischarged',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaChecker.native_formulaQueryIff',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaChecker.native_formulaQuerySound',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaChecker.native_formulaQueryComplete',
                    'PPAC.Migration.Internal.ObjectPureSyntaxFormulaChecker.native_fullSyntaxTypingIff',
                    'PPAC.Migration.Internal.ObjectPureProofSubstitutionQueries.native_termExprQueryIff',
                    'PPAC.Migration.Internal.ObjectPureProofSubstitutionQueries.native_argumentsExprQueryIff',
                    'PPAC.Migration.Internal.ObjectPureProofSubstitutionQueries.native_formulaExprQueryIff',
                    'PPAC.Migration.Internal.ObjectPureProofSubstitutionQueries.native_substitutionFormulaQueryIff',
                    'PPAC.Migration.Internal.ObjectPureProofSubstitutionQueries.native_substitutionArgumentsQueryIff',
                    'PPAC.Migration.Internal.ObjectPureProofSubstitutionQueries.native_substitutionTransformAtModeIff',
                    'PPAC.Migration.Internal.ObjectPureProofSubstitutionQueries.native_substitutionGuardedTransformIff',
                    'PPAC.Migration.Internal.ObjectPureProofSubstitutionQueries.native_substitutionBundleIff',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_pairingComponentExists',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_pairingComponentUnique',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_barePairEveryNaturalDecodes',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawEveryPositiveNaturalDecodes',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawZeroComponent',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawUnselectedNaturalIsZero',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawHeadTailExists',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawHeadTailUnique',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawHeadTailRange',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawHeadTailZeroIff',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_arbitraryRawTagHeadTailIff',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawNaturalIterationFiber',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawGetExists',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawGetUnique',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawGetFiber',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawGetRange',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawGetZeroEquation',
                    'PPAC.Migration.Internal.ObjectRawCodeProjection.native_rawGetSuccessorEquation',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawGetZeroAllInternalIndices',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawGetZeroInputIff',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawFieldExists',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawFieldUnique',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawFieldFiber',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawFieldRange',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawFieldAtActualPayloadIff',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawFieldAtArbitraryRawTagIff',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawFieldZeroInputIff',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawHeadTailOnActualConsIff',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawGetAtFiniteForestIff',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawFieldAtFiniteNodeIff',
                    'PPAC.Migration.Internal.ObjectRawCodeField.native_rawFieldAtFiniteConstructorIff',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionTraceNatural',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionTraceOriginalStep',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionTraceSetExists',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionTraceAllRootsUnfold',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionTraceAtActualSetIff',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionActualHeadBound',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionActualRuleApplication',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionActualRuleCondition',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionTagZeroRule',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionTagPositiveRule',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionGetZeroRule',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionGetHeadRule',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionGetTailRule',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionFieldZeroRule',
                    'PPAC.Migration.Internal.ObjectProjectionTrace.native_projectionFieldPositiveRule',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionConstructorFieldNatural',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionTagQueryNatural',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionGetQueryNatural',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionFieldQueryNatural',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionTagRuleDispatch',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionGetRuleDispatch',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionFieldRuleDispatch',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionTagZeroConstructed',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionTagRawConstructed',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionTagSound',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionTagComplete',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionTagQueryIff',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionTagQueryUnique',
                    'PPAC.Migration.Internal.ObjectProjectionTag.native_projectionTagAtActualRowSound',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionActualPremiseQueryIff',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionActualPremisesQueriesIff',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetVariablesQueryIff',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionArbitraryRawPairHeadTail',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionSuccessorVariableIff',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetZeroConstructed',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetHeadConstructed',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetTailConstructed',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetZeroIndexIff',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetAllInternalCorrect',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetAtInternalIndexIff',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetAllCandidatesIff',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetSound',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetComplete',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetUnique',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetObjectSuccessorStep',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionGetTailActualSubquery',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionFieldZeroConstructed',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionFieldRawConstructed',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionFieldAllCandidatesIff',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionFieldSound',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionFieldComplete',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_projectionFieldUnique',
                    'PPAC.Migration.Internal.ObjectProjectionGetField.native_originalSevenProjectionNumericIffs',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionFreeProjectionIff',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionFormulaProjectionAtOneIff',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionFormulaProjectionIff',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionBothProjectionsIff',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionFreeProjectionAtConstructor',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionFormulaProjectionAtConstructor',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionProjectionsAtConstructor',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionAllFiveQueriesIff',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_pairingProjectionNumericBound',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_rawHeadTailNumericBound',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_rawGetAllInternalBounds',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_rawGetNumericBound',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_rawFieldNumericBound',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionAtOneBound',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionFormulaProjectionBound',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionAllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionActualFiveFieldHeadIff',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionBoundedMatrixIff',
                    'PPAC.Migration.Internal.ObjectProofSubstitutionNode.native_substitutionFullPureRelationalNodeIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpConclusionQueryIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpAntecedentQueryIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpLeftFreeProjectionIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpLeftFormulaProjectionIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpRightFreeProjectionIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpRightImplicationProjectionIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpImplicationGraphIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpRightImplicationAtConstructorIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpAllFourProjectionsIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpBothFormulaQueriesIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpAllSixQueriesIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpAntecedentProjectionBound',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpAllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpActualFourFieldHeadIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpBoundedMatrixIff',
                    'PPAC.Migration.Internal.ObjectProofMPNode.native_mpFullPureRelationalNodeIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_modeZeroFormulaAtCodesIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_modeZeroFullFormulaWeakenIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_modeZeroFullFormulaProgramIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_modeZeroFullFormulaOutputType',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningFormulaQueryIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningFreeProjectionAtSuccessorIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningPredecessorFormulaIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningActualModeZeroQueryIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningGuardedModeZeroProgramIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningAllFourQueriesAtSuccessorIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningAllFourQueriesIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningPredecessorFormulaBound',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningAllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningActualThreeFieldHeadIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningBoundedMatrixIff',
                    'PPAC.Migration.Internal.ObjectProofStrengtheningNode.native_strengtheningFullPureRelationalNodeIff',
                    'PPAC.Migration.Internal.ObjectOriginalAbstract.native_modeOneFiveRuleStepIff',
                    'PPAC.Migration.Internal.ObjectOriginalAbstract.native_modeOneVariableTwoRuleStepIff',
                    'PPAC.Migration.Internal.ObjectOriginalAbstract.native_modeOneVariableWholeTraceIff',
                    'PPAC.Migration.Internal.ObjectOriginalAbstract.native_modeOneBoundIdentityGuardIff',
                    'PPAC.Migration.Internal.ObjectOriginalAbstract.native_modeOneBoundAbstractGuardIff',
                    'PPAC.Migration.Internal.ObjectOriginalAbstract.native_modeOneBoundPreservedTrace',
                    'PPAC.Migration.Internal.ObjectOriginalAbstract.native_modeOneBoundShiftedTrace',
                    'PPAC.Migration.Internal.ObjectOriginalAbstract.native_modeOneFreeHeadTrace',
                    'PPAC.Migration.Internal.ObjectOriginalAbstract.native_modeOneFreeTailTrace',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_originalVariableIndexGraph',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneBoundVariableNumericIff',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneBoundVariableNumericSound',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneBoundVariableNumericComplete',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneFreeVariableNumericIff',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneFreeVariableNumericSound',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneFreeVariableNumericComplete',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneAllVariableNumericTraceIff',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneAllVariableNumericRunIff',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneVariableNumericOutputNatural',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOnePreservedValueConstructsTrace',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneShiftedValueConstructsTrace',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneFreeHeadValueConstructsTrace',
                    'PPAC.Migration.Internal.ObjectAbstractVariable.native_modeOneFreeTailValueConstructsTrace',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_smallModeOriginalNilGuard',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_smallModeOriginalNilMatrixIff',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_smallModeOriginalNilAtRowIff',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_smallModeOriginalNilApplicationIff',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_smallModeArgumentTraceAtActualValueIff',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_smallModeArgumentTraceIff',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_smallModeArgumentWholeRunIff',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_modeOnePureTermGuardedNumericIff',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_modeOnePureTermTypedNumericIff',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_modeOneTermScopeBranchNumeric',
                    'PPAC.Migration.Internal.ObjectSmallModeArguments.native_modeOneTermNumericBranchRun',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneBoundAtZeroDepthIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneFreeAtZeroIndexIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneFreeAtSuccessorIndexIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneBoundBelowDepthIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneActualBoundTableAtSuccessorIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneActualFreeTableAtZeroIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneActualFreeTableAtSuccessorIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthActualVariableTableIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthActualVariableProgramIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthActualPureTermProgramIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthActualCodedPureTermIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthPureTermAtActualCodesIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthPureTermActualOperationIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_actualAbstractPureTermSourceType',
                    'PPAC.Migration.Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthGuardedPureTermActualOperationIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_smallModeArgumentActualFiber',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_smallModeArgumentActualFields',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_smallModeArgumentCompleteFieldMapIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_modeOneActualTermAllOutputsAgreement',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_modeOneActualTermUniqueTypedFiber',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_modeOneActualTermPromiseDischarged',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthActualArgumentFieldsIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthActualArgumentProgramIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthArgumentsAtActualCodesIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthArgumentsActualOperationIff',
                    'PPAC.Migration.Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthGuardedArgumentsActualOperationIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_arbitraryDepthBoundShiftedIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_internalSuccessorThresholdIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_knownActualIndexVariableRenameIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_actualBinderBoundRenameIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_actualBinderFreeRenameIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_arbitraryDepthBoundBinderCovarianceIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_arbitraryDepthFreeBinderCovarianceIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_actualAbstractRootCompatibleFrame',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_actualLiftedBoundFieldsIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_actualLiftedFreeFieldsIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_allInternalLiftedBoundFieldsIff',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_allInternalLiftedFrameCompatibility',
                    'PPAC.Migration.Internal.ObjectAbstractOperationFrame.native_actualBinderCompatibleFrameWitnessesDischarged',
                    'PPAC.Migration.Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameVariableProgramIff',
                    'PPAC.Migration.Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTermProgramIff',
                    'PPAC.Migration.Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTermCodedIff',
                    'PPAC.Migration.Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTermGuardedCodedIff',
                    'PPAC.Migration.Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTermAllOutputsAgreement',
                    'PPAC.Migration.Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTypedTermUniqueFiber',
                    'PPAC.Migration.Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTermPromiseDischarged',
                    'PPAC.Migration.Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameArgumentFieldsIff',
                    'PPAC.Migration.Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameArgumentProgramIff',
                    'PPAC.Migration.Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameGuardedArgumentProgramIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_smallModeFormulaConstantGuard',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_smallModeFormulaConstantMatrixIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_smallModeFormulaConstantApplicationIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_smallModeCompleteFormulaTraceIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_smallModeCompleteFormulaWholeRunIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_smallModeWholeFalseDispatchIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_smallModeWholeTrueDispatchIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_smallModeWholeEqualityDispatchIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_smallModeWholeMemberDispatchIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_modeOneFrameAtomicTermAgreement',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_modeOneFrameActualPairProgramIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_modeOneFrameActualPairAgreement',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_modeOneFrameWholeConstantIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_modeOneFrameWholeMembershipIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_modeOneFrameWholeEqualityIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_modeOneFrameAllAtomicWholeRunIff',
                    'PPAC.Migration.Internal.ObjectAbstractAtomicFormula.native_modeOneFrameAllAtomicProgramIff',
                    'PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness.native_modeOneAllFormulaCorrect',
                    'PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness.native_modeOneFormulaCorrectAt',
                    'PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness.native_modeOneAllFramesIH',
                    'PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness.native_modeOneFullFormulaRunExecutionIff',
                    'PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness.native_modeOneActualHistoryAgreement',
                    'PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness.native_modeOneFullFormulaRunProgramIff',
                    'PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness.native_modeOneAgreedHistoryExists',
                    'PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness.native_modeOneActualTopFullFormulaExecutionIff',
                    'PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness.native_modeOneActualTopFullFormulaProgramIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_modeOneActualTopFormulaAtCodesIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_modeOneActualTopFormulaIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_modeOneActualTopGuardedFormulaIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_modeOneActualTopFormulaSource',
                    'PPAC.Migration.Internal.ObjectForallNode.native_forallFormulaQueryIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_forallFreeProjectionQueryIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_forallPredecessorFormulaQueryIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_forallModeOneTransformNumericIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_forallActualTopTransformIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_forallAllFourQueriesIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_forallAllFourAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectForallNode.native_forallActualNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_forallFullPureRelationalNodeIff',
                    'PPAC.Migration.Internal.ObjectForallNode.native_forallFullNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoWholeVariableValueIff',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoVariableTraceValueIff',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoBoundCandidateIff',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoFreeCandidateIff',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoOriginalVariableTraceStepIff',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoFiveRuleTermDispatchIff',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoBoundPreservedPositiveTrace',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoBoundPointPositiveTrace',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoBoundPredecessorPositiveTrace',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoFreeIdentityPositiveTrace',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoClosedParameterFreeBranch',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoFrameTermProgramIff',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoFrameTermCodedIff',
                    'PPAC.Migration.Internal.ObjectInstantiateVariable.native_modeTwoFrameGuardedTermCodedIff',
                    'PPAC.Migration.Internal.ObjectInstantiateRoot.native_modeTwoClosedParameterBinderRenameIff',
                    'PPAC.Migration.Internal.ObjectInstantiateRoot.native_modeTwoVariableAtPointIff',
                    'PPAC.Migration.Internal.ObjectInstantiateRoot.native_modeTwoVariableBelowIff',
                    'PPAC.Migration.Internal.ObjectInstantiateRoot.native_modeTwoActualRootVariableFieldIff',
                    'PPAC.Migration.Internal.ObjectInstantiateRoot.native_modeTwoActualRootVariableCompatibility',
                    'PPAC.Migration.Internal.ObjectInstantiateRoot.native_modeTwoActualRootFrame',
                    'PPAC.Migration.Internal.ObjectInstantiateRoot.native_modeTwoActualRootTermProgramIff',
                    'PPAC.Migration.Internal.ObjectInstantiateRoot.native_modeTwoActualRootTermCodedIff',
                    'PPAC.Migration.Internal.ObjectInstantiateRoot.native_modeTwoActualRootGuardedTermCodedIff',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderSuccessorPoint',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderContextGeometry',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderBelowCaseIff',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderPointCaseIff',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderBoundCovarianceIff',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderFreeCovarianceIff',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderFreshZeroFieldIff',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderBoundSuccessorFieldIff',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderFreeFieldIff',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderVariableCompatibility',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoBinderFrameAtWitnesses',
                    'PPAC.Migration.Internal.ObjectInstantiateBinder.native_modeTwoActualBinderFrame',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoAllTypedTermAgreement',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoAllTypedTermUniqueFiber',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoTermPromiseDerived',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoArgumentFieldsProgramIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoWholeArgumentProgramIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoGuardedArgumentProgramIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoFourAtomicRunIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoFourAtomicProgramIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoActualBinderPrefixFromInduction',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoAllElevenProgramFromInductionIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoUniformCorrectnessProgressive',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoAllInternalFormulaCorrect',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoAllInternalRootsCorrect',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoAllInternalWholeFormulaExecutionIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoAllInternalWholeFormulaProgramIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoActualHistoryAgreementDischarged',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoAgreedActualHistoryExistsDischarged',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoActualRootWholeFormulaExecutionIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoActualRootWholeFormulaProgramIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoActualInstantiateTopAtCodesIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoActualInstantiateTopIff',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoActualInstantiateTopSourceType',
                    'PPAC.Migration.Internal.ObjectInstantiateFormula.native_modeTwoActualInstantiateTopGuardedIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeAtBoundQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeAllQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeAllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeBoundedMatrixIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeWholeNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeWholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveAtBoundQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveAllQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveAllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveBoundedMatrixIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveWholeNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveWholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalRule20NestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalRule23NestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalInstantiate.native_logicalRule25NestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalAllQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule0WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule0AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule0NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule1WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule1AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule1NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule2WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule2AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule2NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule3WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule3AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule3NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule4WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule4AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule4NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule5WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule5AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule5NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule6WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule6AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule6NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule7WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule7AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule7NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule8WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule8AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule8NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule9WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule9AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule9NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule10WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule10AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule10NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule11WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule11AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule11NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule12WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule12AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule12NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule13WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule13AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule13NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule14WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule14AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule14NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule15WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule15AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule15NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule16WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule16AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule16NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule17WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule17AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule17NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule18WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule18AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule18NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule19WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule19AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule19NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule22WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule22AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule22NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule26WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule26AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalStatic.native_staticLogicalRule26NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule21AtSuccessorsQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule21AtOneQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule21AllQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule21AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule21NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule21WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule24AtSuccessorsQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule24AtOneQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule24AllQueriesIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule24AllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule24NumericNestedHeadIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalRule24WholeNormalizedNodeIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalAllTwentySevenWholeNodesIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalAllTwentySevenActualShapeTableIff',
                    'PPAC.Migration.Internal.ObjectLogicalAbstract.native_logicalAllTwentySevenActualTableSpecificationIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofLogicalNumericHeadIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofLogicalQueryConstructorIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofLogicalQueryNormalizedIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofLogicalAllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofLogicalBoundedMatrixIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofLogicalWholeNodeIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofTheoryNumericHeadIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofTheoryFormulaQueryIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofTheoryParameterizedAxiomQueryIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofTheoryParameterizedAllQueriesIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofTheoryAllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofTheoryParameterizedBoundedMatrixIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofTheoryParameterizedWholeNodeIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofSixRulesParameterizedActualShapeTableIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofSixRulesParameterizedSelectedNodesIff',
                    'PPAC.Migration.Internal.ObjectProofBaseNodes.native_proofSixRulesParameterizedActualTableSpecificationIff',
                    'PPAC.Migration.Internal.ObjectProofTreeTrace.native_proofTreeAllTraceRootsExist',
                    'PPAC.Migration.Internal.ObjectProofTreeTrace.native_proofTreeTraceRange',
                    'PPAC.Migration.Internal.ObjectProofTreeTrace.native_proofTreeAllRootsMembershipIff',
                    'PPAC.Migration.Internal.ObjectProofTreeTrace.native_proofTreeAllRootsClosed',
                    'PPAC.Migration.Internal.ObjectProofTreeTrace.native_proofTreeTwelveRuleTracedStepIff',
                    'PPAC.Migration.Internal.ObjectProofTreeTrace.native_proofTreeFullRecursiveTraceIff',
                    'PPAC.Migration.Internal.ObjectProofTreeTrace.native_proofTreeNodeEntryRecursiveIff',
                    'PPAC.Migration.Internal.ObjectProofTreeTrace.native_proofTreeRootEntryRecursiveIff',
                    'PPAC.Migration.Internal.ObjectProofTreeTrace.native_proofTreeTwelveBranchAllAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectProofTreeTrace.native_proofTreeTwelveBranchTraceComposition',
                    'PPAC.Migration.Internal.ObjectProofTreeRoot.native_proofRootOneNonempty',
                    'PPAC.Migration.Internal.ObjectProofTreeRoot.native_proofRootOneMembership',
                    'PPAC.Migration.Internal.ObjectProofTreeRoot.native_proofRootZeroGuardIff',
                    'PPAC.Migration.Internal.ObjectProofTreeRoot.native_proofRootPayloadConstructorIff',
                    'PPAC.Migration.Internal.ObjectProofTreeRoot.native_proofRootActualLocalCondition',
                    'PPAC.Migration.Internal.ObjectProofTreeRoot.native_proofRootClosedFieldsForward',
                    'PPAC.Migration.Internal.ObjectProofTreeRoot.native_proofRootClosedFieldsBackward',
                    'PPAC.Migration.Internal.ObjectProofTreeRoot.native_proofRootExactClosedFieldsIff',
                    'PPAC.Migration.Internal.ObjectProofTreeNode.native_proofNodeFieldLocalIff',
                    'PPAC.Migration.Internal.ObjectProofTreeNode.native_proofNodeActualTagLocalIff',
                    'PPAC.Migration.Internal.ObjectProofTreeNode.native_proofNodeVariableChildIff',
                    'PPAC.Migration.Internal.ObjectProofTreeNode.native_proofNodeAllChildrenIff',
                    'PPAC.Migration.Internal.ObjectProofTreeNode.native_proofNodePayloadFieldBelow',
                    'PPAC.Migration.Internal.ObjectProofTreeNode.native_proofNodeSixCasesForward',
                    'PPAC.Migration.Internal.ObjectProofTreeNode.native_proofNodeSixCasesBackward',
                    'PPAC.Migration.Internal.ObjectProofTreeNode.native_proofNodeExactSixCasesIff',
                    'PPAC.Migration.Internal.ObjectProofTreeNode.native_proofRootExactNodeSixCasesIff',
                    'PPAC.Migration.Internal.ObjectProofTreeInduction.native_proofTreePropertyStepWithMemberIH',
                    'PPAC.Migration.Internal.ObjectProofTreeInduction.native_proofTreePropertyProgressive',
                    'PPAC.Migration.Internal.ObjectProofTreeInduction.native_proofTreeInternalInduction',
                    'PPAC.Migration.Internal.ObjectProofTreeInduction.native_proofTreePointInduction',
                    'PPAC.Migration.Internal.ObjectProofTreeInduction.native_proofTreeRootProperty',
                    'PPAC.Migration.Internal.ObjectProofTreeInduction.native_proofTreeRejectNodeFromProperty',
                    'PPAC.Migration.Internal.ObjectProofTreeInduction.native_proofTreeRejectRootFromProperty',
                    'PPAC.Migration.Internal.ObjectProofTreeEquation.native_proofTreeEquationImpliesLocalClosure',
                    'PPAC.Migration.Internal.ObjectProofTreeEquation.native_proofTreeEquationReverseProgressive',
                    'PPAC.Migration.Internal.ObjectProofTreeEquation.native_proofTreeEquationAllCodeUnique',
                    'PPAC.Migration.Internal.ObjectProofTreeEquation.native_proofTreeEquationPointUnique',
                    'PPAC.Migration.Internal.ObjectProofTreeEquation.native_proofTreeEquationRootUnique',
                    'PPAC.Migration.Internal.ObjectProofTreeEquation.native_proofTreeEquationTwoSolutions',
                    'PPAC.Migration.Internal.ObjectProofTreeEquation.native_proofTreeEquationNodeNatural',
                    'PPAC.Migration.Internal.ObjectProofTreeEquation.native_proofTreeEquationSolutionNatural',
                    'PPAC.Migration.Internal.ObjectProofTreeEquation.native_proofTreeCanonicalNodeEquation',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_unaryIterationExistsUnique',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_unaryIterationNaturalRange',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_unaryIterationUnique',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_unaryIterationZeroIff',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_unaryIterationSuccessorIff',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_unaryIterationAllInternalCounts',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_forallClosureUniformTyping',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_forallClosureTypingIff',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_forallClosureClosedIff',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_forallClosureClosedExistsUnique',
                    'PPAC.Migration.Internal.ObjectForallClosure.native_forallClosureAllInternalCounts',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_doubleShiftExists',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_doubleShiftMap',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_doubleShiftEdgesIff',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_doubleShiftUnique',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaIndexGraphExists',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaIndexMap',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaIndexZeroIff',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaCollectionOneIff',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaSeparationTailIff',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaCollectionTailIff',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaIndexStateExists',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaIndexCodeExists',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaIndexRenameLaw',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaIndexRenameAt',
                    'PPAC.Migration.Internal.ObjectSchemaIndex.native_schemaIndexSystemExists',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectBoundShiftUnique',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectBoundShiftRange',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectBoundShiftTargetType',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectBoundShiftExists',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectBoundShiftExistsUnique',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectSubsetUnique',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectSubsetTargetType',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectSubsetExists',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectSubsetTypedUnique',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectAtomicResultUnique',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectAtomicCompiledType',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectAtomicCompiledUnique',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectEqualitySameCode',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectAtomicTypedUnique',
                    'PPAC.Migration.Internal.ObjectProjectAtomic.native_projectAtomicAllInternalInputs',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceStateExists',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceStateUniqueFiber',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceStateEdgesIff',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceRecursors',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceActualCarrierRecursors',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceNaturalEvaluationExists',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceEvaluationUniqueFiber',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceTypedRecursiveIff',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceCodeCarrierExists',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceCodeAtCarrierIff',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceCodeGuards',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceNonNaturalCodeRejected',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceInvalidContextRejected',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceCodeOmegaIndependent',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceCodeRecursiveIff',
                    'PPAC.Migration.Internal.ObjectProjectSourceCode.native_projectSourceAllInternalRecursiveLaw',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerStateExists',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerStateUniqueFiber',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerStateEdgesIff',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerAllRecursors',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerActualCarrierRecursors',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerNaturalEvaluationExists',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerEvaluationStateUnique',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerProducedOutputRootCertificate',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerCarrierExists',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerAtActualCarrierIff',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerNaturalGuards',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerNonNaturalInputRejected',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerInvalidCoordinatesRejected',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerOmegaIndependent',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerConstantsActuallyProduced',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerThreeAtomsActuallyProduced',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerThreeAtomsTypedOutputExists',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerHistoryIndependentActualOutput',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerEvaluationStateUniqueFiber',
                    'PPAC.Migration.Internal.ObjectProjectCompiler.native_compilerActualHistoryFromValue',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerActualChildReadIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerGuardedChildQueryIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerAllInternalChildQueries',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerSuccessorQueryIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerScopedChildQueryIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerAllTwelveCasesIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerActualLocalRecursiveIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerActualStateRecursiveIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerAtEvaluationRecursiveIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerAtCarrierRecursiveIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerAllCandidatesRecursiveIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerRecursive.native_compilerAllInternalRecursiveLaw',
                    'PPAC.Migration.Internal.ObjectProjectCompilerTyping.native_compilerChildTypingFromMemberIH',
                    'PPAC.Migration.Internal.ObjectProjectCompilerTyping.native_compilerTwelveCasesTargetTyped',
                    'PPAC.Migration.Internal.ObjectProjectCompilerTyping.native_compilerOutputTypedFromMemberIH',
                    'PPAC.Migration.Internal.ObjectProjectCompilerTyping.native_compilerTypingPropertyStep',
                    'PPAC.Migration.Internal.ObjectProjectCompilerTyping.native_compilerTypingProgressive',
                    'PPAC.Migration.Internal.ObjectProjectCompilerTyping.native_compilerAllInternalOutputsTargetTyped',
                    'PPAC.Migration.Internal.ObjectProjectCompilerTyping.native_compilerInputTypingProperty',
                    'PPAC.Migration.Internal.ObjectProjectCompilerTyping.native_compilerActualOutputTargetTyped',
                    'PPAC.Migration.Internal.ObjectProjectCompilerTyping.native_compilerUntypedOutputRejected',
                    'PPAC.Migration.Internal.ObjectProjectCompilerComplete.native_compilerSourceAtomsActualOutput',
                    'PPAC.Migration.Internal.ObjectProjectCompilerComplete.native_compilerSourceChildOutputFromMemberIH',
                    'PPAC.Migration.Internal.ObjectProjectCompilerComplete.native_compilerSourceOutputFromMemberIH',
                    'PPAC.Migration.Internal.ObjectProjectCompilerComplete.native_compilerCompletenessPropertyStep',
                    'PPAC.Migration.Internal.ObjectProjectCompilerComplete.native_compilerCompletenessProgressive',
                    'PPAC.Migration.Internal.ObjectProjectCompilerComplete.native_compilerAllInternalCompletenessProperty',
                    'PPAC.Migration.Internal.ObjectProjectCompilerComplete.native_compilerSourceInputActualOutputExists',
                    'PPAC.Migration.Internal.ObjectProjectCompilerComplete.native_compilerAllInternalSourceOutputsExist',
                    'PPAC.Migration.Internal.ObjectProjectCompilerComplete.native_compilerSourceInputActualTypedOutputExists',
                    'PPAC.Migration.Internal.ObjectProjectCompilerUnique.native_compilerGuardedChildScalarUnique',
                    'PPAC.Migration.Internal.ObjectProjectCompilerUnique.native_compilerSuccessorChildScalarUnique',
                    'PPAC.Migration.Internal.ObjectProjectCompilerUnique.native_compilerAllCasesScalarUnique',
                    'PPAC.Migration.Internal.ObjectProjectCompilerUnique.native_compilerOutputsUniqueFromMemberIH',
                    'PPAC.Migration.Internal.ObjectProjectCompilerUnique.native_compilerScalarFunctionalityProgressive',
                    'PPAC.Migration.Internal.ObjectProjectCompilerUnique.native_compilerAllInternalOutputsScalarUnique',
                    'PPAC.Migration.Internal.ObjectProjectCompilerUnique.native_compilerActualOutputsScalarUnique',
                    'PPAC.Migration.Internal.ObjectProjectCompilerUnique.native_compilerActualUniqueOutputFiber',
                    'PPAC.Migration.Internal.ObjectProjectCompilerUnique.native_compilerSourceActualTypedUniqueOutputExists',
                    'PPAC.Migration.Internal.ObjectProjectCompilerUnique.native_compilerAllInternalSourceTypedUniqueOutputExists',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerSourceChildValidityFromMemberIH',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerActualCasesRecoverSourceGrammar',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerInputValidFromMemberIH',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerSourceValidityProgressive',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerAllInternalActualInputsValid',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerActualInputValid',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerSourceAcceptanceIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerSourceTypedUniqueAcceptanceIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerAllInternalSourceAcceptanceIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerAllInternalSourceTypedUniqueAcceptanceIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerClosedSourceTypedUniqueAcceptanceIff',
                    'PPAC.Migration.Internal.ObjectProjectCompilerSourceValid.native_compilerInvalidSourceRejected',






                    } or name.startswith((
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
    arithmetic_groups = {




        "ObjectProjectCompilerSourceValid": ('compilerSourceChildValidityFromMemberIH', 'compilerActualCasesRecoverSourceGrammar', 'compilerInputValidFromMemberIH', 'compilerSourceValidityProgressive', 'compilerAllInternalActualInputsValid', 'compilerActualInputValid', 'compilerSourceAcceptanceIff', 'compilerSourceTypedUniqueAcceptanceIff', 'compilerAllInternalSourceAcceptanceIff', 'compilerAllInternalSourceTypedUniqueAcceptanceIff', 'compilerClosedSourceTypedUniqueAcceptanceIff', 'compilerInvalidSourceRejected'),
        "ObjectProjectCompilerUnique": ('compilerGuardedChildScalarUnique', 'compilerSuccessorChildScalarUnique', 'compilerAllCasesScalarUnique', 'compilerOutputsUniqueFromMemberIH', 'compilerScalarFunctionalityProgressive', 'compilerAllInternalOutputsScalarUnique', 'compilerActualOutputsScalarUnique', 'compilerActualUniqueOutputFiber', 'compilerSourceActualTypedUniqueOutputExists', 'compilerAllInternalSourceTypedUniqueOutputExists'),
        "ObjectProjectCompilerComplete": ('compilerSourceAtomsActualOutput', 'compilerSourceChildOutputFromMemberIH', 'compilerSourceOutputFromMemberIH', 'compilerCompletenessPropertyStep', 'compilerCompletenessProgressive', 'compilerAllInternalCompletenessProperty', 'compilerSourceInputActualOutputExists', 'compilerAllInternalSourceOutputsExist', 'compilerSourceInputActualTypedOutputExists'),
        "ObjectProjectCompilerTyping": ('compilerChildTypingFromMemberIH', 'compilerTwelveCasesTargetTyped', 'compilerOutputTypedFromMemberIH', 'compilerTypingPropertyStep', 'compilerTypingProgressive', 'compilerAllInternalOutputsTargetTyped', 'compilerInputTypingProperty', 'compilerActualOutputTargetTyped', 'compilerUntypedOutputRejected'),
        "ObjectProjectCompilerRecursive": ('compilerActualChildReadIff', 'compilerGuardedChildQueryIff', 'compilerAllInternalChildQueries', 'compilerSuccessorQueryIff', 'compilerScopedChildQueryIff', 'compilerAllTwelveCasesIff', 'compilerActualLocalRecursiveIff', 'compilerActualStateRecursiveIff', 'compilerAtEvaluationRecursiveIff', 'compilerAtCarrierRecursiveIff', 'compilerAllCandidatesRecursiveIff', 'compilerAllInternalRecursiveLaw'),
        "ObjectProjectCompiler": ('compilerStateExists', 'compilerStateUniqueFiber', 'compilerStateEdgesIff', 'compilerAllRecursors', 'compilerActualCarrierRecursors', 'compilerNaturalEvaluationExists', 'compilerEvaluationStateUnique', 'compilerProducedOutputRootCertificate', 'compilerCarrierExists', 'compilerAtActualCarrierIff', 'compilerNaturalGuards', 'compilerNonNaturalInputRejected', 'compilerInvalidCoordinatesRejected', 'compilerOmegaIndependent', 'compilerConstantsActuallyProduced', 'compilerThreeAtomsActuallyProduced', 'compilerThreeAtomsTypedOutputExists', 'compilerHistoryIndependentActualOutput', 'compilerEvaluationStateUniqueFiber', 'compilerActualHistoryFromValue'),
        "ObjectProjectSourceCode": ('projectSourceStateExists', 'projectSourceStateUniqueFiber', 'projectSourceStateEdgesIff', 'projectSourceRecursors', 'projectSourceActualCarrierRecursors', 'projectSourceNaturalEvaluationExists', 'projectSourceEvaluationUniqueFiber', 'projectSourceTypedRecursiveIff', 'projectSourceCodeCarrierExists', 'projectSourceCodeAtCarrierIff', 'projectSourceCodeGuards', 'projectSourceNonNaturalCodeRejected', 'projectSourceInvalidContextRejected', 'projectSourceCodeOmegaIndependent', 'projectSourceCodeRecursiveIff', 'projectSourceAllInternalRecursiveLaw'),
        "ObjectProjectAtomic": ('projectBoundShiftUnique', 'projectBoundShiftRange', 'projectBoundShiftTargetType', 'projectBoundShiftExists', 'projectBoundShiftExistsUnique', 'projectSubsetUnique', 'projectSubsetTargetType', 'projectSubsetExists', 'projectSubsetTypedUnique', 'projectAtomicResultUnique', 'projectAtomicCompiledType', 'projectAtomicCompiledUnique', 'projectEqualitySameCode', 'projectAtomicTypedUnique', 'projectAtomicAllInternalInputs'),
        "ObjectSchemaIndex": ('doubleShiftExists', 'doubleShiftMap', 'doubleShiftEdgesIff', 'doubleShiftUnique', 'schemaIndexGraphExists', 'schemaIndexMap', 'schemaIndexZeroIff', 'schemaCollectionOneIff', 'schemaSeparationTailIff', 'schemaCollectionTailIff', 'schemaIndexStateExists', 'schemaIndexCodeExists', 'schemaIndexRenameLaw', 'schemaIndexRenameAt', 'schemaIndexSystemExists'),
        "ObjectForallClosure": ('unaryIterationExistsUnique', 'unaryIterationNaturalRange', 'unaryIterationUnique', 'unaryIterationZeroIff', 'unaryIterationSuccessorIff', 'unaryIterationAllInternalCounts', 'forallClosureUniformTyping', 'forallClosureTypingIff', 'forallClosureClosedIff', 'forallClosureClosedExistsUnique', 'forallClosureAllInternalCounts'),
        "ObjectFixedAxiomTest": ('fixedPacketExists', 'fixedPacketNatural', 'fixedPacketUnique', 'fixedPacketTagsDisjoint', 'fixedPacketAtValue'),
        "ObjectProofTreeEquation": ('proofTreeEquationImpliesLocalClosure', 'proofTreeEquationReverseProgressive', 'proofTreeEquationAllCodeUnique', 'proofTreeEquationPointUnique', 'proofTreeEquationRootUnique', 'proofTreeEquationTwoSolutions', 'proofTreeEquationNodeNatural', 'proofTreeEquationSolutionNatural', 'proofTreeCanonicalNodeEquation'),
        "ObjectProofTreeInduction": ('proofTreePropertyStepWithMemberIH', 'proofTreePropertyProgressive', 'proofTreeInternalInduction', 'proofTreePointInduction', 'proofTreeRootProperty', 'proofTreeRejectNodeFromProperty', 'proofTreeRejectRootFromProperty'),
        "ObjectProofTreeNode": ('proofNodeFieldLocalIff', 'proofNodeActualTagLocalIff', 'proofNodeVariableChildIff', 'proofNodeAllChildrenIff', 'proofNodePayloadFieldBelow', 'proofNodeSixCasesForward', 'proofNodeSixCasesBackward', 'proofNodeExactSixCasesIff', 'proofRootExactNodeSixCasesIff'),
        "ObjectProofTreeRoot": ('proofRootOneNonempty', 'proofRootOneMembership', 'proofRootZeroGuardIff', 'proofRootPayloadConstructorIff', 'proofRootActualLocalCondition', 'proofRootClosedFieldsForward', 'proofRootClosedFieldsBackward', 'proofRootExactClosedFieldsIff'),
        "ObjectProofTreeTrace": ('proofTreeAllTraceRootsExist', 'proofTreeTraceRange', 'proofTreeAllRootsMembershipIff', 'proofTreeAllRootsClosed', 'proofTreeTwelveRuleTracedStepIff', 'proofTreeFullRecursiveTraceIff', 'proofTreeNodeEntryRecursiveIff', 'proofTreeRootEntryRecursiveIff', 'proofTreeTwelveBranchAllAssignmentBounds', 'proofTreeTwelveBranchTraceComposition'),
        "ObjectProofBaseNodes": ('proofLogicalNumericHeadIff', 'proofLogicalQueryConstructorIff', 'proofLogicalQueryNormalizedIff', 'proofLogicalAllAssignmentBounds', 'proofLogicalBoundedMatrixIff', 'proofLogicalWholeNodeIff', 'proofTheoryNumericHeadIff', 'proofTheoryFormulaQueryIff', 'proofTheoryParameterizedAxiomQueryIff', 'proofTheoryParameterizedAllQueriesIff', 'proofTheoryAllAssignmentBounds', 'proofTheoryParameterizedBoundedMatrixIff', 'proofTheoryParameterizedWholeNodeIff', 'proofSixRulesParameterizedActualShapeTableIff', 'proofSixRulesParameterizedSelectedNodesIff', 'proofSixRulesParameterizedActualTableSpecificationIff'),
        "ObjectLogicalAbstract": ('logicalRule21AtSuccessorsQueriesIff', 'logicalRule21AtOneQueriesIff', 'logicalRule21AllQueriesIff', 'logicalRule21AllAssignmentBounds', 'logicalRule21NumericNestedHeadIff', 'logicalRule21WholeNormalizedNodeIff', 'logicalRule24AtSuccessorsQueriesIff', 'logicalRule24AtOneQueriesIff', 'logicalRule24AllQueriesIff', 'logicalRule24AllAssignmentBounds', 'logicalRule24NumericNestedHeadIff', 'logicalRule24WholeNormalizedNodeIff', 'logicalAllTwentySevenWholeNodesIff', 'logicalAllTwentySevenActualShapeTableIff', 'logicalAllTwentySevenActualTableSpecificationIff'),
        "ObjectLogicalStatic": ('staticLogicalAllQueriesIff', 'staticLogicalRule0WholeNormalizedNodeIff', 'staticLogicalRule0AllAssignmentBounds', 'staticLogicalRule0NumericNestedHeadIff', 'staticLogicalRule1WholeNormalizedNodeIff', 'staticLogicalRule1AllAssignmentBounds', 'staticLogicalRule1NumericNestedHeadIff', 'staticLogicalRule2WholeNormalizedNodeIff', 'staticLogicalRule2AllAssignmentBounds', 'staticLogicalRule2NumericNestedHeadIff', 'staticLogicalRule3WholeNormalizedNodeIff', 'staticLogicalRule3AllAssignmentBounds', 'staticLogicalRule3NumericNestedHeadIff', 'staticLogicalRule4WholeNormalizedNodeIff', 'staticLogicalRule4AllAssignmentBounds', 'staticLogicalRule4NumericNestedHeadIff', 'staticLogicalRule5WholeNormalizedNodeIff', 'staticLogicalRule5AllAssignmentBounds', 'staticLogicalRule5NumericNestedHeadIff', 'staticLogicalRule6WholeNormalizedNodeIff', 'staticLogicalRule6AllAssignmentBounds', 'staticLogicalRule6NumericNestedHeadIff', 'staticLogicalRule7WholeNormalizedNodeIff', 'staticLogicalRule7AllAssignmentBounds', 'staticLogicalRule7NumericNestedHeadIff', 'staticLogicalRule8WholeNormalizedNodeIff', 'staticLogicalRule8AllAssignmentBounds', 'staticLogicalRule8NumericNestedHeadIff', 'staticLogicalRule9WholeNormalizedNodeIff', 'staticLogicalRule9AllAssignmentBounds', 'staticLogicalRule9NumericNestedHeadIff', 'staticLogicalRule10WholeNormalizedNodeIff', 'staticLogicalRule10AllAssignmentBounds', 'staticLogicalRule10NumericNestedHeadIff', 'staticLogicalRule11WholeNormalizedNodeIff', 'staticLogicalRule11AllAssignmentBounds', 'staticLogicalRule11NumericNestedHeadIff', 'staticLogicalRule12WholeNormalizedNodeIff', 'staticLogicalRule12AllAssignmentBounds', 'staticLogicalRule12NumericNestedHeadIff', 'staticLogicalRule13WholeNormalizedNodeIff', 'staticLogicalRule13AllAssignmentBounds', 'staticLogicalRule13NumericNestedHeadIff', 'staticLogicalRule14WholeNormalizedNodeIff', 'staticLogicalRule14AllAssignmentBounds', 'staticLogicalRule14NumericNestedHeadIff', 'staticLogicalRule15WholeNormalizedNodeIff', 'staticLogicalRule15AllAssignmentBounds', 'staticLogicalRule15NumericNestedHeadIff', 'staticLogicalRule16WholeNormalizedNodeIff', 'staticLogicalRule16AllAssignmentBounds', 'staticLogicalRule16NumericNestedHeadIff', 'staticLogicalRule17WholeNormalizedNodeIff', 'staticLogicalRule17AllAssignmentBounds', 'staticLogicalRule17NumericNestedHeadIff', 'staticLogicalRule18WholeNormalizedNodeIff', 'staticLogicalRule18AllAssignmentBounds', 'staticLogicalRule18NumericNestedHeadIff', 'staticLogicalRule19WholeNormalizedNodeIff', 'staticLogicalRule19AllAssignmentBounds', 'staticLogicalRule19NumericNestedHeadIff', 'staticLogicalRule22WholeNormalizedNodeIff', 'staticLogicalRule22AllAssignmentBounds', 'staticLogicalRule22NumericNestedHeadIff', 'staticLogicalRule26WholeNormalizedNodeIff', 'staticLogicalRule26AllAssignmentBounds', 'staticLogicalRule26NumericNestedHeadIff'),
        "ObjectLogicalInstantiate": ('logicalTwentyTwentyThreeAtBoundQueriesIff', 'logicalTwentyTwentyThreeAllQueriesIff', 'logicalTwentyTwentyThreeAllAssignmentBounds', 'logicalTwentyTwentyThreeBoundedMatrixIff', 'logicalTwentyTwentyThreeWholeNodeIff', 'logicalTwentyTwentyThreeWholeNormalizedNodeIff', 'logicalTwentyFiveAtBoundQueriesIff', 'logicalTwentyFiveAllQueriesIff', 'logicalTwentyFiveAllAssignmentBounds', 'logicalTwentyFiveBoundedMatrixIff', 'logicalTwentyFiveWholeNodeIff', 'logicalTwentyFiveWholeNormalizedNodeIff', 'logicalRule20NestedHeadIff', 'logicalRule23NestedHeadIff', 'logicalRule25NestedHeadIff'),
        "ObjectInstantiateFormula": ('modeTwoAllTypedTermAgreement', 'modeTwoAllTypedTermUniqueFiber', 'modeTwoTermPromiseDerived', 'modeTwoArgumentFieldsProgramIff', 'modeTwoWholeArgumentProgramIff', 'modeTwoGuardedArgumentProgramIff', 'modeTwoFourAtomicRunIff', 'modeTwoFourAtomicProgramIff', 'modeTwoActualBinderPrefixFromInduction', 'modeTwoAllElevenProgramFromInductionIff', 'modeTwoUniformCorrectnessProgressive', 'modeTwoAllInternalFormulaCorrect', 'modeTwoAllInternalRootsCorrect', 'modeTwoAllInternalWholeFormulaExecutionIff', 'modeTwoAllInternalWholeFormulaProgramIff', 'modeTwoActualHistoryAgreementDischarged', 'modeTwoAgreedActualHistoryExistsDischarged', 'modeTwoActualRootWholeFormulaExecutionIff', 'modeTwoActualRootWholeFormulaProgramIff', 'modeTwoActualInstantiateTopAtCodesIff', 'modeTwoActualInstantiateTopIff', 'modeTwoActualInstantiateTopSourceType', 'modeTwoActualInstantiateTopGuardedIff'),
        "ObjectInstantiateBinder": ('modeTwoBinderSuccessorPoint', 'modeTwoBinderContextGeometry', 'modeTwoBinderBelowCaseIff', 'modeTwoBinderPointCaseIff', 'modeTwoBinderBoundCovarianceIff', 'modeTwoBinderFreeCovarianceIff', 'modeTwoBinderFreshZeroFieldIff', 'modeTwoBinderBoundSuccessorFieldIff', 'modeTwoBinderFreeFieldIff', 'modeTwoBinderVariableCompatibility', 'modeTwoBinderFrameAtWitnesses', 'modeTwoActualBinderFrame'),
        "ObjectInstantiateRoot": ('modeTwoClosedParameterBinderRenameIff', 'modeTwoVariableAtPointIff', 'modeTwoVariableBelowIff', 'modeTwoActualRootVariableFieldIff', 'modeTwoActualRootVariableCompatibility', 'modeTwoActualRootFrame', 'modeTwoActualRootTermProgramIff', 'modeTwoActualRootTermCodedIff', 'modeTwoActualRootGuardedTermCodedIff'),
        "ObjectNaturalAddition": ("fiber", "closure", "zero", "successor", "leftZero"),
        "ObjectNaturalMultiplication": ("fiber", "closure", "zero", "successor", "leftZero"),
        "ObjectNaturalAdditionAlgebra": ("leftSuccessor", "commutative", "associative", "cancelRight", "cancelLeft"),
        "ObjectNaturalAdditionOrder": ("bounds", "zero", "strictRight", "strictLeft"),
        "ObjectNaturalAdditionReassociation": ("swap", "interchange"),
        "ObjectNaturalMultiplicationAlgebra": ("sumRight", "sumLeft", "leftSuccessor", "commutative", "associative", "unit"),
        "ObjectNaturalOrder": ('total', 'transitive', 'antisymmetric', 'successor'),
        "ObjectNaturalDifference": ('order', 'fiber', 'strict', 'zero'),
        "ObjectNaturalAdditiveOrder": ('rightWeak', 'rightStrict', 'leftWeak', 'leftStrict'),
        "ObjectNaturalMultiplicativeOrder": ('zero', 'rightMonotone', 'rightWeak', 'rightStrict', 'rightCancel', 'leftMonotone', 'leftWeak', 'leftStrict', 'leftCancel'),
        "ObjectNaturalNumericBounds": ('unit', 'factors', 'square', 'squareStrict', 'squareInjective'),
        "ObjectGodelPair": ('fiber', 'closure', 'valueUnique', 'components', 'injective', 'lowerBand', 'upperBand'),
        "ObjectGodelUnpair": ('zero', 'successor', 'total', 'characterization', 'fiber', 'bounded'),
        "ObjectStructuralNode": ('encodeFiber', 'closure', 'positive', 'components', 'injective', 'positiveIff', 'decodeTotal', 'decodeFiber', 'decodeBounds'),
        "ObjectStructuralList": ('nilValue', 'nilFiber', 'consTag', 'consFiber', 'closure', 'bounds', 'injective', 'disjoint', 'leafZero'),
        "ObjectStructuralListTrace": ('base', 'append', 'nilValid', 'consValid', 'range', 'recursive', 'consIff', 'positive', 'zeroRejected', 'prefix'),
        "ObjectStructuralListLength": ('prefixTrace', 'knownTailEdge', 'nilEmpty', 'consPredecessor', 'unique', 'traceUnique', 'fiber', 'range', 'exists'),
        "ObjectStructuralListProjection": ('total', 'functional', 'range', 'cons', 'nil', 'offCons', 'recursors', 'fiber', 'closure', 'zero', 'next'),
        "ObjectStructuralListEnd": ('coupled', 'shiftEqual', 'shiftIff', 'consShift', 'terminal', 'existsTerminal', 'uniquePair', 'traceSeed', 'traceRecovery'),
        "ObjectStructuralListPositions": ('reverseStep', 'advance', 'oldIndex', 'swap', 'allPositions', 'at', 'iff', 'reverseExists'),
        "ObjectStructuralListFields": ('valueFiber', 'valueRange', 'zero', 'successor', 'pairFiber', 'rawExists', 'edgeLaw', 'complete', 'graphUnique', 'fiber', 'atLength', 'decode', 'decodeIff', 'decodeUnique', 'traceHead'),
        "ObjectStructuralListEncode": ('nilLength', 'consLength', 'emptyLength', 'offset', 'suffixZero', 'suffixCons', 'suffix', 'fullSuffix', 'graphRecovery', 'zeroFields', 'exists', 'valid', 'readback'),
        "ObjectStructuralListRoundTrip": ('predecessor', 'consView', 'heads', 'tails', 'codeUnique', 'sameGraph', 'encodedUnique', 'encodingFiber', 'decodeThenEncode', 'roundTrip'),
        "ObjectStructuralListCheck": ('termination', 'exists', 'fiber', 'indexUnique', 'valueUnique', 'preservesStep', 'invariant', 'acceptValue', 'rejectValue', 'acceptsIff', 'rejectsIff', 'exclusive', 'decodeAccepted', 'nilAccepts', 'zeroRejects', 'classification'),
        "ObjectStructuralFieldBounds": ('fieldBound', 'edgeBound', 'rawFieldBound', 'rawEdgeBound'),
        "ObjectStructuralTreeOperator": ('shapeBound', 'childrenIff', 'leafGood', 'positiveGood', 'range', 'zero', 'functional', 'recursors', 'ordinalFiber', 'actualUnits'),
        "ObjectStructuralTreeCheck": ('fiber', 'naturalValue', 'valueUnique', 'edgeIff', 'history', 'range', 'goodIff', 'acceptsIff', 'rejectsIff', 'fixedClassification', 'validAccepts', 'invalidRejects', 'markerTransport', 'classification', 'exclusive', 'invalidIffNot', 'recursiveIff', 'decodedFiber', 'decodedIff', 'decodeUnique'),
        "ObjectStructuralTreeEncode": ('exists', 'fiber', 'range', 'unique', 'shapeUnique', 'validity', 'readback', 'codeRecovery'),
        "ObjectSyntaxConstructors": ('numeralExists', 'numeralUnique', 'numeralRange', 'numeralLess', 'numeralDifferent', 'forestExists', 'forestUnique', 'forestMember', 'forestLength', 'nodeFiber', 'nodeMember', 'constructorFiber', 'constructorDisjoint', 'constructorMember', 'scalarFiber', 'scalarInjective', 'variableFiber', 'variableDisjoint'),
        "ObjectSyntaxTerms": ('forestInput', 'nodeInput', 'constructorInput', 'forestArity', 'nodeArity', 'indexNatural', 'indexInjective', 'variableDecode', 'indexFiber', 'branchScope', 'branchDecode', 'scope', 'termExists', 'termRange', 'termDecode', 'branchExclusive', 'decodedExclusive', 'rejectScope', 'rejectEmpty', 'rejectTag', 'rejectFunction', 'rejectArity', 'rejectScalar', 'branchEmpty', 'rawRejectTag', 'rawRejectFunction', 'rawRejectUnknownTag'),
        "ObjectSyntaxAtoms": ('zeroTwo', 'zeroIndex', 'nullaryContexts', 'falseTwo', 'memberTypes', 'equalTypes', 'nullaryExists', 'memberExists', 'equalExists', 'memberFields', 'equalFields', 'memberValueUnique', 'equalValueUnique', 'memberDecode', 'memberFiber', 'equalDecode', 'equalFiber', 'atomicContexts', 'atomicRange', 'nullaryAtomic', 'memberAtomic', 'equalAtomic', 'symbolCheck', 'badSymbol', 'unknownAtomicTag'),
        "ObjectSyntaxLogical": ('readAtValue', 'advancedAtSuccessor', 'successorContext', 'singleTypes', 'negationTypes', 'binaryTypes', 'quantifierTypes', 'singleExists', 'binaryExists', 'quantifierExists', 'singleFields', 'binaryFields', 'singleBound', 'binaryBounds', 'singleUnique', 'binaryUnique', 'singleRange', 'singleDecode', 'binaryRange', 'binaryDecode', 'singleFiber', 'binaryFiber', 'singleNotCheck', 'binaryNotReads', 'quantifierNotRead', 'singleUnknownTag', 'binaryUnknownTag'),
        "ObjectSyntaxContextCarrier": ('pairSubset', 'orderedMember', 'pairExists', 'stateMember', 'exists', 'unique'),
        "ObjectSyntaxTypeStates": ('localContext', 'localRange', 'rowAtPair', 'stateExists', 'stateFiber', 'stateUnique', 'stateSubset', 'stateUniverse', 'noJunk', 'stateEdge', 'badContext', 'offNatural', 'total', 'deterministic', 'recursors', 'ordinalFiber', 'actualCarriers', 'evaluationExists', 'naturalEvaluation', 'evaluationUnique', 'evaluationFiber', 'graphsAgree', 'graphValue', 'history', 'evaluationSubset', 'evaluationUniverse', 'evaluationOffNatural', 'typedAtValue', 'readTyped', 'typedRejectCode', 'typedRejectContext', 'introduceAtomic', 'introduceNegation', 'introduceBinary', 'introduceQuantifier'),
        "ObjectSyntaxTypeRecursive": ('read', 'advanced', 'check', 'single', 'binary', 'local', 'atState', 'atValue', 'recursive', 'universal', 'actualSystem', 'existence'),
        "ObjectFormulaCode": ('carrierExists', 'carrierUnique', 'atCarrier', 'guards', 'rejectCode', 'rejectContext', 'omegaIndependent', 'rootTransport', 'boundTransport', 'freeTransport', 'omegaTransport', 'advancedTransfer', 'singleTransfer', 'binaryTransfer', 'criterionTransfer', 'recursive', 'universal', 'nullaryTypes', 'memberTypes', 'equalTypes', 'negationTypes', 'binary0Types', 'binary1Types', 'binary2Types', 'binary3Types', 'forallTypes', 'existsTypes', 'quantifierTypes', 'unknownTag'),
        "ObjectFormulaCodeConstruction": ('fiber', 'existsOfFiber', 'nullaryLaw', 'nullaryFiber', 'nullaryExists', 'memberLaw', 'memberFiber', 'memberExists', 'equalLaw', 'equalFiber', 'equalExists', 'negationLaw', 'negationFiber', 'negationExists', 'forallLaw', 'forallFiber', 'forallExists', 'existsLaw', 'existsFiber', 'existsExists', 'binary0Law', 'binary0Fiber', 'binary0Exists', 'binary1Law', 'binary1Fiber', 'binary1Exists', 'binary2Law', 'binary2Fiber', 'binary2Exists', 'binary3Law', 'binary3Fiber', 'binary3Exists', 'membershipFiber', 'forestValid', 'nodeShape', 'constructorShape', 'shapeUnique', 'acceptedShape', 'reencoding', 'roundTrip', 'forestArity', 'nodeArity', 'constructorArity', 'constructorTag', 'allowedArity', 'rejectArity'),
        "ObjectSyntaxTypedFields": ('numeralMembers', 'indexMember', 'forestValue', 'forestEdge', 'forestFull', 'forestAll', 'nodeAll', 'nodeValue', 'constructorAll', 'constructorValue', 'slot', 'checked', 'codeField', 'termField', 'advancedField', 'zeroField', 'memberTyping', 'equalTyping', 'negationTyping', 'binaryTyping', 'quantifierTyping', 'quantifierSuccessor'),
        "ObjectFormulaCodeTreeValidity": ('graphChildren', 'node', 'constructor', 'scalar', 'variable', 'termBranch', 'term', 'nullary', 'member', 'equal', 'atomic', 'advancedChild', 'singleCase', 'binaryCase', 'atContext', 'property', 'progressive', 'allProperties', 'code', 'rejectNonTree', 'decodedTree', 'treeChildren', 'typedCases', 'typedData', 'typedFiber', 'rejectCases', 'rejectData', 'dataTreeValid'),
        "ObjectFormulaCodeTypedDecode": ('slotIndex', 'slotNatural', 'slotInputs', 'slotsFull', 'slotsAll', 'graphEquality', 'fieldsGraphSubst', 'forestRecover', 'constructorRecover', 'knownTypes', 'codeFromSlots', 'rootSlot', 'arity0', 'arity1', 'arity2', 'arity3', 'rootCheck', 'casesCode', 'dataCode', 'dataIff', 'casesIff', 'fiberCode', 'fiberIff', 'rejectFiberIff', 'classification'),
        "ObjectSyntaxRenameTerm": ('sourceContexts', 'targetContexts', 'selectedMap', 'edgeSource', 'edgeTarget', 'valueExists', 'introBranch', 'sourceBranch', 'targetBranch', 'sourceTerm', 'targetTerm', 'outputNatural', 'oppositeBranches', 'branchUnique', 'unique', 'existsAtIndex', 'existsBranch', 'existsTerm', 'fiber', 'termOfExists', 'termOfFiber', 'existsIff', 'fiberIff', 'knownBranch', 'knownTerm', 'rejectEdge', 'diagonalAt', 'branchIdentity', 'identity', 'outputSubst', 'reflexive'),
        "ObjectSyntaxIndexLift": ('relationUnique', 'pairTotal', 'pairGraph', 'pairEdge', 'pairComplete', 'graphExists', 'graphFiber', 'graphUnique', 'graphSequence', 'zeroMember', 'successorMember', 'predecessorMember', 'successorInjective', 'zeroOutput', 'successorOutput', 'sourceMember', 'targetMember', 'valueUnique', 'pointExists', 'pointFiber', 'liftTotal', 'liftOutputs', 'targetMap', 'liftExists', 'liftFiber', 'liftUnique', 'liftEdge', 'liftAll', 'liftZero', 'liftSuccessor', 'mapsLifted', 'newBoundFixed', 'oldBoundShifted', 'freePreserved', 'liftSystem'),
        "ObjectSyntaxMapCodeState": ('omegaSequence', 'codeNatural', 'codeValid', 'uniqueCode', 'uniqueGraph', 'sourceGraphRecovery', 'existsMapCode', 'codeFiber', 'mapNatural', 'mapContexts', 'mapValid', 'graphFiber', 'mapFiberIff', 'liftAtSource', 'liftExistsAtSource', 'liftExists', 'liftUniqueAtSource', 'liftInputCode', 'liftOutputCode', 'liftOutputNatural', 'liftCodeUnique', 'liftCodeFiber', 'stateInputs', 'cellNatural', 'fieldNatural', 'sameField', 'sameFields', 'uniqueCell', 'stateFiber', 'uniqueParams', 'actualDecode', 'recognizedNatural', 'stateDecodeIff', 'actualStateSystem', 'introStateRecognition'),
        "ObjectSyntaxRenameOperator": ('containsAtState', 'queryAtValue', 'queryAtState', 'advancedFreeMap', 'advancedIntro', 'nullaryCase', 'membershipCase', 'equalityCase', 'negationCase', 'binaryCase', 'quantifierCase', 'localGraphs', 'rowIntro', 'rowAtState', 'rowRecognized', 'rowSourceNatural', 'valueMember', 'valueExists', 'valueSubset', 'valueUniverse', 'valueUnique', 'valueFiber', 'memberRecognized', 'valueAtState', 'offNatural', 'operatorTotal', 'operatorDeterministic', 'recursors', 'graphFiber', 'carrierRecursors', 'evaluationExists', 'naturalEvaluationExists', 'evaluationUnique', 'evaluationFiber', 'naturalEvaluationFiber', 'graphAgreement', 'graphEdgeValue', 'prefix', 'evaluationSubset', 'evaluationUniverse', 'evaluationOffNatural', 'existence'),
        "ObjectSyntaxRenameRecursive": ('intro', 'rejectCode', 'legal', 'targetType', 'containsCriterion', 'atValue', 'read', 'advanced', 'check', 'singleFields', 'singleCase', 'binaryFields', 'binaryCase', 'allCases', 'local', 'recursiveAtValue', 'recursive', 'sourceType', 'universal', 'actualSystem', 'existence'),
        "ObjectSyntaxRenameOutput": ('liftSuccessors', 'liftParameters', 'advancedAtLift', 'renamedInput', 'renamedNatural', 'inputNatural', 'existsFromFiber', 'existsFromRenamed', 'fiberIntro', 'propertyAt', 'earlierAt', 'atomicFilter', 'nullaryLocal', 'nullarySelf', 'nullaryUnique', 'nullaryFiber', 'nullaryAllParameters'),
        "ObjectSyntaxRenameAtomic": ('graphCases', 'casesFromJudgment', 'atomicFromJudgment', 'introFromCases', 'equalDataUnique', 'equalRelationUnique', 'equalAtOutputs', 'equalExistsAtGraphs', 'equalUniqueAtGraphs', 'equalFiberAtGraphs', 'equalFiber', 'equalAllParameters', 'equalBaseProperty', 'memberDataUnique', 'memberRelationUnique', 'memberAtOutputs', 'memberExistsAtGraphs', 'memberUniqueAtGraphs', 'memberFiberAtGraphs', 'memberFiber', 'memberAllParameters', 'memberBaseProperty', 'atomicProperty', 'atomicFiber', 'atomicExists'),
        "ObjectSyntaxRenameTotal": ('tagFilter', 'tagJudgment', 'fiberUnique', 'propertyUnique', 'checkTarget', 'checkNatural', 'checkUnique', 'checkExists', 'singleDataUnique', 'singleRelationUnique', 'binaryDataUnique', 'binaryRelationUnique', 'negationAtOutput', 'negationExistsAtGraphs', 'negationFiber', 'negationPropertyStep', 'forallAtOutput', 'forallExistsAtGraphs', 'forallFiber', 'forallPropertyStep', 'existsAtOutput', 'existsExistsAtGraphs', 'existsFiber', 'existsPropertyStep', 'binaryAtOutputs', 'binaryExistsAtGraphs', 'binaryFiber', 'binaryPropertyStep', 'codePropertyStep', 'propertyStep', 'progressive', 'allProperties', 'naturalProperty', 'actualFiber', 'actualExists', 'fiberIffInput', 'existsIffInput', 'rejectInput', 'unique', 'uniqueOutput'),
        "ObjectSyntaxRenameFields": ('introBranch', 'branchTarget', 'sourceCaseIff', 'checkSource', 'equalityRawIff', 'membershipRawIff', 'singleRawIff', 'binaryRawIff', 'equalityIff', 'equalityInput', 'membershipIff', 'membershipInput', 'negationIff', 'negationCodeIff', 'negationInput', 'forallIff', 'forallCodeIff', 'forallInput', 'existsIff', 'existsCodeIff', 'existsInput', 'binaryIff', 'binaryCodeIff', 'binaryInput', 'nullaryIff', 'quantifiedAtLift'),
        "ObjectSyntaxRenameIdentity": ('graphExists', 'graphEdges', 'graphUnique', 'graphDiagonal', 'graphIndexMap', 'mapExists', 'codeExists', 'codeMap', 'codeAtGraph', 'codeEncodedIff', 'liftValueDiagonal', 'liftGraphDiagonal', 'liftCode', 'formulaReflexive', 'formulaIdentity', 'formulaIdentityIff'),
        "ObjectSyntaxCompose": ('valueSource', 'valueTarget', 'valueUnique', 'pointExists', 'pointFiber', 'relationTotal', 'graphExists', 'graphFiber', 'graphUnique', 'graphEdges', 'graphTargetMap', 'codeFirst', 'codeSecond', 'codeOutput', 'codeReadSources', 'codeReadGraphs', 'codeEncodedIff', 'codeEdges', 'codeExistsAtSources', 'codeExists', 'codeUnique', 'codeFiber', 'codeInputIff', 'termBranch', 'termCompose', 'termFactor', 'termCollapse', 'termComposeIff'),
        "ObjectSyntaxComposeLift": ('zero', 'shifted', 'valueForward', 'edgeForward', 'includedAgreement', 'included', 'equalGraphs', 'graphComposition', 'graphEdges', 'graphValues', 'liftedIffComposed', 'atSources', 'codedComposition', 'codedIff', 'middleEqual', 'mixedMiddle', 'mixedIff'),
        "ObjectSyntaxFormulaCompose": ('targetNegation', 'targetForall', 'targetExists', 'targetBinary', 'targetEquality', 'targetMembership', 'boundDiagramCode', 'freeDiagramCode', 'nullary', 'equalityFields', 'membershipFields', 'equality', 'membership', 'atomic', 'advancedCompose', 'checkCompose', 'negationFields', 'forallFields', 'existsFields', 'binaryFields', 'negation', 'forall', 'exists', 'binary', 'codeStep', 'diagramStep', 'mapCodeStep', 'propertyStep', 'progressive', 'allProperties', 'naturalProperty', 'forward', 'factor', 'collapse', 'composeIff'),
        "ObjectSyntaxFreeShift": ('graphExists', 'graphEdges', 'graphUnique', 'mapExists', 'mapFiber', 'mapUnique', 'mapEdges', 'codeExists', 'codeMap', 'codeNatural', 'codeInput', 'codeAtGraph', 'codeEncodedIff', 'codeUnique', 'codeFiber', 'codeInputIff', 'actualState', 'zeroState', 'codedEdges', 'freshAbsent', 'emptySource', 'emptyGraph', 'rangeUnique'),
        "ObjectSyntaxWeakenFree": ('identityUnique', 'identityLift', 'input', 'sourceType', 'targetType', 'outputNatural', 'existsOutput', 'atCodes', 'outputUnique', 'uniqueOutput', 'actualFiber', 'existsInputIff', 'fiberInputIff', 'actualState', 'negation', 'binary', 'quantified', 'forall', 'exists', 'nullary', 'equality', 'membership', 'boundTerm', 'freeTerm', 'freshFreeAbsent', 'emptyFreeAbsent', 'actualCodes', 'internalNegation', 'internalBinary', 'internalQuantified'),
        "ObjectSyntaxFreeSubstCodec": ('openTerm', 'decodedTarget', 'encodedNatural', 'encodedFree', 'decodedUnique', 'encodedUnique', 'decodedIndex', 'encodedTerms', 'decodeExists', 'encodeExists', 'decodeGraphUnique', 'encodeGraphUnique', 'encodedAtCode', 'decodedAtCode', 'encodedToDecoded', 'decodedToEncoded', 'indicesUnique', 'termsUnique', 'listProjection', 'mapProjection', 'fromList', 'fromMap', 'mapUnique', 'listUnique', 'mapFiber', 'mapExistsIff', 'mapFiberIff', 'listFiber', 'listExistsIff', 'listFiberIff', 'atGraph', 'fieldAtCode', 'fieldIsFree'),
        "ObjectFormulaFreeSubst": ('input', 'sourceType', 'targetType', 'outputNatural', 'existsOutput', 'atCodes', 'outputUnique', 'uniqueOutput', 'actualFiber', 'existsInputIff', 'fiberInputIff', 'negation', 'binary', 'quantified', 'forall', 'exists', 'nullary', 'equality', 'membership', 'boundTerm', 'freeTermField', 'actualCodes', 'internalNegation', 'internalBinary', 'internalQuantified'),
        "ObjectMixedTerm": ('input', 'sourceType', 'targetType', 'outputNatural', 'existsOutput', 'outputUnique', 'uniqueOutput', 'actualFiber', 'existsInputIff', 'fiberInputIff', 'atCode', 'imageGraphExists', 'pushExists', 'pushUnique', 'pushGuardedEdges', 'pushEdges', 'pushAtValue', 'bothExist', 'bothTarget', 'bothUnique', 'boundShiftExists'),
        "ObjectMixedBinder": ('prefixExists', 'prefixUnique', 'prefixEdges', 'prefixZero', 'prefixSuccessor', 'valueUnique', 'valueZero', 'valueSuccessor', 'valueTarget', 'valueSource', 'headTerm', 'headCode', 'headExists', 'headUnique', 'preparedExists', 'preparedUnique', 'preparedTarget', 'actualState', 'binderExists', 'binderUnique', 'binderTarget', 'binderAtWitnesses', 'binderInput', 'binderUniquePair', 'binderFiber', 'binderExistsIff', 'binderFiberIff', 'binderZero', 'binderBound', 'binderFree'),
        "ObjectMixedEnvironment": ('listType', 'fromFields', 'fieldType', 'imageEdges', 'codeExists', 'graphExists', 'codeInputIff', 'graphInputIff', 'codeUnique', 'graphUnique', 'atEncoding', 'codeFiber', 'codeFiberIff', 'graphFiber', 'graphFiberIff', 'pairCodes', 'pairGraphs', 'pairGraphUnique', 'pairCodeUnique', 'termInput', 'termSource', 'termTarget', 'termNatural', 'termExists', 'termAtGraphs', 'termUnique', 'termUniqueOutput', 'termFiber', 'termExistsIff', 'termFiberIff', 'termField', 'binderExists', 'binderUnique', 'binderAtGraphs', 'binderInputLists', 'binderOutputLists', 'binderInput', 'binderNatural', 'binderUniqueOutput', 'binderFiber', 'binderExistsIff', 'binderFiberIff', 'binderZero', 'binderBound', 'binderFree'),
        "ObjectMixedFormula": ('stateExists', 'stateInputIff', 'stateNatural', 'stateUnique', 'stateDecode', 'stateParamsUnique', 'containsAtState', 'readAtValue', 'readAtState', 'advancedQuery', 'operatorExists', 'operatorFiber', 'operatorUnique', 'operatorSubset', 'operatorRecognized', 'operatorMembership', 'recursors', 'carrier', 'graphExists', 'evaluationExists', 'evaluationFiber', 'evaluationUnique', 'history', 'judgmentRead', 'formulaSource', 'formulaTarget', 'formulaLegal', 'formulaInput', 'formulaNatural', 'recursiveIff', 'formulaFiber', 'formulaExists', 'formulaUnique', 'formulaUniqueOutput', 'formulaExistsIff', 'formulaFiberIff', 'formulaRejectInvalid', 'nullaryFalse', 'nullaryTrue', 'equalityFields', 'membershipFields', 'negationFields', 'binary0Fields', 'binary1Fields', 'binary2Fields', 'binary3Fields', 'forallFields', 'forallAtLift', 'existsFields', 'existsAtLift'),
        "ObjectTopEnvironment": ('variableImageExists', 'variableImageUnique', 'variableImageEdges', 'variableImageAtIndex', 'identityTableExists', 'shiftedTableExists', 'identityTableUnique', 'shiftedTableUnique', 'identityTableAt', 'shiftedTableAt', 'instantiateActualExists', 'instantiateActualInput', 'instantiateActualMaps', 'instantiateActualUnique', 'instantiateCodeExists', 'instantiateCodeInput', 'instantiateCodeLists', 'instantiateCodeNatural', 'instantiateCodeUnique', 'instantiateCodeUniqueOutput', 'instantiateCodeFiber', 'instantiateCodeExistsIff', 'instantiateCodeFiberIff', 'instantiateFormulaFiber', 'instantiateFormulaExists', 'instantiateActualZero', 'instantiateCodeZero', 'instantiateActualBound', 'instantiateCodeBound', 'instantiateActualFree', 'instantiateCodeFree', 'abstractActualExists', 'abstractActualInput', 'abstractActualMaps', 'abstractActualUnique', 'abstractCodeExists', 'abstractCodeInput', 'abstractCodeLists', 'abstractCodeNatural', 'abstractCodeUnique', 'abstractCodeUniqueOutput', 'abstractCodeFiber', 'abstractCodeExistsIff', 'abstractCodeFiberIff', 'abstractFormulaFiber', 'abstractFormulaExists', 'abstractActualZero', 'abstractCodeZero', 'abstractActualBound', 'abstractCodeBound', 'abstractActualFree', 'abstractCodeFree'),
        "ObjectTopFormula": ('instantiateAtCodes', 'instantiateEnvironment', 'instantiateSourceType', 'instantiateTargetType', 'instantiateSourceNatural', 'instantiateInput', 'instantiateTargetNatural', 'instantiateExists', 'instantiateUnique', 'instantiateUniqueOutput', 'instantiateFiber', 'instantiateExistsIff', 'instantiateFiberIff', 'instantiateRejectInput', 'instantiateNullary', 'instantiateNegation', 'instantiateBinary', 'instantiateEqual', 'instantiateMember', 'instantiateQuantified', 'abstractAtCodes', 'abstractEnvironment', 'abstractSourceType', 'abstractTargetType', 'abstractSourceNatural', 'abstractInput', 'abstractTargetNatural', 'abstractExists', 'abstractUnique', 'abstractUniqueOutput', 'abstractFiber', 'abstractExistsIff', 'abstractFiberIff', 'abstractRejectInput', 'abstractNullary', 'abstractNegation', 'abstractBinary', 'abstractEqual', 'abstractMember', 'abstractQuantified'),
        "ObjectOriginalQuotation": ('treeExists', 'treeRange', 'treeUnique', 'treeUniqueOutput', 'treeFiber', 'forestExists', 'forestRange', 'forestUnique', 'forestUniqueOutput', 'forestFiber', 'termExists', 'termRange', 'termUnique', 'termFiber', 'formulaExists', 'formulaRange', 'formulaUnique', 'formulaFiber'),
        "ObjectQuotationFields": ('fieldNatural', 'fieldAt', 'forestOfFields', 'forestToFields', 'forestIff', 'treeOfConstructor', 'treeToConstructor', 'treeIff', 'treeOfScalar', 'scalarOfTree', 'scalarIff', 'treeOfVariable', 'variableOfTree', 'variableIff', 'contextsOfLengths', 'termType', 'termTypedExists', 'termTypedUnique', 'termTypedUniqueOutput', 'termTypedFiber', 'formulaType', 'formulaTypedExists', 'formulaTypedUnique', 'formulaTypedUniqueOutput', 'formulaTypedFiber', 'nullaryType', 'equalType', 'memberType', 'negationType', 'binaryType', 'quantifiedType'),
        "ObjectTermImageQuotation": ('quotationAtValue', 'forestRead', 'forestLength', 'imageField', 'imageLength', 'imageRange', 'imageUnique', 'imageExists', 'imageTypedFields', 'imageTermList', 'environmentExists', 'environmentFiber', 'environmentUnique', 'environmentUniqueOutput', 'mixedAtIndex', 'mixedTerm', 'shiftAtIndex', 'shiftVariable', 'shiftTerm'),
        "ObjectTermLiftQuotation": ('readingsFromImages', 'readingsAt', 'agreeFromReadings', 'imagesFromReadings', 'zeroField', 'zeroAtNumeral', 'boundAtCode', 'boundValue', 'boundAtNumeral', 'boundReadings', 'freeAtCode', 'freeValue', 'freeReadings', 'environmentAtWitnesses', 'environmentAtMaps', 'environmentAtLifted', 'liftedFromEnvironment', 'liftedIffEnvironment', 'environmentFiber', 'jointFiber'),
        "ObjectNativeFormulaQuotation": ('environmentExists', 'environmentFiber', 'environmentAtLifted', 'termIff', 'nullaryStep', 'equalityStep', 'membershipStep', 'negationStep', 'binaryStep', 'quantifiedStep', 'formulaConstruct', 'formulaIff', 'formulaAtCandidate', 'formulaValueUnique', 'formulaUniqueOutput', 'formulaFiber'),
        "ObjectNativeTopQuotation": ('instantiateBoundField', 'instantiateBoundReadings', 'instantiateFreeField', 'instantiateFreeReadings', 'abstractBoundField', 'abstractBoundReadings', 'abstractFreeField', 'abstractFreeReadings', 'instantiateEnvironment', 'abstractEnvironment', 'instantiateAtCodes', 'instantiateIff', 'instantiateOriginalIff', 'instantiateAtCandidate', 'instantiateFiber', 'abstractAtCodes', 'abstractIff', 'abstractOriginalIff', 'abstractAtCandidate', 'abstractFiber'),
        "ObjectTermTransformProgram": ('variableRun', 'defaultRun', 'checkedIff', 'rejectEnvironment', 'rejectSource', 'targetType', 'outputNatural', 'rejectTarget', 'rejectOutputNatural', 'unique', 'uniqueOutput', 'atCandidate', 'actualFiber', 'fiberIffInput', 'encodedCheckedIff', 'uniformCorrectness', 'uniqueCode', 'atCode', 'existsCorrectProgram'),
        "ObjectFormulaTransformProgram": ('membershipInstructionIff', 'equalityInstructionIff', 'compiledStepIff', 'operatorRowIff', 'operatorValueIff', 'graphIff', 'evaluationIff', 'executionIff', 'actualRecursors', 'graphExists', 'evaluationExists', 'inputOfExecution', 'sourceType', 'targetType', 'outputNatural', 'uniqueOutput', 'atCandidate', 'rejectEnvironment', 'rejectSource', 'rejectInput', 'rejectTarget', 'rejectOutputNatural', 'unique', 'actualFiber', 'fiberIffInput', 'encodedExecutionIff', 'uniformCorrectness', 'uniqueCode', 'atCode', 'existsCorrectProgram'),
        "ObjectIndexFormulaRename": ('convertedExists', 'convertedFiber', 'convertedDomainIff', 'convertedUnique', 'environmentExists', 'environmentUnique', 'termProgramIff', 'membershipIff', 'equalityIff', 'binderEnvironment', 'allMetadataAtNatural', 'formulaForward', 'formulaReverse', 'formulaRenameIff', 'formulaProgramIff'),
        "ObjectFreeVariablePrograms": ('freeImageGraph', 'freeSameListCode', 'freeSameListCodeUnique', 'boundIdentityImageExists', 'freeForward', 'freeReverse', 'freeExecutionIff', 'freeInputOfExecution', 'freeSourceType', 'freeTargetType', 'freeOutputNatural', 'freeUniqueOutput', 'freeAtCandidate', 'freeUnique', 'freeActualFiber', 'freeFiberIffInput', 'freeRejectEnvironment', 'freeRejectSource', 'freeRejectInput', 'freeRejectTarget', 'freeRejectOutputNatural', 'weakForward', 'weakReverse', 'weakExecutionIff', 'weakInputOfExecution', 'weakSourceType', 'weakTargetType', 'weakOutputNatural', 'weakUniqueOutput', 'weakAtCandidate', 'weakUnique', 'weakActualFiber', 'weakFiberIffInput', 'weakRejectEnvironment', 'weakRejectSource', 'weakRejectInput', 'weakRejectTarget', 'weakRejectOutputNatural', 'weakActualSuccessorState'),
        "ObjectStrictLookup": ('binderFreeCodeStable', 'binderLiftedEnvironment', 'binderChildExecution', 'lookupZeroSelected', 'lookupConsSuccessor', 'lookupOuterRejected', 'lookupNilRejected', 'lookupConsZeroReturns', 'lookupEmptySink', 'lookupExactDomain', 'lookupCheckedDomain', 'lookupUnique', 'lookupUniqueOutput', 'lookupAtCandidate', 'lookupActualFiber', 'lookupFiberIffRange', 'lookupHasOutputIffRange', 'lookupRejectedIffNotRange', 'lookupOutOfBoundsRejected', 'lookupInRangeFieldIff', 'lookupFreeImageAtEdge'),
        "ObjectLookupTableProgram": ('operatorActualFiber', 'actualCarrierRecursors', 'allOrdinalRecursors', 'actualGraph', 'evaluationAtNatural', 'evaluationUniqueFiber', 'stateMembershipIff', 'recursiveCriterion', 'allInternalExecutionIff', 'naturalExecutionIff', 'encodedExecutionIff', 'uniformCorrectness', 'uniqueProgramCode', 'existsCorrectProgram', 'hasOutputIff', 'noOutputIff', 'outcomeExhaustive', 'outcomeIncompatible', 'uniqueOutput'),
        "ObjectOriginalLookupRules": ('expressionActualValue', 'expressionNaturalRange', 'expressionActualUniqueFiber', 'expressionUniqueValue', 'expressionCandidateIff', 'rawExpressionIff', 'consExpressionIff', 'premiseAtValue', 'guardAtValues', 'originalLookupHeadExpressionIff', 'originalLookupTailExpressionIff', 'originalLookupPremiseExpressionIff', 'originalLookupHeadMatrixIff', 'originalLookupTailMatrixIff', 'originalLookupChildMemberIff', 'originalLookupHeadAssignmentBound', 'originalLookupTailAssignmentBound'),
        "ObjectBoundedLookupDispatch": ('naturalAssignmentFromSearchBound', 'boundedRuleApplication', 'originalLookupHeadApplication', 'originalLookupTailApplication', 'searchBoundMembershipIff', 'originalBoundedMatrixIff', 'originalQuantifiedApplicationIff', 'wholeRuleTableBoundedSearchIff', 'wholeRuleTableActualSearchIff', 'originalOtherRulesRejected', 'originalWholeTableLookupDispatchIff', 'originalActualSearchLookupDispatchIff', 'originalLookupIntoWholeTable'),
        "ObjectLookupTrace": ('actualOriginalLookupRow', 'originalLookupRowNaturalFields', 'originalHeadApplicationSound', 'arbitraryClosedInternalTraceSound', 'canonicalTraceActualSet', 'canonicalTraceSubsetOmega', 'canonicalTraceSuccessfulMember', 'canonicalTraceClosed', 'compiledTraceComplete', 'compiledTraceExecutionIff', 'compiledTraceCandidateRejectionIff', 'originalBoundedSearchClosureIff', 'originalBoundedSearchTraceIff', 'originalBoundedSearchTraceExecutionIff', 'actualPowerTraceDomainIff', 'actualPowerTraceSearchIff', 'actualPowerTraceExecutionIff', 'allInternalTraceSomeExecutionIff', 'allInternalTraceSomeCheckedIff', 'naturalTraceSomeRawLookupIff', 'allInternalTraceHasOutputIff', 'allInternalTraceNoOutputIff', 'naturalTraceHasOutputStrictIff', 'naturalTraceNoOutputStrictIff', 'allInternalTraceOutputUnique'),
        "ObjectScalarTrace": ('ruleMatrixTraceMonotone', 'ruleApplicationTraceMonotone', 'originalWholeTableTraceMonotone', 'insertedTraceIncludes', 'insertedTraceSubsetOmega', 'insertedTraceClosed', 'insertedRootActualTrace', 'boundModeZeroTrace', 'boundModeZeroPowerTrace', 'boundModeThreeTrace', 'boundModeThreePowerTrace', 'freeModeZeroTrace', 'freeModeZeroPowerTrace', 'freeModeThreeTrace', 'freeModeThreePowerTrace'),
        "ObjectScalarDispatch": ('originalDifferentNodeTags', 'originalFiveFieldRecovery', 'originalModeWholeTableDispatchIff', 'originalVariableWholeTableDispatchIff', 'boundModeZeroDispatchIff', 'boundModeThreeDispatchIff', 'freeModeZeroDispatchIff', 'freeModeThreeDispatchIff', 'originalVariableActualSearchDispatchIff', 'originalVariableCandidateRejectionIff', 'arbitraryClosedVariableTraceApplication', 'originalVariableExprFromCode', 'originalBoundApplicationIdentity', 'originalBoundTraceIdentityIff', 'originalBoundPowerTraceIdentityIff', 'originalBoundTraceRejectionIff'),
        "ObjectFreeReplace": ('originalVariableExprCodeIff', 'originalVariableCodeNatural', 'originalFreeReplaceLookupPremiseSound', 'originalFreeReplaceMatrixSound', 'originalFreeReplaceApplicationSound', 'originalFreeReplaceTraceExecutionIff', 'originalFreeReplacePowerTraceExecutionIff', 'originalFreeReplaceTraceCandidateRejectionIff', 'actualOriginalFreeReplaceRoot', 'allInternalFreeReplaceReturnedIff', 'allInternalFreeReplaceCheckedIff', 'validFreeReplaceReturnedExecutionIff', 'naturalFreeReplaceReturnedStrictIff', 'allInternalFreeReplaceCandidateRejectionIff', 'allInternalFreeReplaceHasOutputGuardedIff', 'allInternalFreeReplaceNoOutputGuardedIff', 'validFreeReplaceHasOutputIff', 'validFreeReplaceNoOutputIff', 'naturalFreeReplaceStrictNoOutputIff', 'invalidFreeReplaceGuardNoOutput', 'nonNaturalFreeReplaceOutputRejected', 'allInternalFreeReplaceOutputUnique'),
        "ObjectFreeWeaken": ('actualSuccessorVariableValue', 'successorVariableValueExactDomain', 'successorVariableValueAtActualSuccessor', 'successorVariableValueNatural', 'successorVariableValueUnique', 'originalFreeWeakenMatrixSound', 'originalFreeWeakenApplicationSound', 'originalFreeWeakenTraceValueIff', 'originalFreeWeakenPowerTraceValueIff', 'originalFreeWeakenTraceCandidateRejectionIff', 'actualOriginalFreeWeakenRoot', 'allInternalFreeWeakenReturnedIff', 'validFreeWeakenReturnedValueIff', 'validFreeWeakenAtActualSuccessorIff', 'allInternalFreeWeakenCandidateRejectionIff', 'allInternalFreeWeakenHasOutputIff', 'allInternalFreeWeakenNoOutputIff', 'validFreeWeakenActualOutput', 'invalidFreeWeakenGuardNoOutput', 'nonNaturalFreeWeakenParameterNoOutput', 'nonNaturalFreeWeakenDepthNoOutput', 'invalidFreeWeakenInputNoOutput', 'allInternalFreeWeakenOutputNatural', 'nonNaturalFreeWeakenOutputRejected', 'allInternalFreeWeakenOutputUnique', 'allFourOriginalVariableTraceValueIff', 'allFourOriginalVariablePowerTraceValueIff', 'allFourOriginalVariableCandidateRejectionIff'),
        "ObjectOriginalTermProgram": ('replace_checked_iff', 'replace_coded_iff', 'weaken_checked_iff', 'weaken_coded_iff'),
        "ObjectOriginalArgumentsTrace": ('actualUniversalOriginalTrace', 'universalOriginalTraceMembershipIff', 'everyClosedOriginalTraceIncluded', 'universalOriginalTraceClosed', 'originalFullTraceOneStepIff', 'originalWholeTableRuleFromTraces', 'originalArgumentFullTableDispatchIff', 'originalArgumentTraceSelectedIff', 'originalNilArgumentsTrace', 'originalConsArgumentsTrace', 'originalConsArgumentActualChildTraces'),
        "ObjectOriginalArgumentMatrix": ('nilModeZeroThreeGuard', 'allCandidateEmptyExprNilIff', 'nilActualHeadNumericIff', 'consActualHeadNumericIff', 'headActualChildTraceNumericIff', 'tailActualChildTraceNumericIff', 'nilFullTracedMatrixNumericIff', 'consFullTracedMatrixNumericIff', 'consOriginalMatrixNumericIff', 'nilAllCandidateRowMatrixIff', 'consAllCandidateRowMatrixIff'),
        "ObjectOriginalArgumentRun": ('originalRunInputNatural', 'originalRunOutputNatural', 'actualOriginalArgumentRoot', 'originalArgumentOutcomesNatural', 'originalNilApplicationExactIff', 'originalConsApplicationExactIff', 'originalArgumentTraceCasesExactIff', 'originalArgumentWholeRunCasesExactIff'),
        "ObjectTypedArgumentList": ('numericTermModeRunIff', 'numericReplaceOnTypedTerm', 'numericWeakenOnTypedTerm', 'typedNilListIntroduction', 'typedConsListIntroduction', 'typedConsActualPredecessor', 'typedConsHead', 'typedConsTail', 'typedNilListIff', 'typedConsListIff', 'typedWholeListCasesIff'),
        "ObjectOriginalNumericTermFiber": ('replaceWholeTermAgreement', 'replaceActualOriginalTermFiber', 'replaceAllInternalTermPromise', 'weakenWholeTermAgreement', 'weakenActualOriginalTermFiber', 'weakenAllInternalTermPromise', 'originalTermValueTransfer', 'originalTermFiberTransfer', 'originalTermValueTargetType', 'originalTermAllCandidateUnique'),
        "ObjectOriginalArgumentFiber": ('originalRunInputSubstitution', 'originalRunOutputSubstitution', 'originalListValueTargetType', 'originalListAllCandidateUnique', 'originalNilListActualValue', 'originalConsListActualValue', 'originalAllInternalTypedListFiber', 'originalAllInternalListCodeProperties', 'replaceAllInternalOriginalListFiber', 'weakenAllInternalOriginalListFiber'),
        "ObjectOriginalArgumentFields": ('allCandidateOriginalListValue', 'originalAllInternalArgumentFields', 'originalAllInternalFieldCodeProperties', 'allInternalFieldImageOutputUnique', 'originalRunAllFieldImageIff', 'replaceAllInternalProgramFieldsIff', 'replaceWholeOriginalArgumentProgramIff', 'weakenAllInternalProgramFieldsIff', 'weakenWholeOriginalArgumentProgramIff', 'originalConsAllInternalFields'),
        "ObjectOriginalFormulaMatrix": ('originalKindThreeWholeTableDispatch', 'originalKindThreeTraceSelectedIff', 'originalFormulaHeadMetadata', 'originalFormulaApplicationNumericIff', 'originalFormulaConstantNumericMatrix', 'originalFormulaBinaryNumericMatrix', 'originalFormulaNonbinderNumericMatrix', 'originalFormulaBinderNumericMatrix', 'originalFormulaApplicationNumericMatrix', 'originalFormulaBinderActualChildRun', 'originalElevenRuleTraceComposition', 'originalFormulaConstantTraceFromData', 'originalFormulaBinaryTraceFromData', 'originalFormulaNonbinderTraceFromData', 'originalFormulaBinderTraceFromData', 'originalFormulaApplicationTraceFromData'),
        "ObjectOriginalFormulaEquation": ('originalFormulaConstantAssignmentEliminated', 'originalFormulaBinaryAssignmentEliminated', 'originalFormulaNonbinderAssignmentEliminated', 'originalFormulaBinderAssignmentEliminated', 'originalFormulaApplicationAssignmentEliminated', 'originalFormulaBinderAtActualSuccessor', 'originalFormulaElevenCasesAtTraceValue', 'originalFormulaElevenCasesAtRow', 'originalFormulaElevenCasesInputOutputNatural', 'originalFormulaWholeRunElevenCases'),
        "ObjectOriginalMemberApplication": ('originalAppHeadForestConstructorIff', 'originalAppHeadForestRecovered', 'originalMemberScalarAtZeroIndex', 'originalMemberAtTwoArgumentForestIff', 'originalMemberAppZeroAndTwoArgumentsRecovered', 'originalMemberAppAtNaturalArgumentsIff', 'originalMemberCheckedAppIff', 'originalMemberApplicationCaseIff'),
        "ObjectOriginalArgumentPair": ('finiteForestTypedListIff', 'finiteForestAllIndexProgramFieldsIff', 'finiteForestMappedProgramIff', 'replaceOriginalRunAtFiniteForestsIff', 'weakenOriginalRunAtFiniteForestsIff', 'twoArgumentListActualForestWitness', 'twoArgumentMappedAllCandidatesIff', 'replaceOriginalTwoArgumentAllCandidatesIff', 'weakenOriginalTwoArgumentAllCandidatesIff', 'twoArgumentForestRecoveredFromActualFields'),
        "ObjectOriginalMemberProgram": ('replaceMemberPairAllInternalAgreement', 'weakenMemberPairAllInternalAgreement', 'originalMemberWholeElevenCaseDispatchIff', 'originalMemberWholeRunApplicationIff', 'originalMembershipCaseProgramIff', 'originalMemberApplicationProgramIff', 'replaceOriginalMemberApplicationProgramIff', 'replaceOriginalMemberWholeRunProgramIff', 'weakenOriginalMemberApplicationProgramIff', 'weakenOriginalMemberWholeRunProgramIff'),
        "ObjectPureSyntaxBinary": ('formulaCorrectInstance', 'formulaStrictIHInstance', 'binaryInputExpressionIff', 'binaryKnownTypeIff', 'binaryActualApplicationSound', 'binaryActualChildTracesMerged', 'binaryQueryFromActualChildren', 'binaryQueryFromStrictInduction'),
        "ObjectPureSyntaxUnary": ('unaryInputExpressionIff', 'unaryKnownTypeIff', 'unaryActualApplicationSound', 'unaryActualChildTraceExtended', 'unaryQueryFromActualChild', 'unaryQueryFromInternalStep', 'unaryQueryFromStrictInduction'),
        "ObjectPureSyntaxFormulaChecker": ('formulaFromInductionIff', 'formulaAllInternalCorrect', 'formulaCorrectAtRoot', 'formulaInductionDischarged', 'formulaQueryIff', 'formulaQuerySound', 'formulaQueryComplete', 'fullSyntaxTypingIff'),
        "ObjectPureProofSubstitutionQueries": ('termExprQueryIff', 'argumentsExprQueryIff', 'formulaExprQueryIff', 'substitutionFormulaQueryIff', 'substitutionArgumentsQueryIff', 'substitutionTransformAtModeIff', 'substitutionGuardedTransformIff', 'substitutionBundleIff'),
        "ObjectRawCodeProjection": ('pairingComponentExists', 'pairingComponentUnique', 'barePairEveryNaturalDecodes', 'rawEveryPositiveNaturalDecodes', 'rawZeroComponent', 'rawUnselectedNaturalIsZero', 'rawHeadTailExists', 'rawHeadTailUnique', 'rawHeadTailRange', 'rawHeadTailZeroIff', 'arbitraryRawTagHeadTailIff', 'rawNaturalIterationFiber', 'rawGetExists', 'rawGetUnique', 'rawGetFiber', 'rawGetRange', 'rawGetZeroEquation', 'rawGetSuccessorEquation'),
        "ObjectRawCodeField": ('rawGetZeroAllInternalIndices', 'rawGetZeroInputIff', 'rawFieldExists', 'rawFieldUnique', 'rawFieldFiber', 'rawFieldRange', 'rawFieldAtActualPayloadIff', 'rawFieldAtArbitraryRawTagIff', 'rawFieldZeroInputIff', 'rawHeadTailOnActualConsIff', 'rawGetAtFiniteForestIff', 'rawFieldAtFiniteNodeIff', 'rawFieldAtFiniteConstructorIff'),
        "ObjectProjectionTrace": ('projectionTraceNatural', 'projectionTraceOriginalStep', 'projectionTraceSetExists', 'projectionTraceAllRootsUnfold', 'projectionTraceAtActualSetIff', 'projectionActualHeadBound', 'projectionActualRuleApplication', 'projectionActualRuleCondition', 'projectionTagZeroRule', 'projectionTagPositiveRule', 'projectionGetZeroRule', 'projectionGetHeadRule', 'projectionGetTailRule', 'projectionFieldZeroRule', 'projectionFieldPositiveRule'),
        "ObjectProjectionTag": ('projectionConstructorFieldNatural', 'projectionTagQueryNatural', 'projectionGetQueryNatural', 'projectionFieldQueryNatural', 'projectionTagRuleDispatch', 'projectionGetRuleDispatch', 'projectionFieldRuleDispatch', 'projectionTagZeroConstructed', 'projectionTagRawConstructed', 'projectionTagSound', 'projectionTagComplete', 'projectionTagQueryIff', 'projectionTagQueryUnique', 'projectionTagAtActualRowSound'),
        "ObjectProjectionGetField": ('projectionActualPremiseQueryIff', 'projectionActualPremisesQueriesIff', 'projectionGetVariablesQueryIff', 'projectionArbitraryRawPairHeadTail', 'projectionSuccessorVariableIff', 'projectionGetZeroConstructed', 'projectionGetHeadConstructed', 'projectionGetTailConstructed', 'projectionGetZeroIndexIff', 'projectionGetAllInternalCorrect', 'projectionGetAtInternalIndexIff', 'projectionGetAllCandidatesIff', 'projectionGetSound', 'projectionGetComplete', 'projectionGetUnique', 'projectionGetObjectSuccessorStep', 'projectionGetTailActualSubquery', 'projectionFieldZeroConstructed', 'projectionFieldRawConstructed', 'projectionFieldAllCandidatesIff', 'projectionFieldSound', 'projectionFieldComplete', 'projectionFieldUnique', 'originalSevenProjectionNumericIffs'),
        "ObjectProofSubstitutionNode": ('substitutionFreeProjectionIff', 'substitutionFormulaProjectionAtOneIff', 'substitutionFormulaProjectionIff', 'substitutionBothProjectionsIff', 'substitutionFreeProjectionAtConstructor', 'substitutionFormulaProjectionAtConstructor', 'substitutionProjectionsAtConstructor', 'substitutionAllFiveQueriesIff', 'pairingProjectionNumericBound', 'rawHeadTailNumericBound', 'rawGetAllInternalBounds', 'rawGetNumericBound', 'rawFieldNumericBound', 'substitutionAtOneBound', 'substitutionFormulaProjectionBound', 'substitutionAllAssignmentBounds', 'substitutionActualFiveFieldHeadIff', 'substitutionBoundedMatrixIff', 'substitutionFullPureRelationalNodeIff'),
        "ObjectProofMPNode": ('mpConclusionQueryIff', 'mpAntecedentQueryIff', 'mpLeftFreeProjectionIff', 'mpLeftFormulaProjectionIff', 'mpRightFreeProjectionIff', 'mpRightImplicationProjectionIff', 'mpImplicationGraphIff', 'mpRightImplicationAtConstructorIff', 'mpAllFourProjectionsIff', 'mpBothFormulaQueriesIff', 'mpAllSixQueriesIff', 'mpAntecedentProjectionBound', 'mpAllAssignmentBounds', 'mpActualFourFieldHeadIff', 'mpBoundedMatrixIff', 'mpFullPureRelationalNodeIff'),
        "ObjectProofStrengtheningNode": ('modeZeroFormulaAtCodesIff', 'modeZeroFullFormulaWeakenIff', 'modeZeroFullFormulaProgramIff', 'modeZeroFullFormulaOutputType', 'strengtheningFormulaQueryIff', 'strengtheningFreeProjectionAtSuccessorIff', 'strengtheningPredecessorFormulaIff', 'strengtheningActualModeZeroQueryIff', 'strengtheningGuardedModeZeroProgramIff', 'strengtheningAllFourQueriesAtSuccessorIff', 'strengtheningAllFourQueriesIff', 'strengtheningPredecessorFormulaBound', 'strengtheningAllAssignmentBounds', 'strengtheningActualThreeFieldHeadIff', 'strengtheningBoundedMatrixIff', 'strengtheningFullPureRelationalNodeIff'),
        "ObjectOriginalAbstract": ('modeOneFiveRuleStepIff', 'modeOneVariableTwoRuleStepIff', 'modeOneVariableWholeTraceIff', 'modeOneBoundIdentityGuardIff', 'modeOneBoundAbstractGuardIff', 'modeOneBoundPreservedTrace', 'modeOneBoundShiftedTrace', 'modeOneFreeHeadTrace', 'modeOneFreeTailTrace'),
        "ObjectAbstractVariable": ('originalVariableIndexGraph', 'modeOneBoundVariableNumericIff', 'modeOneBoundVariableNumericSound', 'modeOneBoundVariableNumericComplete', 'modeOneFreeVariableNumericIff', 'modeOneFreeVariableNumericSound', 'modeOneFreeVariableNumericComplete', 'modeOneAllVariableNumericTraceIff', 'modeOneAllVariableNumericRunIff', 'modeOneVariableNumericOutputNatural', 'modeOnePreservedValueConstructsTrace', 'modeOneShiftedValueConstructsTrace', 'modeOneFreeHeadValueConstructsTrace', 'modeOneFreeTailValueConstructsTrace'),
        "ObjectSmallModeArguments": ('smallModeOriginalNilGuard', 'smallModeOriginalNilMatrixIff', 'smallModeOriginalNilAtRowIff', 'smallModeOriginalNilApplicationIff', 'smallModeArgumentTraceAtActualValueIff', 'smallModeArgumentTraceIff', 'smallModeArgumentWholeRunIff', 'modeOnePureTermGuardedNumericIff', 'modeOnePureTermTypedNumericIff', 'modeOneTermScopeBranchNumeric', 'modeOneTermNumericBranchRun'),
        "ObjectAbstractAtomicFormula": ('smallModeFormulaConstantGuard', 'smallModeFormulaConstantMatrixIff', 'smallModeFormulaConstantApplicationIff', 'smallModeCompleteFormulaTraceIff', 'smallModeCompleteFormulaWholeRunIff', 'smallModeWholeFalseDispatchIff', 'smallModeWholeTrueDispatchIff', 'smallModeWholeEqualityDispatchIff', 'smallModeWholeMemberDispatchIff', 'modeOneFrameAtomicTermAgreement', 'modeOneFrameActualPairProgramIff', 'modeOneFrameActualPairAgreement', 'modeOneFrameWholeConstantIff', 'modeOneFrameWholeMembershipIff', 'modeOneFrameWholeEqualityIff', 'modeOneFrameAllAtomicWholeRunIff', 'modeOneFrameAllAtomicProgramIff'),
        "ObjectAbstractFormulaCorrectness": ('modeOneAllFormulaCorrect', 'modeOneFormulaCorrectAt', 'modeOneAllFramesIH', 'modeOneFullFormulaRunExecutionIff', 'modeOneActualHistoryAgreement', 'modeOneFullFormulaRunProgramIff', 'modeOneAgreedHistoryExists', 'modeOneActualTopFullFormulaExecutionIff', 'modeOneActualTopFullFormulaProgramIff'),
        "ObjectForallNode": ('modeOneActualTopFormulaAtCodesIff', 'modeOneActualTopFormulaIff', 'modeOneActualTopGuardedFormulaIff', 'modeOneActualTopFormulaSource', 'forallFormulaQueryIff', 'forallFreeProjectionQueryIff', 'forallPredecessorFormulaQueryIff', 'forallModeOneTransformNumericIff', 'forallActualTopTransformIff', 'forallAllFourQueriesIff', 'forallAllFourAssignmentBounds', 'forallActualNestedHeadIff', 'forallFullPureRelationalNodeIff', 'forallFullNormalizedNodeIff'),
        "ObjectInstantiateVariable": ('modeTwoWholeVariableValueIff', 'modeTwoVariableTraceValueIff', 'modeTwoBoundCandidateIff', 'modeTwoFreeCandidateIff', 'modeTwoOriginalVariableTraceStepIff', 'modeTwoFiveRuleTermDispatchIff', 'modeTwoBoundPreservedPositiveTrace', 'modeTwoBoundPointPositiveTrace', 'modeTwoBoundPredecessorPositiveTrace', 'modeTwoFreeIdentityPositiveTrace', 'modeTwoClosedParameterFreeBranch', 'modeTwoFrameTermProgramIff', 'modeTwoFrameTermCodedIff', 'modeTwoFrameGuardedTermCodedIff'),
        "ObjectAbstractFramePrograms": ('arbitraryDepthFrameVariableProgramIff', 'arbitraryDepthFrameTermProgramIff', 'arbitraryDepthFrameTermCodedIff', 'arbitraryDepthFrameTermGuardedCodedIff', 'arbitraryDepthFrameTermAllOutputsAgreement', 'arbitraryDepthFrameTypedTermUniqueFiber', 'arbitraryDepthFrameTermPromiseDischarged', 'arbitraryDepthFrameArgumentFieldsIff', 'arbitraryDepthFrameArgumentProgramIff', 'arbitraryDepthFrameGuardedArgumentProgramIff'),
        "ObjectAbstractOperationFrame": ('arbitraryDepthBoundShiftedIff', 'internalSuccessorThresholdIff', 'knownActualIndexVariableRenameIff', 'actualBinderBoundRenameIff', 'actualBinderFreeRenameIff', 'arbitraryDepthBoundBinderCovarianceIff', 'arbitraryDepthFreeBinderCovarianceIff', 'actualAbstractRootCompatibleFrame', 'actualLiftedBoundFieldsIff', 'actualLiftedFreeFieldsIff', 'allInternalLiftedBoundFieldsIff', 'allInternalLiftedFrameCompatibility', 'actualBinderCompatibleFrameWitnessesDischarged'),
        "ObjectAbstractTopArguments": ('smallModeArgumentActualFiber', 'smallModeArgumentActualFields', 'smallModeArgumentCompleteFieldMapIff', 'modeOneActualTermAllOutputsAgreement', 'modeOneActualTermUniqueTypedFiber', 'modeOneActualTermPromiseDischarged', 'modeOneZeroDepthActualArgumentFieldsIff', 'modeOneZeroDepthActualArgumentProgramIff', 'modeOneZeroDepthArgumentsAtActualCodesIff', 'modeOneZeroDepthArgumentsActualOperationIff', 'modeOneZeroDepthGuardedArgumentsActualOperationIff'),
        "ObjectAbstractTopTerm": ('modeOneBoundAtZeroDepthIff', 'modeOneFreeAtZeroIndexIff', 'modeOneFreeAtSuccessorIndexIff', 'modeOneBoundBelowDepthIff', 'modeOneActualBoundTableAtSuccessorIff', 'modeOneActualFreeTableAtZeroIff', 'modeOneActualFreeTableAtSuccessorIff', 'modeOneZeroDepthActualVariableTableIff', 'modeOneZeroDepthActualVariableProgramIff', 'modeOneZeroDepthActualPureTermProgramIff', 'modeOneZeroDepthActualCodedPureTermIff', 'modeOneZeroDepthPureTermAtActualCodesIff', 'modeOneZeroDepthPureTermActualOperationIff', 'actualAbstractPureTermSourceType', 'modeOneZeroDepthGuardedPureTermActualOperationIff'),
        "ObjectPureSyntaxMembership": ('membershipInputDataIff', 'membershipAtForestIff', 'membershipTypedListSound', 'membershipActualPremiseAtTwo', 'membershipApplicationSound', 'membershipQueryFromList', 'membershipQueryAt', 'typedMembershipQuery', 'fullMembershipQuery', 'allFourAtomicQueries'),
        "ObjectPureSyntaxFormulaAtoms": ('constantInputExpressionIff', 'constantApplicationIffNullary', 'constantApplicationSound', 'constantQueryConstructed', 'typedConstantQueryConstructed', 'equalityInputExpressionIff', 'equalityApplicationSound', 'equalityQueryConstructed', 'typedEqualityQueryConstructed', 'equalityActualChildTracesMerged'),
        "ObjectPureSyntaxArgumentChecker": ('pureConsQueryComplete', 'pureConsApplicationFromInductionSound', 'pureArgumentsFromInductionIff', 'pureAllArgumentsCorrect', 'pureArgumentsInductionDischarged', 'pureArgumentsQueryIff', 'pureArgumentsQuerySound', 'pureArgumentsQueryComplete', 'pureEmptyBoundArgumentsQueryIff', 'pureModeThreeFromArgumentsQueryIff'),
        "ObjectPureSyntaxListSteps": ('binaryUnionExists', 'pureTraceInsertionCondition', 'pureTracePairCondition', 'pureNilExpressionIff', 'pureNilApplicationSound', 'pureNilApplicationComplete', 'pureNilChecked', 'pureTypedNilChecked', 'pureConsApplicationComplete', 'pureConsConditionComplete'),
        "ObjectPureSyntaxTermChecker": ('purePremiseFreeTraceExists', 'pureVariableExpressionIff', 'pureVariableApplicationSound', 'pureTermClosedTraceSound', 'pureTermCheckSound', 'pureTermCheckComplete', 'pureTermCheckIff', 'pureEmptyBoundTermCheckFree'),
        "ObjectOriginalFreeSubstFormula": ('emptyBoundTermFree', 'emptyBoundListsIff', 'emptyBoundConversionExists', 'modeThreeWholeSubstitutionIff', 'modeThreeWholeProgramIff', 'modeThreeEmptyBoundArgumentsIff', 'modeThreeOutputType', 'modeThreeOutputUnique', 'modeThreeActualOutput'),
        "ObjectOriginalFormulaCorrectness": ('fullElevenProgramFromUniformIff', 'wholeRunExecutedFromUniformIff', 'allParametersCorrectFromUniform', 'allInternalRootsCorrect', 'uniformInductionDischarged', 'allInternalWholeRunExecutedIff', 'allInternalWholeProgramIff', 'actualHistoryAgreementDischarged', 'agreedActualHistoryExistsDischarged'),
        "ObjectFormulaTransformRootStep": ('recursiveCasesTargetType', 'actualProgramTargetType', 'actualRootGuardedStepIff', 'actualRootStepIff', 'actualRootWholeProgramIff'),
        "ObjectOriginalBinderProgram": ('naturalSuccessorWitness', 'liftedChildExecutionAlignmentIff', 'quantifierChildReadAtLiftIff', 'quantifierStepAdvancedIff', 'quantifierLocalCaseIff', 'quantifierWholeRunDispatchIff', 'quantifierWholeRunFromUniformInductionIff'),
        "ObjectUniformOperationFrames": ('freeConversionFromActualConverted', 'frameEnvironment', 'weakenFrameFromExistingEnvironment', 'replaceFrameFromFreeConversion', 'frameAtomicWholeProgramIff', 'binderEnvironmentAt', 'binderEnvironmentExists', 'uniformCorrectAt', 'uniformPrefixAt', 'uniformPrefixAtFrame', 'actualHistoryAgreementAtUniformFrame', 'actualHistoryExistsAtUniformFrame', 'binderPrefixFromUniformInduction'),
        "ObjectActualFormulaHistory": ('actualHistoryReadExecutedIff', 'prefixInductionAt', 'actualHistoryAgreementFromInduction', 'agreedActualHistoryExists', 'negationActualHistoryFromInductionIff', 'binaryActualHistoryFromInductionIff'),
        "ObjectOriginalLogicalProgram": ('logicalHistoryAgreementAt', 'negationChildFormulaCode', 'binaryChildrenFormulaCode', 'negationLocalHistoryIff', 'negationWholeRunDispatchIff', 'negationWholeRunHistoryConditionalIff', 'binaryLocalHistoryIff', 'binaryWholeRunDispatchIff', 'binaryWholeRunHistoryConditionalIff'),
        "ObjectUnifiedAtomicProgram": ('compiledAtomicProgramSource', 'replaceTypedMembershipWholeRunIff', 'replaceTypedEqualityWholeRunIff', 'replaceUnifiedAtomicProgramIff', 'weakenTypedMembershipWholeRunIff', 'weakenTypedEqualityWholeRunIff', 'weakenUnifiedAtomicProgramIff'),
        "ObjectWholeAtomicInterfaces": ('rawApplicationWrongTagRejected', 'applicationCaseWrongTagRejected', 'wholeFalseDispatchIff', 'wholeTrueDispatchIff', 'wholeEqualityDispatchIff', 'replaceWholeEqualityExistingAtomIff', 'weakenWholeEqualityExistingAtomIff', 'wholeConstantExistingAtomIff'),
        "ObjectExistingAtomicInterfaces": ('memberResultExistingAtomIff', 'replaceWholeMemberExistingAtomIff', 'weakenWholeMemberExistingAtomIff', 'replaceAllInternalCheckedTermAgreement', 'weakenAllInternalCheckedTermAgreement', 'equalityLocalCaseExistingAtomIff', 'replaceEqualityLocalExistingAtomIff', 'weakenEqualityLocalExistingAtomIff', 'constantDataExistingAtomIff'),
    }
    standard_core = {"propext", "Classical.choice", "Quot.sound"}
    for namespace, names in arithmetic_groups.items():
        for name in names:
            core = f"PPAC.Migration.Internal.{namespace}.{name}_kernel_certificate"
            native = f"PPAC.Migration.Internal.{namespace}.native_{name}"
            if set(footprints.get(core, [])) != standard_core:
                raise RuntimeError(f"Unexpected arithmetic core certificate footprint: {core}")
            if set(footprints.get(native, [])) != standard_core | inherited:
                raise RuntimeError(f"Unexpected arithmetic native certificate footprint: {native}")
    hashed = sources + sorted(ROOT.glob("third_party/openai/*.txt")) + [ROOT / x for x in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "scripts/verify.py", "scripts/source_hash.py", "scripts/check_ci_inputs.py", "scripts/test_ci_compatibility.py", "scripts/original_comparator.py", "scripts/test_original_comparator_guard.py", ".github/workflows/lean.yml", "docs/ORIGINAL_COMPARATOR_LOCK.json", "scripts/check_source_rules.py", "scripts/check_source_theory.py", "docs/SOURCE_THEORY_LOCK.json", "docs/SOURCE_RULES_LOCK.json", "docs/SOURCE_LOCK.json", "docs/L_REUSE_LOCK.json", "docs/TRUST_BASELINE.json", "docs/CHOICE_TRUST_BASELINE.json", "docs/MODE3_CHECKER_SCOPE.json"]]
    summary = {
        "source_hash_policy": POLICY,
        "lean_version": version,
        "source_forcing_Child_formula_indexed_induction_proved": True,
        "source_forcing_Child_external_wellFounded_claimed": False,
        "source_forcing_IsName_set_condition_unfolding_proved": True,
        "source_forcing_IsName_formula_indexed_uniqueness_proved": True,
        "source_forcing_evaluate_internal_set_G_total_unique_unfolding_proved": True,
        "source_forcing_evaluate_external_generic_filter_identification_proved": False,
        "source_forcing_mapConditions_definable_total_unique_unfolding_edge_empty_proved": True,
        "source_forcing_mapConditions_object_function_antecedent_retained": True,
        "source_forcing_mapConditions_concrete_actCode_instance_proved": True,
        "source_forcing_actCode_instance_scope": "Internal permutation graph on P, identity outside P; final PPAC group/homomorphism family not instantiated",
        "source_forcing_condition_graph_identity_inverse_composition_proved": True,
        "source_forcing_Name_act_graph_preservation_identity_composition_inverse_proved": True,
        "source_forcing_Name_evaluate_smul_formula_class_proved": True,
        "source_forcing_pairName_existence_unique_edge_name_proved": True,
        "source_forcing_pairName_formula_class_evaluation_and_map_proved": True,
        "source_forcing_Name_smul_pair_fixed_condition_proved": True,
        "source_forcing_unionName_exact_range_edge_name_proved": True,
        "source_forcing_unionName_formula_class_filter_evaluation_proved": True,
        "source_forcing_unionName_condition_action_proved": True,
        "source_forcing_checkName_proved": True,
        "source_forcing_checkName_scope": "All internal sets: existence, uniqueness, exact membership/edge equations, IsName, formula-class evaluation, definable condition-map covariance and fixed-condition action. External generic-filter identification is not claimed. HS closure is proved separately in ForcingHSCheck under the original fixed-action and top-filter premises.",
        "source_forcing_checkName_external_wellFounded_required": False,
        "source_forcing_checkName_HS_closure_proved": True,
        "source_forcing_checkName_HS_scope": "All internal x; explicit source top-filter, t in P and action-family fixing t; Uniform product family and its actual same-L concrete poset/top/filter parents are now constructed; the generic check-name closure proof is retained.",
        "source_forcing_literal_stabilizer_constructed": True,
        "source_forcing_HS_definition_unfolding_and_definable_uniqueness_proved": True,
        "source_forcing_empty_HS_proved": True,
        "source_forcing_HS_action_closure_native_schema_proved": True,
        "source_forcing_HS_action_closure_concrete_PPAC_instance_proved": False,
        "source_forcing_HS_pair_union_closure_proved": True,
        "source_actual_HS_forces_pairing_union_native_certificate_proved": True,
        "source_actual_HS_forces_extensionality_emptySet_native_certificate_proved": True,
        "source_literal_union_guarded_codeOrder_equivalence_proved": True,
        "source_actual_HS_forces_foundation_native_certificate_proved": True,
        "source_minimal_member_uses_internal_formula_child_induction": True,
        "source_actual_HS_forces_infinity_native_certificate_proved": True,
        "source_forced_infinity_uses_literal_check_of_internal_omega": True,
        "source_equivariantMix_exact_raw_name_native_kernel_constructed": True,
        "source_equivariantMix_regular_membership_native_kernel_proved": True,
        "source_equivariantMix_coherent_family_equality_at_activation_native_kernel_proved": True,
        "source_equivariantMix_actual_Product_fixed_HS_native_kernel_proved": True,
        "source_equivariantMix_additional_internal_Choice_or_rank_bound": False,
        "source_OrbitNames_literal_name_eq_of_same_diagram_native_kernel_proved": True,
        "source_ProductForcing_actual_compatible_placement_same_L_native_kernel_proved": True,
        "source_ChoiceFailure_forces_at_supporting_root_proved": True,
        "source_ChoiceFailure_forces_iff_restrict_same_L_native_kernel_proved": True,
        "source_LocalQuotients_active_equal_independent_same_L_native_kernel_proved": True,
        "source_LocalQuotients_active_equal_arbitrary_overlap_same_L_native_kernel_proved": True,
        "source_ProductNames_actual_Bit_and_five_laws_native_kernel_proved": True,
        "source_ProductNames_actual_label_and_labelSet_constructed": True,
        "source_LocalQuotients_actual_label_bound_and_normalized_subset_native_kernel_proved": True,
        "source_LocalQuotients_LocalName_carrier_and_literal_restriction_native_kernel_proved": True,
        "source_LocalQuotients_localNormalize_and_localName_descent_proved": True,
        "source_ProductNames_actual_label_HS_and_covariance_and_labelSet_full_group_fixation_native_kernel_proved": True,
        "source_LocalQuotients_actual_root_orbit_families_constructed": True,
        "source_LocalQuotients_support_descent_same_L_native_kernel_proved": True,
        "source_LocalQuotients_actual_active_equal_and_support_descent_proved": True,
        "source_LocalQuotients_actual_quotients_and_restrictions_constructed": True,
        "source_LocalQuotients_quotient_restriction_identity_and_composition_native_kernel_proved": True,
        "source_LocalQuotients_quotient_restriction_injective_and_intersection_proved": True,
        "source_AvailableRecords_eligibility_and_root_reflection_native_kernel_proved": True,
        "source_AvailableRecords_actual_eligibleSystem_object_carrier_constructed": True,
        "source_AvailableRecords_actual_Obj_restriction_constructed": True,
        "source_AvailableRecords_Obj_map_identity_composition_injectivity_transfer_proved": True,
        "source_AvailableRecords_actual_Obj_intersection_native_kernel_proved": True,
        "source_AvailableRecords_Obj_map_quotient_law_premises_discharged": True,
        "source_AvailableRecords_all_internal_diagram_object_and_map_families_constructed": True,
        "source_AvailableRecords_same_family_source_target_compatibility_proved": True,
        "source_AvailableRecords_actual_eligibleSystem_full_assembly_completed": True,
        "source_LocalRecords_actual_availability_ideals_native_kernel_proved": True,
        "source_AvailableRecords_same_eligibleSystem_all_classAvailability_ideals_constructed": True,
        "source_AvailableRecords_actual_availability_contraction_and_fiber_bijections_proved": True,
        "source_ComponentGluing_all_internal_vertex_fibers_and_actual_arrow_coherence_native_kernel_proved": True,
        "source_ComponentGluing_actual_Point_Matches_equivalence_and_same_fiber_laws_native_kernel_proved": True,
        "source_ComponentGluing_entire_component_quotient_and_all_toGlued_bijections_commuting_native_kernel_proved": True,
        "source_LocalRecords_literal_labelSystem_and_centers_native_kernel_proved": True,
        "source_ConcreteSystem_exact_label_fiber_and_glued_cardinalities_native_kernel_proved": True,
        "source_ConcreteSystem_label_cardinality_scope": "Same actual label System, exact fiber and entire glued component. Original IdealProbes, Small D mu and K equinumerous mu premises retained; existing final-T producers have not yet been jointly instantiated here. labelFiberSet_common, moving-filter transport and final internal Con are not asserted.",
        "source_ConcreteSystem_same_actual_T_label_fiber_glued_cardinality_instance_proved": True,
        "source_ConcreteSystem_labelFiberSet_common_literal_set_equality_proved": True,
        "source_ConcreteSystem_same_actual_T_labels_scope": "ConstructionConcreteBase actual tower and final Target are jointly constructed in the existing internal L; the SAME Row/ObjectFields/AllIdeals/Cardinals discharge the probe and cardinal hypotheses. Every internal coordinate set has a literal label System with all exact fiber/glued cardinalities and Common fiber set equality. Moving-filter transport, CodeLinks and final internal Con remain unproved.",
        "source_QuotientTransport_ReindexIso_exact_availability_and_fiber_transport_native_kernel_proved": True,
        "source_QuotientActions_actual_labelTransport_app_family_native_kernel_constructed": True,
        "source_QuotientTransport_reindex_scope": "Distinct source/target actual Systems; source naturality square and actual per-diagram app bijections imply complete availability and exact-fiber transport by literal restrictions. Label instance constructs the entire unique app family from the coordinate permutation. Whole-component glued transport is supplied by ForcingGluedTransport; moving-filter eligibleSystem instantiation and final internal Con remain unproved.",
        "source_ConcreteSystem_Vertex_permute_Arrow_move_Common_move_native_kernel_proved": True,
        "source_QuotientTransport_whole_component_gluedEquiv_toGlued_native_kernel_proved": True,
        "source_QuotientTransport_glued_scope": "Distinct source/target Systems; actual whole component quotients and projection graphs constructed with existing backend. Root-fiber composite is a set bijection agreeing with literal restricted app at every Common vertex. Original ReindexIso, conditional joins and root-fixing premises retained. Moving-filter eligibleSystem, full root-group action laws, CodeLinks, and final internal Con not asserted.",
        "source_QuotientTransport_actual_moved_filter_and_local_eq_transport_iff_native_kernel_proved": True,
        "source_QuotientTransport_local_transport_scope": "Constructs the actual Product action and moved Cohen filter from existing Presentation and coordinate permutation. Local equality is preserved and reflected for all internal mapped names with both filter and diagram moved. Uses existing moved_code and atomic symmetry, not fixed-filter equality. Actual LocalName, quotient and per-diagram eligible app transport are supplied by the following adapters; complete eligibleSystemTransport family assembly remains unassembled.",
        "source_QuotientTransport_LocalName_transportEquiv_native_kernel_proved": True,
        "source_QuotientTransport_LocalQuotient_transportEquiv_native_kernel_proved": True,
        "source_QuotientTransport_literal_restriction_square_native_kernel_proved": True,
        "source_QuotientTransport_actual_name_quotient_scope": "Actual LocalName action bijection using existing HS, bound and support conjugacy; literal labelSet discharges bound stability. Actual moved-filter quotient construction consumes that bijection and local EqG preservation/reflection, returning both class carriers, projections and the descended bijection. Native restriction square is proved for exact graphs. Actual eligibility and per-diagram app transport are supplied by ForcingEligibleTransport; complete eligibleSystemTransport family assembly and final internal Con remain unproved.",
        "source_QuotientTransport_eligibleName_coordinate_transport_native_kernel_proved": True,
        "source_QuotientTransport_actual_eligible_root_object_bijection_native_kernel_proved": True,
        "source_QuotientTransport_actual_eligible_app_from_existing_rows_native_kernel_proved": True,
        "source_QuotientTransport_full_eligibleSystemTransport_family_assembled": True,
        "source_QuotientTransport_eligible_transport_scope": "Actual coordinate eligibility consumes existing full HS formula symmetry and simultaneously moves filter, diagram and E. Actual root Obj bijection consumes literal labelSet fixedness, root support and fixed E. Assembly constructs LocalName/quotient/eligible app from the two actual EligibleFamily.Data rows; no app or quotient bijection is assumed. All-app function family and full naturality are now assembled by ForcingEligibleReindex against the existing actual object/restriction families; CodeLinks, model applications and final internal Con remain unproved.",
        "source_TailGraphs_actual_internal_omega_ChainCode_carrier_constructed": True,
        "source_TailGraphs_actual_At_Represents_unique_proved": True,
        "source_TailGraphs_every_glued_value_has_literal_representing_code_same_L_native_kernel_proved": True,
        "source_TailGraphs_same_code_covariance_and_leastCode_completed": False,
        "source_TailGraphs_actual_At_transport_iff_proved": True,
        "source_TailGraphs_internal_tail_fixed_and_same_code_covariance_proved": True,
        "source_TailGraphs_leastCode_completed": False,
        "source_TailGraphs_code_scope": "Exact existing candidate names, chain, object family and gluing laws are consumed. All internal omega entries are actual local normalized names. Existing internal uniformization supplies representative sequences inside the same L; no ambient Choice or host sequence is substituted. Actual At transport and same-code covariance are now proved in nativeZF using the same internal chain and code. leastCode, persistent selection, ordinal rank, CodeLinks and final Con remain unproved.",
        "source_collectRaw_exact_internal_graph_range_constructed": True,
        "source_component_rebase_same_set_quotient_proved": True,
        "source_component_transport_target_original_root_constructed": True,
        "source_collect_HS_original_subgroup_entry_contract_native_certificate_proved": True,
        "source_collect_HS_indexed_permutation_contract_equivalence_proved": True,
        "source_tuple_stabilizer_native_schema_proved": True,
        "source_separation_common_support_from_actual_name_stabilizers_proved": True,
        "source_collect_HS_concrete_separation_instance_proved": True,
        "source_separate_literal_edge_and_mem_iff_proved": True,
        "source_actual_HS_full_forced_Separation_native_schema_proved": True,
        "source_subsetBound_normalize_and_literal_power_name_proved": True,
        "source_power_exact_edge_and_all_HS_mem_iff_proved": True,
        "source_actual_HS_forces_powerSet_native_certificate_proved": True,
        "source_chosenWitness_consumer_discharged_by_native_Collection": True,
        "source_internal_choice_function_constructed_or_assumed": False,
        "source_replacementBound_whole_group_orbit_and_local_witness_proved": True,
        "source_replacementImage_exact_membership_under_single_valuedness_proved": True,
        "source_actual_HS_full_forced_Replacement_native_schema_proved": True,
        "source_actual_HS_all_forced_ZF_schemas_proved": True,
        "source_actual_HS_all_forced_ZF_scope": "Every external source axiom/schema has a native object derivation under original source monoid/Presentation/carrier/Normal/condition premises; concrete stage-8 algebra and arbitrary internal syntax/proof-code reduction are not discharged.",
        "source_product_actual_name_stabilizers_subgroup_proved": True,
        "source_product_HS_pair_union_object_kernel_certificates_proved": True,
        "source_product_HS_union_assumes_order_invariance_on_nonconditions": False,
        "source_atomic_left_right_swap_induction_native_certificate_proved": True,
        "source_atomic_relations_recursion_constructed": True,
        "source_atomic_relations_scope": "All internal raw names, internal condition set P, formula-defined relation R; native existence, uniqueness, exact membership/equality equations. External condition presentation identification remains pending.",
        "source_atomic_relations_exact_recursive_equations_proved": True,
        "source_atomic_condition_presentation_identified": False,
        "source_atomic_forcing_laws_proved": True,
        "source_atomic_forcing_laws_scope": "Internal condition codes P and formula-defined preorder R; monotonicity, symmetry, dense closure, edge introduction, reflexivity, equality transitivity and both membership congruences. No external condition-presentation identification or atomic truth claimed.",
        "source_atomic_four_query_triple_induction_proved": True,
        "source_forcing_fixed_formula_native_monotonicity_and_dense_closure_proved": True,
        "source_forcing_sound_all_19_rules_fixed_proof_native_schema_proved": True,
        "source_forcing_sound_arbitrary_internal_code_reduction_proved": False,
        "source_forcing_formula_HS_domain_native_schema_instantiated": True,
        "source_forcing_formula_HS_domain_concrete_PPAC_system_instantiated": True,
        "source_forcing_formula_action_symmetry_native_schema_proved": True,
        "source_forcing_formula_action_symmetry_HS_native_schema_proved": True,
        "source_forcing_formula_action_symmetry_concrete_PPAC_instance_proved": False,
        "source_forcing_formula_action_symmetry_scope": "Every fixed formula; constructed atomic symmetry and existing actCode. ProductSymmetry now constructs the reverse conjugation and discharges both contexts and order transport for the fixed-carrier product action and support-defined filter. Its source omega/two carrier instance is constructed. The actual same-L concrete system and all static parents are now constructed by ForcingConcreteSystem. The standalone concrete full-schema export flag is not claimed by this existence-and-quotient batch; its generic forcing/symmetry proof is retained.",
        "source_atomic_action_symmetry_native_certificates_proved": True,
        "source_atomic_action_symmetry_scope": "All internal raw names; definable injective map/order-isomorphism on P, with actual actCode permutation instance. ProductSymmetry now instantiates the uniform product family and HS domain; the actual same-L concrete monoid/poset and group/filter parents now exist; the original fixed-formula atomic symmetry proof remains the reusable backend.",
        "source_atomic_decision_truth_branch_required_for_selected_route": False,
        "source_atomic_decision_set_density_proved": False,
        "source_atomic_truth_proved": False,
        "source_forcing_label_permutation_carrier_and_fixing_sets_proved": True,
        "source_forcing_label_fixing_identity_inverse_composition_closure_proved": True,
        "source_forcing_label_fixing_conjugacy_pointwise_native_certificate_proved": True,
        "source_forcing_label_group_conjugation_set_graph_constructed": True,
        "source_forcing_label_fixing_conjugation_exact_set_image_proved": True,
        "source_forcing_label_subgroup_conjugation_closure_proved": True,
        "source_forcing_small_support_family_constructed": True,
        "source_forcing_small_support_empty_subset_image_bounds_proved": True,
        "source_forcing_small_support_top_upward_conjugation_proved": True,
        "source_forcing_small_support_union_bound_proved": True,
        "source_forcing_small_support_intersection_closure_proved": True,
        "source_forcing_small_support_normal_filter_constructed": True,
        "source_forcing_small_support_properness_proved": False,
        "source_forcing_small_support_omega_cardinality_assumed": False,
        "additional_pinned_cardinal_native_Bool_certificates_reevaluated": 9,
        "source_forcing_label_group_scope": "Every internal label set I; actual permutation carrier, fixing subsets and operation witnesses; conjugation is an internally constructed permutation graph with exact fixing-subgroup images and subgroup closure. Actual small-support family and top/upward/conjugation clauses are constructed. The donor finite-union bound, intersection closure and full four-clause normal-filter construction are now proved under internal IsOmega/IsInfiniteCardinal, with omega cardinality derived. Uniform ProductNames condition action and HS context are constructed; source omega/two fixed carriers are constructed; monoid/conical order, properness and forcing axioms remain.",
        "source_forcing_final_group_homomorphism_family_instantiated": False,
        "source_diagram_full_injection_label_action_native_certificates_proved": True,
        "source_diagram_order_and_Cohen_product_action_proved": True,
        "source_cohen_coordinate_permutation_graphs_constructed": True,
        "source_cohen_bounded_partial_function_carrier_constructed": True,
        "source_cohen_image_preserves_functionality_and_internal_bound": True,
        "source_cohen_condition_carrier_order_permutation_constructed": True,
        "source_cohen_label_action_group_laws_instantiated": True,
        "source_cohen_omega_two_and_product_WithTop_system_assembled": True,
        "source_product_condition_carrier_and_action_from_label_permutation_constructed": True,
        "source_product_condition_identity_and_multiplication_proved": True,
        "source_product_condition_partial_order_algebra_instantiated": True,
        "source_product_partial_order_from_source_monoid_contract_proved": True,
        "source_product_actual_relation_PreorderOn_antisymmetry_top_native_certificate_proved": True,
        "source_product_stage8_monoid_construction_proved": True,
        "source_ConcreteSystem_closed_exists_native_kernel_and_uniform_quotient_consequence_proved": True,
        "original_stage8_global_parent_inputs_discharged": True,
        "source_UniformImages_actual_kernel_graph_HS_support_and_application_native_kernel_proved": True,
        "source_UniformImages_kernel_value_and_same_value_class_construction_native_kernel_proved": True,
        "source_UniformImages_kernel_value_and_image_class_laws_complete": True,
        "source_UniformImages_imageQuotient_graph_functions_complete": True,
        "source_RelationCalculus_composition_and_inverse_graphs_complete": True,
        "source_UniformImages_nonwellorderable_image_bijection_complete": True,
        "source_ChoiceFailure_same_system_forces_not_AC_complete": True,
        "source_OrdinalChoice_same_system_rootProbes_complete": True,
        "source_OrdinalChoice_exact_dense_ACwo_logical_bridge_complete": True,
        "source_DiagramPlacements_witness_placement_object_schema_complete": True,
        "source_DiagramPlacements_localized_existential_complete": True,
        "source_OrdinalChoice_Cohen_maximal_antichain_complete": True,
        "source_OrdinalChoice_localized_maximum_complete": True,
        "source_GraphFusion_indexedGraph_complete": True,
        "source_OrdinalChoice_ground_family_choice_complete": True,
        "source_OrdinalChoice_ground_family_choice_dense_complete": True,
        "source_OrdinalChoice_actual_dense_choice_and_forces_ACwo_complete": True,
        "source_OrdinalPresentation_default_relation_complete": True,
        "source_OrdinalPresentation_completion_graph_surjection_complete": True,
        "source_OrbitNames_actual_partial_orbit_graph_complete": True,
        "source_OrdinalPresentation_actual_index_and_partial_family_complete": True,
        "source_OrdinalPresentation_actual_family_and_ordinal_presentation_complete": True,
        "source_OrdinalPresentation_actual_dense_coverage_complete": True,
        "source_SliceGeometry_actual_subset_image_surjection_complete": True,
        "source_OrderedSections_LeastOccurrence_internal_ordinal_dense_unique_complete": True,
        "source_OrderedSections_wellorderable_check_dense_complete": True,
        "source_OrderedSections_indexedSection_exists_complete": True,
        "source_OrderedSections_leastRelation_injection_complete": False,
        "source_OrderedSections_checked_index_leastRelation_injection_complete": True,
        "source_OrderedSections_actual_indexedImage_cover_one_complete": True,
        "source_OrderedSections_wellorderable_image_complete": True,
        "source_OrderedSections_leastRelation_scope": "Actual supported HS graph and full source injection in ordinary nativeZF for INTERNAL ordinal checked-index forcing families; source Cover/OneAt/common support/check(O) remain explicit. Arbitrary host-selected wellorder families are not claimed; actual indexedImage/wellorderable_image are complete in their adapter. Uniform section/slice consumers remain incomplete.",
        "source_OrderedSections_uniform_section_injection_and_wellorderable_target_complete": True,
        "source_UniformImages_uniform_maximum_dense_family_wrapper_complete": True,
        "source_UniformImages_uniform_maximum_dense_family_scope": "Actual internal FunctionOn family over ALL members of an arbitrary internal index set, for definable functional Q parameters; same condition and support prepared before witnesses. Existing localized_maximum, Collection and donor uniformization genuinely consumed. Ordinary nativeZF kernel SAME-L relative sentence discharges ground Choice. Source n is finite syntactic arity, not an index bound. Arbitrary external Sort families and actual section/slice consumers are not claimed complete.",
        "source_OrderedSections_and_full_slice_geometry_assembly_complete": True,
        "source_OrdinalPresentation_scope": "Full pinned OrdinalPresentation:342-412. Actual full index/family, supporting diagram extension, dense cover, existing INTERNAL ordinal reindexing and actual Cartesian/completion graph surjection; all internal conditions and unrestricted HS names. The nativeZF object-kernel endpoint uses the already completed internal L interpretation to discharge ground Choice. Source mathematical background guards remain explicit. No given family, cover, ordinal enumeration, Cartesian domain or final surjection. Main global reverse injection, PP and all-internal/nonstandard Con remain incomplete.",
        "source_UniformImages_kernel_graph_scope": "Pinned UniformImages:16-169. Original nativeZF Derives actually constructs the SAME three-name support and raw HS kernel graph, then proves the regular/monotone/congruent imageClassRelation, exact movement under the constructed support, and conditional One/Injective at EVERY internal condition under the FULL original mapsTo formula. Exact separated-class witnesses use the existing literal class uniqueness and class movement, with no quotient representative. Existing force_congr/atomic_congr transport the SAME graph into its extended binder environment; no graph/support/fixedness or final law is supplied to the new existence sentence. Actual image quotient/graph and the SAME-system nonwellorderable image bijection are now complete in their own source adapters. Remaining stage9 model applications, PP/Main and all-internal/nonstandard Con remain pending.",
        "source_SliceGeometry_piece_family_original_kernel_constructed": True,
        "source_SliceGeometry_support_before_all_internal_indices": True,
        "source_SliceGeometry_full_graph_surjections_source_disjointness_cover_and_assembly_complete": True,
        "source_SliceGeometry_full_slice_and_part_graph_surjections_native_kernel_complete": True,
        "source_SliceGeometry_Spart_disjointness_native_kernel_complete": True,
        "source_SliceGeometry_occurrence_and_actual_Ypart_name_cover_native_kernel_complete": True,
        "source_SliceAssembly_empty_domain_and_nonwellorderable_member_native_kernel_complete": True,
        "source_SliceAssembly_actual_two_name_parameter_total_unique_HS_fixed_native_kernel_complete": True,
        "source_SliceAssembly_separate_parameter_FunctionOn_required": False,
        "source_SliceAssembly_actual_slice_candidate_native_kernel_complete": True,
        "source_SliceAssembly_all_four_actual_UniformMaximum_inputs_complete": True,
        "source_SliceAssembly_actual_internal_candidate_FunctionOn_family_constructed": True,
        "source_SliceAssembly_actual_assemble_native_kernel_complete": True,
        "source_SliceAssembly_actual_assemble_output_retains_Graph_HS_support_full_injection": True,
        "source_SliceAssembly_slice_candidate_and_assemble_complete": True,
        "source_SliceAssembly_presentation_reverse_injection_complete": True,
        "source_SliceAssembly_actual_candidate_support_intersection_and_assembly_composed": True,
        "source_SliceGeometry_piece_family_scope": "Ordinary nativeZF Derives constructs one actual common support, then check(i), B/Ypart/Spart names for every INTERNAL i in the WHOLE O, with exact raw edges and same-support HS. Source literal-pair slice equivalence, exact B/occurrence/Ypart/Spart member laws and internal-ordinal Ypart disjointness are compiled helpers. No supplied support/check/piece family, finite-index/rank cutoff, new Choice/L/foundation, external family, or completed FunctionOn graph of all pieces. Actual slice/part graph surjections, Spart disjointness, occurrence and actual Ypart-name cover now have separate ordinary nativeZF endpoints. The actual definable two-name parameter relation is now total/unique/HS/fixed in nativeZF; existing UniformMaximum consumes it directly, so a separate parameter FunctionOn is not required. Actual slice_candidate, force(ex injection), all four UniformMaximum.Inputs and the actual all-internal FunctionOn candidate family now have an ordinary nativeZF L-relative original-kernel endpoint. Source assemble now has a separate ordinary nativeZF original-kernel endpoint retaining actual Graph, HS, support and FULL injection/functionOn/no-junk. Its candidate FunctionOn and support are exactly the original source consumer inputs, already separately constructed by ForcingSliceCandidate. The actual candidate family, existing support intersection, strict raw ParameterSpec/graph transport and full assemble are now composed in the ordinary nativeZF L-relative presentation_reverse_injection endpoint. Full Main all-set reverse_injection_dense and actual forces_PP now have an ordinary nativeZF L-relative endpoint, with actual presentation/support and both branches discharged. forces_target is complete in its own same-system native kernel adapter; all-internal Main/nonstandard Con and Comparator remain pending.",
        "original_stage9_model_applications_complete": True,
        "source_Main_all_set_reverse_injection_dense_complete": True,
        "source_Main_actual_full_PP_forced_on_same_Core": True,
        "source_Main_PP_requires_no_dense_or_surjection_oracle": True,
        "source_Main_forces_target_complete": True,
        "source_Main_target_axiom_schema_native_kernel_existence_complete": True,
        "source_Main_target_schema_index_is_external": True,
        "source_Main_target_uniform_internal_coded_axiom_forcing_complete": False,
        "source_ConcreteSystem_scope": "ForcingConcreteSystem.kernel_certificate proves existence of all actual same-L primitive parents and the SAME-system uniform quotient consequence. No given omega/system remains. Existing fixed-schema forcing/action proofs are retained; standalone concrete full-schema export booleans do not claim a new export here. Stage9 model applications and actual PP are complete in ForcingReverseInjection. forces_target is complete in its own same-system native kernel adapter; all-internal Main/Proof/Con and Comparator remain incomplete.",
        "source_initial_base_internal_omega_addition_table_constructed": True,
        "source_initial_base_left_cancel_conical_unit_and_generator_proved": True,
        "source_initial_base_le_iff_and_pair_joins_proved": True,
        "source_initial_base_algebra_native_kernel_certificate_proved": True,
        "source_probe_path_factor_terminal_graphs_and_laws_kernel_proved": True,
        "source_probe_transition_graphs_directed_system_kernel_proved": True,
        "source_probe_actual_direct_limit_quotient_and_projection_kernel_proved": True,
        "source_probe_letter_equality_iff_common_stage_proved": True,
        "source_probe_quotient_action_and_target_constructed": True,
        "source_probe_action_identity_composition_injective_and_target_equivariant_kernel_proved": True,
        "source_probe_exit_equivariance_dvd_target_and_head_separation_kernel_proved": True,
        "source_probe_alphabet_cone_intersection_profile_and_letter_cardinal_bounds_proved": True,
        "source_probe_alphabet_constructed": True,
        "source_probe_raw_carrier_and_constructor_cases_kernel_proved": True,
        "source_probe_raw_old_action_and_reduced_word_proved": True,
        "source_probe_word_quotient_graph_and_inverse_laws_proved": True,
        "source_probe_letter_front_reduction_equivariance_and_injectivity_kernel_proved": True,
        "source_probe_raw_eval_total_unique_old_cons_equations_kernel_proved": True,
        "source_probe_raw_eval_oldAct_and_injectivity_proved": True,
        "source_probe_raw_eval_and_word_monoid_proved": True,
        "source_probe_actual_old_embedding_factor_divisibility_and_conical_kernel_proved": True,
        "source_probe_actual_generator_graph_relations_and_old_gate_kernel_proved": True,
        "source_probe_evalHom_and_actual_liftHom_arbitrary_target_monoid_kernel_proved": True,
        "source_probe_Word_hom_ext_actual_graph_equality_kernel_proved": True,
        "source_probe_actual_indexed_probe_graph_and_presentedHom_ext_kernel_proved": True,
        "source_probe_adjacent_transport_and_actual_interpretedLetter_equivariance_kernel_proved": True,
        "source_probe_actual_word_carrier_multiplication_left_cancel_monoid_kernel_proved": True,
        "source_probe_indexed_relations_and_unique_presentedHom_kernel_proved": True,
        "source_probe_raw_and_extension_cardinal_bounds_kernel_proved": True,
        "source_probe_actual_mapped_path_and_letter_map_kernel_proved": True,
        "source_probe_actual_alphabet_simulation_kernel_proved": True,
        "source_probe_raw_transport_and_reducedness_kernel_proved": True,
        "source_probe_reduced_word_transport_embedding_kernel_proved": True,
        "source_probe_actual_transportHom_kernel_proved": True,
        "source_probe_actual_old_embedding_full_conservative_kernel_proved": True,
        "source_probe_head_and_gate_local_laws_kernel_proved": True,
        "source_probe_suffix_intersection_gate_kernel_proved": True,
        "source_probe_head_transport_kernel_proved": True,
        "source_probe_shared_old_intersections_kernel_proved": True,
        "source_probe_shared_gate_existence_kernel_proved": True,
        "source_probe_word_transport_factors_kernel_proved": True,
        "source_probe_word_transport_common_below_kernel_proved": True,
        "source_probe_conservative_simulation_transport_proved": True,
        "source_probe_simulation_old_and_indexed_probe_same_graph_kernel_proved": True,
        "source_probe_word_conditional_joins_proved": True,
        "source_probe_word_left_cancel_conical_conditional_joins_kernel_proved": True,
        "source_probe_word_full_profile_proved": True,
        "source_probe_old_gates_proved": True,
        "source_probe_successor_profile_preservation_proved": True,
        "source_probe_simulation_pushout_proved": True,
        "source_probe_letter_floor_graph_and_order_bounds_proved": True,
        "source_probe_inside_outside_cost_bounds_from_old_point_bound_proved": True,
        "source_initial_base_PointBound_adapter_proved": True,
        "source_initial_base_UniformMargins_HeightOrder_adapter_proved": True,
        "source_probe_interval_cut_addition_and_max_constructed": True,
        "source_probe_positive_cut_division_graph_constructed": True,
        "source_probe_actual_cut_quarter_graph_constructed": True,
        "source_probe_actual_cut_quarter_fourfold_sum_identity_proved": True,
        "source_probe_actual_cut_addition_associativity_proved": True,
        "source_probe_general_cut_difference_exact_recovery_proved": True,
        "source_probe_cut_addition_order_reflection_cancellation_proved": True,
        "source_probe_pointwise_letter_intervals_from_old_uniform_margin_proved": True,
        "source_probe_letter_intervals_constructed": True,
        "source_probe_successor_HeightCost_PointBound_instantiated": False,
        "source_probe_actual_cut_product_graph_constructed": True,
        "source_probe_actual_cut_product_positive_mono_zero_laws_proved": True,
        "source_probe_actual_cut_minimum_total_positive_proved": True,
        "source_probe_actual_Word_height_total_unique_map_proved": True,
        "source_probe_actual_gateCap_total_unique_graph_proved": True,
        "source_probe_actual_Word_cost_total_unique_map_proved": True,
        "source_probe_actual_Word_cost_positive_unit_bound_proved": True,
        "source_probe_actual_cut_product_unit_law_proved": True,
        "source_probe_actual_Word_height_bounds_cost_scale_proved": True,
        "source_probe_actual_old_cost_factor_from_existing_profiles_proved": True,
        "source_probe_literal_gate_outside_block_cost_proved": True,
        "source_probe_old_old_strict_uniform_margin_proved": True,
        "source_probe_old_new_strict_uniform_margin_proved": True,
        "source_probe_new_old_strict_uniform_margin_proved": True,
        "source_probe_Word_exact_old_cost_supremum_proved": True,
        "source_probe_required_positive_affine_cut_scaling_proved": True,
        "source_probe_same_head_and_all_internal_uniform_margins_proved": True,
        "source_probe_Word_complete_actual_HeightCost_constructed": True,
        "source_probe_extension_height_cost_margin_proved": True,
        "additional_pinned_sequence_restriction_Bool_certificates_reevaluated": 6,
        "source_probe_complete_extension_package_proved": True,
        "source_probe_same_carrier_weighted_request_package_constructed": True,
        "source_probe_parent_Path_alphabet_interval_producer_composition_complete": True,
        "source_merger_actual_prescribed_copies_and_right_free_action_constructed": True,
        "source_merger_actual_Word_carrier_right_action_and_product_constructed": True,
        "source_merger_Word_monoid_and_left_cancel_proved": True,
        "source_merger_actual_copies_conditional_joins_proved": True,
        "source_merger_Word_conditional_joins_proved": True,
        "source_merger_old_common_multiples_and_cones_preserved_proved": True,
        "source_merger_actual_old_inclusion_full_Conservative_and_gates_constructed": True,
        "source_merger_all_old_profiles_preserved_proved": True,
        "source_merger_actual_roots_exact_prescription_realization_and_newness_proved": True,
        "source_merger_actual_coordinate_height_cost_graphs_constructed": True,
        "source_merger_coordinate_bounds_monotonicity_and_represented_strictness_proved": True,
        "source_merger_copies_literal_average_and_min_product_function_graphs_constructed": True,
        "source_merger_copies_height_cost_positivity_cap_and_all_copy_estimates_proved": True,
        "source_merger_copies_average_height_mono_strictMono_and_cost_unit_bound_proved": True,
        "source_merger_copies_average_height_lt_canonical_unit_proved": True,
        "source_merger_copies_average_coordinate_gap_proved": True,
        "source_merger_copies_coordinate_margin_proved": True,
        "source_merger_copies_finite_uniform_actual_supremum_margin_proved": True,
        "source_merger_copies_average_product_heightCost_proved": True,
        "source_merger_copies_complete_heightCost_same_parent_producer_proved": True,
        "source_merger_word_actual_height_cost_graphs_and_pointwise_bounds_proved": True,
        "source_merger_word_complete_heightCost_proved": True,
        "source_merger_word_uniform_margin_all_internal_comparisons_proved": True,
        "source_merger_word_actual_supremum_strict_margin_proved": True,
        "source_merger_word_all_old_pairs_exact_missed_cost_family_and_cap_proved": True,
        "source_merger_word_snoc_existential_witness": "room*(unit/4); literal source weight formulas unchanged",
        "source_merger_word_old_cost_supremum_proved": True,
        "source_merger_complete_weighted_extension_package_proved": True,
        "source_merger_cardinality_from_same_actual_copies_and_Raw_proved": True,
        "source_merger_cardinality_is_conditional_output_not_construction_premise": True,
        "source_merger_same_original_parent_weighted_request_producer_proved": True,
        "source_merger_same_old_inclusion_marked_nonunit_and_height_cost_preserved": True,
        "source_directed_limit_actual_varying_carrier_projection_and_all_stage_maps_proved": True,
        "source_directed_limit_actual_common_stage_pair_and_triple_proved": True,
        "source_directed_limit_of_map_and_conditional_transition_injectivity_proved": True,
        "source_directed_limit_carrier_quotient_requires_transition_injectivity": False,
        "source_directed_limit_monoid_and_conservativity_proved": True,
        "source_directed_limit_same_actual_multiplication_and_unit_constructed": True,
        "source_directed_limit_associative_LeftCancelMonoid_and_conditional_Conical_proved": True,
        "source_directed_limit_every_stage_actual_MonoidHom_proved": True,
        "source_directed_limit_monoid_requires_transition_injectivity": False,
        "source_directed_limit_full_Conservative_maps_proved": True,
        "source_directed_limit_of_factors_and_exact_divisibility_reflection_proved": True,
        "source_directed_limit_conditional_joins_from_actual_stages_proved": True,
        "source_directed_limit_all_later_stage_profile_transport_proved": True,
        "source_directed_limit_profile_initial_assumed_or_HasOldGates_required": False,
        "source_directed_limit_complete_weighted_limit_proved": True,
        "source_directed_limit_actual_height_cost_graphs_four_bounds_and_exact_cap_margins_proved": True,
        "source_directed_limit_all_old_pairs_actual_families_same_unique_supremum_proved": True,
        "source_directed_limit_weighted_scope": "Complete generic weighted pointed Object, actual canonical cocone family and full universal lift/fac/uniq; original Choice explicit only in cardinal output. Actual final weighted tower/request schedule remain open",
        "source_directed_limit_cardinality_and_marked_Object_assembly_proved": True,
        "source_directed_limit_cardinality_source_object_Choice_explicit_in_output_only": True,
        "source_directed_limit_distinguished_mark_nonunit_and_all_inclusion_mark_equations_proved": True,
        "source_directed_limit_complete_pointed_weighted_object_constructed": True,
        "source_directed_limit_actual_canonical_cocone_leg_family_and_naturality_constructed": True,
        "source_directed_limit_full_weighted_pointed_conservative_lift_fac_unique_proved": True,
        "source_directed_limit_actual_generic_universal_colimit_constructed": True,
        # Final saturation/CompleteRounds tower; single-round recursion is recorded separately below.
        "source_directed_limit_actual_universal_colimit_and_final_tower_constructed": False,
        "source_request_map_both_ProbeData_and_MergerData_constructors_proved": True,
        "source_request_map_actual_partial_start_graph_and_exact_one_step_relation_reflection_proved": True,
        "source_request_map_validity_iff_all_target_elements_without_transitive_closure_proved": True,
        "source_request_map_actual_internal_path_and_nonunit_payload_unique_proved": True,
        "source_request_map_scope": "Both parameter constructors transported and BOTH actual full weighted Round.step successors/fromBase/operation witnesses now constructed. Given Schedule maps uniformly at VARYING stages; actual ordinal iteration and final exhaustive CompleteRounds are completed by the accepted SaturationIteration/ConcreteTower consumers",
        "source_round_step_actual_both_weighted_successors_and_same_fromBase_constructed": True,
        "source_round_step_original_base_Probe_profile_and_Merger_root_realization_retained": True,
        "source_round_step_full_fields_all_profiles_same_old_cap_and_cardinality_retained": True,
        "source_request_schedule_actual_unique_mapped_graph_arbitrary_varying_stage_domains_constructed": True,
        "source_request_schedule_uniform_graph_has_fixed_target_carrier_or_omega_index_restriction": False,
        "source_round_same_L_whole_successor_tuple_selector_total_unique_all_inputs": True,
        "source_round_same_L_selected_successor_both_requests_actual_full_parent_producer": True,
        "source_round_same_chosen_successor_all_old_stage_map_family_constructed": True,
        "source_round_successor_all_existing_fromBase_naturality_and_full_MapFields_preserved": True,
        "source_round_old_current_identity_leg_maps_exact_same_inclusion_proved": True,
        "source_round_native_ordinal_append_actual_new_carrier_and_self_identity_constructed": True,
        "source_round_actual_Under_base_limit_full_weighted_object_and_all_leg_fields_constructed": True,
        "source_round_actual_Under_base_limit_unique_fromBase_all_old_triangles_proved": True,
        "source_directed_profile_mapped_function_parameter_correctly_typed": True,
        "source_actual_typed_transition_Profiles_discharge_source_persistent_hP_kernel_proved": True,
        "source_round_initial_successor_limit_values_unique_under_original_case_parents": True,
        "source_round_all_three_state_values_same_nine_field_codec_full_self_family": True,
        "source_round_initial_packet_time_object_zero_successor_limit_time_internal_J": True,
        "source_round_record_history_nine_actual_field_graphs_constructed": True,
        "source_round_record_history_all_index_transition_matrix_exact_target_incoming_leg": True,
        "source_round_record_history_internal_ordinal_original_index_laws_proved": True,
        "source_round_full_record_history_validity_pure_formula_defined": True,
        "source_round_21_original_weighted_diagram_Under_base_parents_derived_from_record_validity": True,
        "source_round_actual_canonical_limit_from_record_history_total_unique": True,
        "source_round_actual_initial_history_full_algebraic_profile_coherence_validity_proved": True,
        "source_round_same_original_selected_successor_from_full_valid_history_total_unique": True,
        "source_round_actual_successor_and_limit_append_preserve_complete_Valid": True,
        "source_round_both_original_case_parent_constructors_return_unique_record_and_actual_valid_append": True,
        "source_round_concrete_binary_operator_total_unique_on_ALL_internal_set_histories": True,
        "source_round_native_ordinal_recursion_instantiated_with_SAME_actual_source_operator": True,
        "source_round_internal_formula_separation_ordinal_induction_full_recursive_validity_proved": True,
        "source_round_actual_recursive_tower_all_field_tables_time_identity_global_base_naturality_constructed": True,
        "source_round_exact_global_map_succ_original_request_equation_exported": True,
        "source_round_SELECTED_actual_probe_generator_stored_in_existing_tuple_and_CURRENT_inclusion_freshness_retained": True,
        "source_round_SELECTED_merger_roots_CURRENT_inclusion_freshness_retained": True,
        "source_round_actual_global_map_succ_exports_SAME_current_fresh_request_witness": True,
        "source_round_selected_successors_retain_ACTUAL_alphabet_normal_word_and_free_action_provenance": True,
        "source_round_actual_global_map_succ_exports_SAME_original_operation_source_data": True,
        "source_original_Probe_independent_exact_common_exit_cone_all_internal_words_proved": True,
        "source_actual_request_Provenance_implies_same_chosen_probe_independence_kernel_proved": True,
        "source_original_Probe_gate_independence_and_Merger_full_RootSystem_transferred": True,
        "source_original_Merger_full_RootSystem_all_internal_extension_elements_kernel_proved": True,
        "source_actual_request_Provenance_implies_same_chosen_Merger_RootSystem_kernel_proved": True,
        "source_full_Probe_and_Merger_exact_cones_later_cut_transport_complete": True,
        "source_exact_later_cones_construct_actual_image_and_composite_graphs": True,
        "source_actual_recursive_tower_all_internal_later_cuts_original_request_cones_kernel_proved": True,
        "source_actual_recursive_tower_Merger_final_base_equals_SAME_target_row_fromBase": True,
        "source_actual_recursive_tower_Probe_composite_equals_global_F_i_k_full_MapFields_profile_and_current_freshness": True,
        "source_actual_tower_SAME_Picked_raw_execution_and_ninth_field_graphs_constructed": True,
        "source_actual_tower_canonical_fixed_request_cut_probe_family_total_unique_profile_proved": True,
        "source_actual_tower_canonical_probe_cross_cut_transition_kernel_proved": True,
        "source_actual_tower_canonical_probe_family_injective_and_pairwise_independent_complete": True,
        "source_actual_constructed_cut_probe_family_returns_Injection_and_exact_fromBase_exit_cones": True,
        "source_CompleteRound_final_K_Place_last_target_inclusion_and_probe_assembly_complete": True,
        "source_CompleteRound_constructed_from_original_parents_including_actual_Request_schedule_tower": True,
        "source_CompleteRound_every_merger_full_RootSystem_on_same_target_complete": True,
        "source_CompleteRound_original_parent_forall15_internal_L_relative_native_kernel_certificate": True,
        "source_CompleteRound_actual_schedule_recursion_execution_and_last_row_trace_retained": True,
        "source_Saturation_valid_original_parent_complete_round_selected_uniquely_with_native_kernel_certificate": True,
        "source_Saturation_actual_selected_successor_updates_ALL_old_legs_and_base_and_exact_current_inclusion": True,
        "source_Saturation_actual_successor_append_preserves_full_Valid_and_AllSmall": True,
        "source_Saturation_concrete_history_operator_total_unique_on_ALL_internal_set_histories": True,
        "source_Saturation_existing_native_ordinal_recursion_actually_instantiated": True,
        "source_Saturation_actual_full_recursive_Valid_AND_AllSmall_proved_by_internal_formula_induction": True,
        "source_Saturation_full_internal_multiround_recursive_tower_constructed": True,
        "source_Saturation_all_twelve_tables_time_full_weighted_diagram_and_stage_bounds_constructed": True,
        "source_Saturation_global_adjacent_map_equals_SAME_trace_bearing_selected_complete_round_inclusion": True,
        "source_Saturation_concrete_internal_Hartogs_omega_regular_index_and_successor_mu_small_constructed": True,
        "source_Saturation_omega1_plus_one_actual_recursive_tower_constructed": True,
        "source_Saturation_original_omega1_le_mu_parent_preserved": True,
        "source_Saturation_ConcreteSystem_mu_K_instantiation_complete": False,
        "source_RoundOrdinal_countable_bounded_ALL_internal_countable_domains_actual_range_constructed_native_kernel_certificate": True,
        "source_RoundOrdinal_countable_subset_bound_native_kernel_certificate": True,
        "source_Saturation_actual_limit_representatives_read_from_SAME_recursive_history_and_global_matrix": True,
        "source_Saturation_internal_birth_index_function_and_actual_lift_graph_constructed": True,
        "source_Saturation_countable_proper_stage_coverage_complete": True,
        "source_Saturation_countable_stage_SAME_constructed_tower_native_kernel_certificate": True,
        "source_Saturation_concrete_omega1_index_and_countable_stage_cover_instantiated": True,
        "source_SaturatedMonoids_probe_stage_actual_parameter_lift_and_conservative_path_reflection_complete": True,
        "source_SaturatedMonoids_SAME_selected_complete_round_inclusion_afterRound_and_profile_transport_complete": True,
        "source_SaturatedMonoids_final_Probe_saturation_K_injection_full_final_divisor_profiles_exact_intersections_native_kernel_certificate": True,
        "source_SaturatedMonoids_finite_prescription_stage_complete": True,
        "source_SaturatedMonoids_final_finiteMergers_complete": True,
        "source_SaturatedMonoids_prescription_stage_no_Valid_premise_full_literal_optional_table_round_trip": True,
        "source_SaturatedMonoids_all_internal_n_in_omega_including_empty_index_preserved": True,
        "source_SaturatedMonoids_SAME_final_roots_full_RootSystem_AND_exact_product_equality_iff_GIVEN_CopyRel_native_kernel_certificate": True,
        "source_SaturatedMonoids_complement_probes_same_final_tower_native_kernel_certificate": True,
        "source_SaturatedMonoids_target_and_complement_cardinality_internal_bijections_complete": True,
        "source_DiagramOrder_internal_supremum_grid_and_directed_cofinal_proof_consumed_by_final_ideal_kernel_certificate": True,
        "source_ConeIdeal_no_countability_premise_internal_unit_and_all_indices_preserved": True,
        "source_SaturatedMonoids_all_final_divisors_arbitrary_internal_ideal_probes_native_kernel_certificate": True,
        "source_SaturatedMonoids_ideal_complement_probes_and_cardinal_endpoints_complete": True,
        "source_ConcreteSystem_actual_full_power_set_continuum_successor_mu_regular_and_countable_power_native_kernel_certificate": True,
        "source_ConcreteSystem_K_equal_actual_mu_consumed_by_SAME_IdealTower_native_kernel_certificate": True,
        "source_ConcreteSystem_fully_concrete_Base_T_without_geometric_parent_contract_complete": True,
        "source_PlacementExtensions_exact_internal_obstructions_and_fresh_member_kernel_certificates": True,
        "source_PlacementExtensions_set_valued_family_actual_row_relation_constructed": True,
        "source_PlacementExtensions_ground_Choice_discharged_in_same_internal_L": True,
        "source_PlacementExtensions_actual_infinite_budget_permutation_and_two_three_copy_placements_complete": True,
        "source_DiagramPlacements_exact_internal_extend_permutation_off_kernel_certificate": True,
        "source_ConcreteSystem_actual_Hartogs_label_set_non_small_native_ZF_kernel_certificate": True,
        "source_ConcreteSystem_SAME_actual_label_set_ALL_internal_placement_inputs_kernel_certificate": True,
        "source_DiagramPlacements_finite_overlap_paste_two_three_copy_complete": True,
        "source_DiagramPlacements_simultaneous_three_copy_ALL_exact_image_intersections_kernel_certificate": True,
        "source_DiagramPlacements_actual_Diagram_common_extension_and_Product_descent_constructions_complete": True,
        "source_actual_Diagram_exact_cone_range_and_common_sub_label_iff_kernel_certificates": True,
        "source_actual_Diagram_full_ExactOverlap_of_common_and_actual_permuted_graph_equality_kernel_certificates": True,
        "source_actual_Diagram_same_position_root_fixed_permutation_kernel_certificate": True,
        "source_actual_Diagram_overlap_prescription_and_amalgamate_constructed": True,
        "source_actual_Diagram_literal_optional_overlap_prescription_constructed": True,
        "source_actual_Diagram_GIVEN_CopyRel_iff_actual_labels_and_Valid_kernel_certificate": True,
        "source_actual_Diagram_no_diagonal_or_disjoint_start_and_no_junk_rows": True,
        "source_actual_Diagram_SAME_final_row_Merger_consumed_with_SAME_constructed_P": True,
        "source_actual_Diagram_whole_amalgamating_injection_constructed": True,
        "source_actual_Diagram_SAME_P_roots_WHOLE_carrier_all_internal_finite_family_common_extension_kernel_certificate": True,
        "source_actual_Diagram_amalgamate_supplied_whole_embedding_or_diagram_premise": False,
        "source_actual_Diagram_fixed_three_family_and_Cohen_descent_consumers_complete": True,
        "source_actual_Diagram_fixed_three_internal_family_common_extension_kernel_certificate": True,
        "source_actual_Cohen_compatibility_union_and_full_descent_complete": True,
        "source_actual_full_descent_comparison_placement_Product_lower_bound_kernel_certificate": True,
        "source_actual_descent_supplied_placements_or_output_lower_bound_premise": False,
        "source_actual_binary_countable_hull_all_internal_omega_complete": True,
        "source_actual_countable_conservative_hull_original_kernel_certificate": True,
        "source_actual_countable_conservative_hull_supplied_output_closure": False,
        "source_actual_ComponentGluing_vertex_root_and_exact_contraction_preserved": True,
        "source_actual_ComponentGluing_nine_geometry_laws_nativeZF_kernel_certificate": True,
        "source_actual_ComponentGluing_ALL_internal_vertex_carrier_constructed": True,
        "source_actual_ComponentGluing_entire_Common_component_cofinal_chain_kernel_certificate": True,
        "source_actual_ComponentGluing_internal_finite_zigzag_equivalence": False,
        "source_actual_ComponentGluing_System_Fiber_arrowMap_gluing_complete": False,
        "source_actual_CellTowers_actual_Attachment_dependencies_reordering_complete": False,
        "source_actual_CellTowers_hull_and_ComponentGluing_consumers_complete": False,
        "source_actual_ConservativeHull_ComponentGluing_complete": False,
        "source_actual_Cohen_label_support_countable_restriction_constructed": True,
        "source_actual_Cohen_TWO_existing_coordinate_lifts_exact_label_move_kernel_certificate": True,
        "source_actual_Cohen_agreement_trigger_overlap_and_three_union_kernel_certificates": True,
        "source_actual_Cohen_s0_restriction_and_s1_overlap_ranges_identified": False,
        "source_ConcreteSystem_SAME_actual_final_row_full_ObjectFields_Probes_Mergers_Ideals_Complement_and_Cardinals": True,
        "source_Saturation_multiround_actual_system_complete": True,
        "source_round_actual_full_valid_history_operator_instantiated": True,
        "source_round_actual_ordinal_iteration_and_global_fromBase_naturality_constructed": True,
        "source_CompleteRounds_actual_exhaustive_enumeration_and_final_saturated_monoid_constructed": True,
        "source_CompleteRounds_full_internal_canonical_Request_carrier_and_defaultProbe_constructed": True,
        "source_CompleteRounds_actual_exhaustive_underlying_Request_times_K_top_Schedule_and_Place_graphs_constructed": True,
        "source_CompleteRounds_every_Request_K_pair_non_top_position_and_K_place_injection_proved": True,
        "source_CompleteRounds_original_Request_data_cardinal_le_instantiated": True,
        "source_CompleteRounds_actual_small_Request_carrier_constructed": True,
        "source_Request_cardinal_bound_preserves_complete_partial_start_graph_all_internal_n_and_diagonals": True,
        # Request and SAME actual ordinal-index bounds are proved; final CompleteRounds/saturation is separate.
        "source_CompleteRounds_actual_WithTop_and_SAME_canonical_ordinal_and_last_size_bounds_proved": True,
        "source_round_actual_recursive_tower_ALL_internal_stage_cardinal_bounds_proved": True,
        "source_round_actual_bounded_tower_constructor_retains_ALL_fields_global_map_succ_and_stage_bounds": True,
        "source_CompleteRounds_internal_wellorder_ordinal_index_and_original_Request_cardinal_bounds_instantiated": True,
        "source_CompleteRounds_actual_chosen_internal_product_and_WithTop_wellorders_constructed": True,
        "source_CompleteRounds_every_designated_place_strictly_before_top_proved": True,
        "source_CompleteRounds_actual_canonical_ordinal_type_and_equinumerosity_constructed": True,
        "source_CompleteRounds_chosen_wellorder_object_Choice_explicit_antecedent": True,
        "source_CompleteRounds_schedule_transported_to_ordinal_graph_constructed": True,
        "source_CompleteRounds_actual_canonical_collapse_inverse_and_ordinal_Place_graphs_constructed": True,
        "source_CompleteRounds_actual_ordinal_successor_endpoint_and_every_pair_before_last_proved": True,
        "source_CompleteRounds_ordinal_schedule_from_full_original_monoid_parents_constructed": True,
        "source_initial_base_height_cost_and_margin_proved": True,
        "source_initial_base_height_cost_fraction_graphs_constructed": True,
        "source_initial_base_fraction_numerator_positive_below_denominator_proved": True,
        "source_initial_base_fraction_graph_native_kernel_certificate_proved": True,
        "source_initial_base_fraction_order_density_kernel_proved": True,
        "source_initial_base_fraction_cut_order_completion_proved": True,
        "source_initial_base_principal_cut_equivalence_and_order_reflection_proved": True,
        "source_initial_base_cut_bounded_set_suprema_proved": True,
        "source_initial_base_height_cost_cut_graphs_and_positive_unit_bounds_proved": True,
        "source_initial_base_fraction_addition_total_unique_commutative_order_reflection_proved": True,
        "source_initial_base_principal_addition_representation_independence_proved": True,
        "source_initial_base_weight_principal_addition_kernel_proved": True,
        "source_principal_cut_nonnegative_difference_kernel_proved": True,
        "source_base_margin_exact_nonempty_cost_image_and_supremum_bound_kernel_proved": True,
        "source_base_margin_strict_height_gap_estimate_proved": True,
        "source_initial_base_actual_cut_graphs_and_full_margin_kernel_proved": True,
        "source_initial_base_margin_scope": "Actual original n+1/n+3 weight graphs with positive unit bounds and, for every internal x<y, exact nonempty missed-cost image supremum strictly below the represented additive height gap. Native kernel certificate constructs the data. This is not arbitrary-cut field arithmetic or the later source extensions/final monoid.",
        "source_arbitrary_cut_addition_proved": False,
        "source_initial_base_fraction_real_interpretation_proved": False,
        "source_initial_base_fraction_carrier_total_preorder_constructed": True,
        "source_initial_base_fraction_order_native_kernel_certificates_proved": True,
        "source_initial_base_unit_fraction_reverse_denominator_order_proved": True,
        "source_initial_base_fraction_codes_claimed_antisymmetric": False,
        "source_initial_base_fraction_order_scope": "Internal natural fraction-code carrier and cross-multiplication total preorder; includes both source weight graphs. Unit fractions have precisely reversed denominator order. Equivalent fraction codes remain distinct, but their principal cuts are proved equal. Rounded cut completion and cut-valued source weight graphs are now constructed. Full Base numeric margin is proved in the cut representation; complete arbitrary-cut field arithmetic remains unproved.",
        "source_initial_base_weights_scope": "Exact internal natural fraction graphs ((2^(n+1)-1),2^(n+1)) and (1,2^(n+3)); positive numerator strictly below denominator. All internal omega, including nonstandard. The actual cut-valued source weights and their full strict margin are proved separately; no complete arbitrary-cut field or final construction is claimed.",
        "source_initial_base_scope": "Only initial Base.M algebra, exact internal addition graph, zero unit, nonzero successor generator and pair joins. All internal/nonstandard naturals; the separately constructed exact cut weight graphs now supply the full Base margin. The initial data must be consumed by the original extension interfaces. Final saturated construction and final Con remain incomplete.",
        "source_product_WithTop_action_instantiated": True,
        "source_product_WithTop_top_fixed_and_group_laws_proved": True,
        "source_product_WithTop_uniform_label_family_instantiated": True,
        "source_product_uniform_action_support_context_constructed": True,
        "source_product_uniform_action_HS_closure_native_certificate_proved": True,
        "source_product_action_context_assumes_HS_closure_or_NormalImage": False,
        "source_product_uniform_action_actual_HS_formula_symmetry_proved": True,
        "source_product_formula_symmetry_assumes_order_transport_or_domain_closure": False,
        "source_cohen_omega_two_fixed_carriers_family_constructed": True,
        "source_product_WithTop_scope": "Internal empty/singleton carrier, actual extension of the constructed product permutation, fixed top, exact coe edges/order and identity/composition. Uniform fixed-carrier formula, unique actions, Family/Covariance, support-filter Context construction and HS closure are now proved. Source omega/two fixed carriers and actual HS-domain formula symmetry are now proved. ProductPoset proves actual preorder, antisymmetry and internal top under the source left-cancel monoid/conical contract. The same actual final monoid is constructed by ConcreteBase/Tower; actual Models system consumers remain.",
        "source_cohen_order_action_scope": "All internal level/value carriers and injection bounds; products, exact coordinate permutations, bounded partial-function carrier and reverse-inclusion automorphism constructed in one native theorem. Label identity/composition and actual Cohen/diagram product assembly are now proved. WithTop extension is constructed. Uniform action-family and support Context are now constructed; source omega/two fixed carriers are constructed; monoid/conical system assembly remains.",
        "source_diagram_all_injection_carrier_and_set_action_constructed": True,
        "source_diagram_set_action_identity_and_multiplication_proved": True,
        "source_diagram_sub_constructed_from_left_cancellation_table": True,
        "source_diagram_translation_relation_preserved_and_reflected": True,
        "source_diagram_order_scope": "All internal diagram injections; internal multiplication table; sub constructed from fixed-left totality/functionality/cancellation. Translation-relation automorphism constructed. Concrete monoid/conical partial-order premises not yet instantiated. Cohen/product/WithTop permutations and relation invariance are constructed; uniform action-family and HS context are now instantiated; concrete monoid/conical order and forcing axioms remain.",
        "source_forcing_mapConditions_identity_on_IsName_proved": True,
        "source_forcing_mapConditions_composition_all_raw_names_proved": True,
        "source_forcing_IsName_mapConditions_set_conditions_proved": True,
        "source_forcing_mapConditions_extensional_relation_congruence_proved": True,
        "source_forcing_evaluate_formula_class_total_unique_unfolding_proved": True,
        "source_forcing_evaluate_internal_set_G_formula_class_equivalence_proved": True,
        "source_forcing_evaluate_mapConditions_formula_class_covariance_proved": True,
        "source_forcing_evaluate_covariance_assumes_preimage_is_set": False,
        "interpreted_ZF_full_schema_external_transport_proved": True,
        "interpreted_ZF_transport_domain_nonempty_antecedent_retained": True,
        "interpreted_ZF_transport_background": "translated D-relativization of source Replacement ZF",
        "interpreted_ZF_transport_is_internal_Con_proof": False,
        "native_internal_L_missing_dependency_slice_reused_on_pinned_kernel": True,
        "native_internal_L_arbitrary_model_full_ZF_ZFC_mathematics_reused": True,
        "native_internal_L_relative_all_ZF_ZFC_axiom_schema_original_kernel_certificates": True,
        "native_internal_L_relative_Choice_global_order_and_nonempty_original_kernel_certificates": True,
        "native_internal_L_requires_ambient_object_Choice_standardness_or_external_wellfoundedness": False,
        "native_internal_L_source_Relativization_domain_formula_consumer_connected": True,
        "native_internal_L_source_ZF_full_schemas_Choice_and_Collection_relative_kernels": True,
        "native_internal_L_InterpretedZF_background_and_nonempty_actually_discharged": True,
        "native_internal_L_native_ZF_and_source_native_ZFC_standard_proof_transports": True,
        "original_stage6_background_universe_instance_Derives_gate_complete": True,
        "native_internal_L_all_internal_Proof_Con_transfer_completed": False,
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
        "arithmetic_closed_kernel_certificates_checked": sum(len(names) for names in arithmetic_groups.values()),
        "object_internal_natural_order_total_transitive_antisymmetric_proved": True,
        "object_natural_order_iff_actual_natural_difference_proved": True,
        "object_strict_natural_order_iff_nonzero_difference_proved": True,
        "object_difference_actual_unique_with_only_natural_candidates_proved": True,
        "object_addition_preserves_reflects_both_orders_on_both_sides_proved": True,
        "object_multiplication_weak_monotone_including_zero_proved": True,
        "object_nonzero_multiplier_order_reflection_and_cancellation_proved": True,
        "object_natural_product_empty_iff_factor_empty_proved": True,
        "object_nonzero_natural_iff_at_least_actual_internal_one_proved": True,
        "object_natural_nonzero_product_factor_bounds_proved": True,
        "object_natural_square_lower_strict_monotone_injective_proved": True,
        "object_original_godel_pair_actual_total_unique_omega_value_proved": True,
        "object_original_godel_pair_components_below_output_proved": True,
        "object_original_godel_pair_guarded_square_bands_proved": True,
        "object_original_godel_pair_input_injective_proved": True,
        "object_original_godel_pair_inverse_total_on_all_internal_codes_proved": True,
        "object_original_godel_pair_inverse_by_object_omega_induction_proved": True,
        "object_original_godel_pair_inverse_exact_biconditional_fiber_proved": True,
        "object_original_godel_pair_inverse_actual_unique_bounded_components_proved": True,
        "object_original_raw_structural_node_actual_total_unique_positive_value_proved": True,
        "object_original_raw_structural_node_input_injective_proved": True,
        "object_original_raw_structural_node_strict_component_bounds_proved": True,
        "object_original_raw_structural_node_exact_decode_all_positive_internal_codes_proved": True,
        "object_original_structural_nil_cons_values_and_bounds_proved": True,
        "object_original_structural_nil_exact_internal_one_value_proved": True,
        "object_original_structural_cons_actual_unique_values_and_injectivity_proved": True,
        "object_original_structural_nil_cons_disjoint_proved": True,
        "object_zero_leaf_raw_envelope_at_internal_two_proved": True,
        "object_internal_list_validity_pure_finite_trace_AST_implemented": True,
        "object_internal_list_actual_nil_seed_and_cons_trace_append_proved": True,
        "object_internal_list_actual_prefix_and_valid_tail_decomposition_proved": True,
        "object_internal_list_validity_exact_nil_cons_recursive_iff_proved": True,
        "object_internal_list_cons_reflects_valid_tail_proved": True,
        "object_internal_list_zero_code_rejected_proved": True,
        "object_internal_list_precise_predecessor_length_prefix_graph_exists_proved": True,
        "object_internal_list_known_cons_tail_equals_trace_predecessor_value_proved": True,
        "object_internal_list_unique_lengths_proved": True,
        "object_internal_list_actual_unique_length_fiber_proved": True,
        "object_internal_list_same_code_arbitrary_trace_lengths_equal_proved": True,
        "object_internal_original_cons_head_tail_projections_total_functional_all_internal_sets_proved": True,
        "object_internal_original_cons_head_tail_projection_values_always_in_omega_proved": True,
        "object_internal_original_cons_head_tail_projection_cons_and_nil_equations_proved": True,
        "object_internal_original_cons_head_tail_actual_unique_recursors_and_natural_values_proved": True,
        "object_internal_original_cons_head_tail_iteration_zero_successor_and_range_proved": True,
        "object_internal_projection_two_actual_recursors_coupled_at_all_natural_indices_proved": True,
        "object_internal_projection_actual_iteration_shift_equality_and_iff_proved": True,
        "object_internal_list_cons_tail_actual_iteration_shift_iff_proved": True,
        "object_internal_list_actual_length_tail_iteration_is_nil_proved": True,
        "object_internal_list_actual_tail_iteration_recovers_original_trace_nil_seed_proved": True,
        "object_internal_list_actual_terminal_length_value_pair_exists_and_unique_proved": True,
        "object_internal_list_tail_recursion_aligned_at_all_trace_positions_proved": True,
        "object_internal_list_each_original_domain_point_actual_reverse_natural_index_exists_proved": True,
        "object_internal_list_original_edges_iff_actual_tail_iteration_at_reverse_indices_proved": True,
        "object_internal_original_cons_rows_reverse_to_actual_tail_steps_proved": True,
        "object_internal_projection_actual_iteration_successor_construction_proved": True,
        "object_internal_list_field_reading_actual_total_unique_omega_values_proved": True,
        "object_internal_list_field_reading_original_cons_zero_successor_iff_proved": True,
        "object_internal_list_field_original_Kuratowski_pair_fibers_and_Replacement_exact_image_proved": True,
        "object_internal_list_field_graph_full_functionOn_exact_edges_and_omega_range_proved": True,
        "object_internal_list_valid_codes_actual_unique_length_and_ordered_field_graph_decode_proved": True,
        "object_internal_list_field_reading_matches_original_trace_cons_heads_proved": True,
        "object_internal_list_actual_ordered_field_graphs_proved": True,
        "object_internal_list_unique_lengths_and_actual_field_graphs_proved": True,
        "object_internal_list_arbitrary_field_sequences_inverse_encoding_proved": True,
        "object_internal_list_original_nil_and_cons_at_specified_actual_lengths_proved": True,
        "object_internal_list_all_internal_suffixes_actual_code_exists_proved": True,
        "object_internal_list_encoded_field_graph_recovers_exact_given_sequence_proved": True,
        "object_internal_list_encode_then_decode_recovers_original_length_and_graph_proved": True,
        "object_internal_list_same_length_same_fields_code_injective_proved": True,
        "object_internal_list_decode_then_encode_original_code_recovery_proved": True,
        "object_internal_list_full_encode_decode_round_trip_proved": True,
        "object_internal_list_actual_unique_encoding_fibers_proved": True,
        "object_internal_list_first_terminal_true_tail_execution_total_unique_proved": True,
        "object_internal_list_checker_definition_has_no_Valid_oracle": True,
        "object_internal_list_checker_accepts_iff_original_valid_proved": True,
        "object_internal_list_checker_rejects_iff_not_valid_proved": True,
        "object_internal_list_checker_accepted_codes_actual_decoded_proved": True,
        "object_internal_structural_list_validity_and_decode_proved": True,
        "object_internal_list_domain_field_values_strictly_member_of_list_code_proved": True,
        "object_internal_raw_node_child_fields_strictly_member_of_parent_code_proved": True,
        "object_internal_tree_operator_only_queries_strictly_smaller_children_proved": True,
        "object_internal_tree_operator_child_bounds_equivalent_to_original_marks_proved": True,
        "object_internal_tree_operator_actual_total_and_deterministic_proved": True,
        "object_internal_tree_operator_all_internal_ordinals_actual_unique_recursors_proved": True,
        "object_internal_tree_operator_real_zero_unit_recursors_exist_proved": True,
        "object_internal_tree_accept_reject_recursive_correctness_proved": True,
        "object_internal_structural_tree_validity_and_decode_proved": True,
        "object_internal_tree_actual_successor_domain_evaluation_total_unique_proved": True,
        "object_internal_tree_arbitrary_prefix_graph_edges_iff_actual_values_proved": True,
        "object_internal_tree_validity_independent_of_actual_zero_unit_markers_proved": True,
        "object_internal_tree_validity_exact_recursive_iff_on_all_internal_sets_proved": True,
        "object_internal_tree_actual_unique_tag_payload_length_full_graph_decode_proved": True,
        "object_internal_tree_arbitrary_complete_sequences_actual_unique_node_encoding_proved": True,
        "object_internal_tree_constructed_nodes_valid_iff_all_original_child_fields_valid_proved": True,
        "object_internal_tree_encode_decode_recovers_exact_original_tag_length_and_full_graph_proved": True,
        "object_internal_tree_decode_encode_recovers_exact_original_node_code_proved": True,
        "object_finite_syntax_tag_numerals_actual_exists_unique_ordered_disjoint_proved": True,
        "object_fixed_arity_original_forests_actual_unique_and_exact_numeral_lengths_proved": True,
        "object_fixed_arity_original_syntax_nodes_actual_unique_scalar_injective_proved": True,
        "object_finite_tag_syntax_constructors_actual_unique_disjoint_child_bounds_proved": True,
        "object_bvar_fvar_codes_actual_unique_at_all_internal_natural_indices_proved": True,
        "object_bvar_fvar_code_classes_disjoint_proved": True,
        "object_pure_signature_term_scope_check_proved": True,
        "object_original_syntax_forest_node_constructor_same_code_field_recovery_proved": True,
        "object_original_variable_same_code_unique_internal_index_decode_proved": True,
        "object_internal_term_scope_exact_known_variable_iff_proved": True,
        "object_internal_term_actual_unique_scoped_index_decode_proved": True,
        "object_internal_term_wrong_scope_empty_contexts_scalar_and_wrong_arity_rejected_proved": True,
        "object_internal_term_function_tag_rejected_for_arbitrary_internal_payload_proved": True,
        "object_internal_term_unknown_arbitrary_internal_tag_rejected_proved": True,
        "object_internal_membership_zero_scalar_exact_internal_two_proved": True,
        "object_internal_atomic_same_context_terms_and_known_constructor_iff_proved": True,
        "object_internal_atomic_actual_codes_exist_for_given_legal_inputs_proved": True,
        "object_internal_atomic_unique_field_decode_iff_proved": True,
        "object_internal_atomic_unknown_arbitrary_internal_tag_rejected_proved": True,
        "object_internal_context_history_reads_actual_set_values_proved": True,
        "object_internal_quantifier_reads_real_successor_bound_and_same_free_proved": True,
        "object_seven_logical_constructor_local_state_conditions_proved": True,
        "object_logical_nodes_actual_codes_strict_child_bounds_unique_decode_proved": True,
        "object_internal_context_pair_and_state_actual_power_set_carriers_proved": True,
        "object_internal_all_eleven_local_case_union_proved": True,
        "object_internal_context_type_state_actual_separation_and_unique_fiber_proved": True,
        "object_internal_context_type_state_pair_membership_iff_proved": True,
        "object_internal_context_type_state_operator_total_deterministic_proved": True,
        "object_internal_context_type_actual_unique_recursors_on_all_ordinals_proved": True,
        "object_internal_context_type_actual_unique_state_values_at_all_naturals_proved": True,
        "object_internal_type_state_graph_edges_iff_actual_values_proved": True,
        "object_internal_type_judgment_iff_state_membership_and_history_reads_proved": True,
        "object_internal_all_eleven_history_free_typing_recursive_iff_proved": True,
        "object_internal_typing_universal_law_on_all_internal_codes_and_contexts_proved": True,
        "object_actual_internal_typing_system_with_omega_carriers_and_recursors_exists_proved": True,
        "object_internal_formula_code_actual_carrier_eliminated_proved": True,
        "object_internal_formula_code_omega_independence_proved": True,
        "object_internal_formula_code_carrier_free_all_candidate_recursion_proved": True,
        "object_internal_formula_code_known_all_eleven_constructor_types_proved": True,
        "object_internal_formula_code_arbitrary_unknown_internal_tag_rejected_proved": True,
        "object_original_all_eleven_legal_inputs_actual_unique_typed_code_fibers_proved": True,
        "object_membership_zero_symbol_and_typed_code_actually_constructed_from_terms_proved": True,
        "object_accepted_formula_actual_unique_full_root_fields_proved": True,
        "object_accepted_formula_decoded_root_roundtrip_preserves_type_proved": True,
        "object_original_node_arity_on_arbitrary_internal_length_candidates_proved": True,
        "object_accepted_formula_internal_tag_arity_complete_classification_proved": True,
        "object_nonmatching_decoded_formula_shape_rejected_proved": True,
        "object_finite_numeral_members_classified_on_all_internal_candidates_proved": True,
        "object_original_forests_full_all_internal_index_value_graph_correspondence_proved": True,
        "object_same_root_constructor_shape_full_fields_correspondence_proved": True,
        "object_actual_slots_exact_original_inputs_proved": True,
        "object_arbitrary_pure_formula_schema_checked_field_transfer_proved": True,
        "object_formula_term_successor_symbol_checks_on_decoded_field_graph_proved": True,
        "object_known_constructor_parent_typing_iff_decoded_graph_checks_proved": True,
        "object_formula_code_implies_original_recursive_tree_validity_proved": True,
        "object_pure_terms_imply_original_recursive_tree_validity_proved": True,
        "object_tree_validity_closed_by_original_foundation_separation_membership_induction_proved": True,
        "object_all_internal_formula_contexts_in_tree_validity_property_proved": True,
        "object_formula_code_actual_unique_original_tree_decode_proved": True,
        "object_formula_code_actual_unique_forward_typed_data_decode_proved": True,
        "object_same_root_failed_typed_data_rejection_proved": True,
        "object_typed_data_reverse_recognition_proved": True,
        "object_actual_complete_recursive_typed_data_decode_and_reverse_recognition_proved": True,
        "object_all_eleven_formula_constructors_type_check_proved": True,
        "object_bound_free_context_type_recursion_proved": True,
        "object_internal_term_arbitrary_complete_index_graph_rename_total_unique_proved": True,
        "object_internal_term_rename_exact_actual_variable_edge_iff_proved": True,
        "object_internal_term_rename_actual_diagonal_graph_identity_proved": True,
        "object_arbitrary_parameter_functional_relation_actual_unique_full_graph_proved": True,
        "object_internal_bound_index_graph_quantifier_lift_total_proved": True,
        "object_internal_bound_index_graph_quantifier_lift_all_edge_zero_successor_iff_proved": True,
        "object_internal_bound_index_graph_quantifier_lift_term_compatibility_proved": True,
        "object_internal_bound_index_graph_quantifier_lift_joint_successors_system_proved": True,
        "object_internal_index_maps_actual_unique_natural_code_proved": True,
        "object_internal_index_map_code_actual_unique_graph_decode_proved": True,
        "object_internal_index_map_codes_actual_unique_quantifier_lift_proved": True,
        "object_internal_rename_state_actual_unique_natural_tuple_and_decode_proved": True,
        "object_internal_rename_state_actual_joint_map_code_construction_proved": True,
        "object_internal_formula_rename_state_operator_total_deterministic_proved": True,
        "object_internal_formula_rename_history_actual_state_code_query_proved": True,
        "object_internal_formula_rename_all_eleven_local_matrix_implemented": True,
        "object_internal_formula_rename_state_operator_exact_membership_and_range_proved": True,
        "object_internal_formula_rename_actual_unique_recursors_on_all_ordinals_proved": True,
        "object_internal_formula_rename_actual_unique_state_values_at_all_naturals_proved": True,
        "object_internal_formula_rename_prefix_equation_and_graph_value_iff_proved": True,
        "object_internal_formula_rename_actual_omega_carrier_recursors_system_proved": True,
        "object_internal_formula_rename_judgment_implemented": True,
        "object_internal_formula_rename_judgment_actual_state_membership_iff_proved": True,
        "object_internal_formula_rename_all_internal_prefix_reads_iff_judgment_proved": True,
        "object_internal_formula_rename_history_free_all_eleven_recursive_iff_proved": True,
        "object_internal_formula_rename_all_candidate_type_preservation_proved": True,
        "object_internal_formula_rename_uniform_recursive_law_and_actual_system_proved": True,
        "object_internal_formula_rename_output_fiber_and_six_parameter_induction_contract_implemented": True,
        "object_internal_coded_index_lift_successors_and_output_parameters_unique_proved": True,
        "object_internal_formula_quantifier_judgment_at_given_actual_lift_iff_proved": True,
        "object_internal_formula_rename_known_atomic_tag_filters_all_eleven_branches_proved": True,
        "object_internal_formula_rename_nullary_actual_unique_output_proved": True,
        "object_internal_formula_rename_nullary_all_internal_parameter_property_proved": True,
        "object_internal_formula_rename_membership_and_equality_actual_unique_outputs_proved": True,
        "object_internal_formula_rename_all_candidate_decoded_graphs_align_given_actual_graphs_proved": True,
        "object_internal_formula_rename_all_four_atomic_modes_internal_parameter_property_proved": True,
        "object_internal_formula_rename_all_atomic_inputs_actual_unique_output_proved": True,
        "object_internal_formula_rename_logical_progressive_and_closed_induction_proved": True,
        "object_internal_formula_rename_all_legal_inputs_actual_unique_output_proved": True,
        "object_internal_formula_rename_all_eleven_tags_filter_original_cases_proved": True,
        "object_internal_formula_rename_plain_and_actual_lifted_child_outputs_exist_from_internal_property_proved": True,
        "object_internal_formula_rename_all_seven_logical_modes_actual_unique_output_step_proved": True,
        "object_internal_formula_rename_internal_foundation_separation_induction_closed_proved": True,
        "object_internal_formula_rename_all_candidate_input_iff_exists_and_fiber_proved": True,
        "object_internal_formula_rename_full_single_constructor_exact_laws_proved": True,
        "object_internal_formula_rename_complete_all_eleven_known_source_target_fields_iff_proved": True,
        "object_internal_formula_rename_known_fields_laws_recover_input_without_input_premise_proved": True,
        "object_internal_formula_rename_logical_known_fields_iff_without_decoded_graph_premises_proved": True,
        "object_internal_formula_rename_quantifiers_exact_at_given_actual_coded_lift_proved": True,
        "object_internal_actual_identity_graph_and_natural_map_code_exist_proved": True,
        "object_internal_identity_map_code_diagonal_at_any_actual_decode_proved": True,
        "object_internal_identity_graph_and_code_quantifier_lift_identity_proved": True,
        "object_internal_formula_identity_induction_closed_by_foundation_separation_proved": True,
        "object_internal_formula_rename_identity_proved": True,
        "object_internal_formula_identity_exact_all_candidate_iff_proved": True,
        "object_internal_actual_complete_index_graph_composition_exists_unique_proved": True,
        "object_internal_index_graph_composition_all_candidate_edge_iff_proved": True,
        "object_internal_index_map_composition_actual_unique_natural_code_proved": True,
        "object_internal_coded_composition_recovers_relation_at_any_actual_decode_proved": True,
        "object_internal_coded_composition_exists_iff_exact_composable_inputs_proved": True,
        "object_internal_term_rename_actual_complete_graph_composition_proved": True,
        "object_internal_term_rename_composition_exact_actual_intermediate_code_iff_proved": True,
        "object_internal_binder_lift_compatible_with_actual_composition_proved": True,
        "object_internal_lift_composite_full_graph_recognition_all_candidates_proved": True,
        "object_internal_lift_composite_coded_recognition_all_candidates_proved": True,
        "object_internal_independent_middle_successors_aligned_in_coded_composition_proved": True,
        "object_internal_formula_rename_composition_proved": True,
        "object_internal_formula_rename_identity_and_composition_proved": True,
        "object_internal_known_source_constructor_actual_target_fields_exist_proved": True,
        "object_internal_all_eleven_formula_composition_steps_proved": True,
        "object_internal_fourteen_parameter_formula_composition_induction_closed_proved": True,
        "object_internal_formula_composition_exact_internal_intermediate_code_iff_proved": True,
        "object_internal_free_head_shift_actual_graph_and_code_proved": True,
        "object_internal_free_head_shift_exact_edges_and_fresh_absence_proved": True,
        "object_internal_free_head_shift_zero_source_covered_proved": True,
        "object_internal_free_head_shift_exact_input_iff_proved": True,
        "object_internal_free_head_formula_weakening_unique_total_proved": True,
        "object_internal_free_head_formula_weakening_exact_input_iff_proved": True,
        "object_internal_free_head_formula_weakening_eleven_endpoint_laws_proved": True,
        "object_internal_free_head_formula_weakening_logical_laws_without_code_witnesses_proved": True,
        "object_internal_pure_open_term_fvar_classification_proved": True,
        "object_internal_free_substitution_term_list_index_codec_proved": True,
        "object_internal_free_substitution_term_list_index_unique_fibers_proved": True,
        "object_internal_free_substitution_original_term_fields_exact_correspondence_proved": True,
        "object_internal_original_term_list_formula_free_substitution_unique_total_proved": True,
        "object_internal_original_term_list_formula_free_substitution_exact_input_iff_proved": True,
        "object_internal_original_term_list_formula_free_substitution_eleven_endpoint_laws_proved": True,
        "object_internal_original_term_list_formula_free_substitution_logical_laws_without_external_code_witnesses_proved": True,
        "object_internal_original_term_list_formula_free_substitution_free_term_field_biconditional_proved": True,
        "object_internal_mixed_term_image_substitution_unique_total_proved": True,
        "object_internal_mixed_term_image_substitution_exact_input_iff_proved": True,
        "object_internal_mixed_term_image_known_source_field_iff_proved": True,
        "object_internal_term_image_relation_actual_graph_schema_proved": True,
        "object_internal_term_image_value_rename_actual_unique_graph_proved": True,
        "object_internal_both_term_image_tables_actual_value_rename_proved": True,
        "object_internal_both_term_image_tables_actual_bound_shift_state_proved": True,
        "object_internal_term_image_prefix_actual_unique_graph_proved": True,
        "object_internal_term_image_prefix_zero_successor_exact_fields_proved": True,
        "object_internal_mixed_binder_actual_canonical_head_code_proved": True,
        "object_internal_mixed_term_image_binder_lift_unique_total_proved": True,
        "object_internal_mixed_term_image_binder_lift_exact_input_iff_proved": True,
        "object_internal_mixed_term_image_binder_lift_both_value_categories_shifted_proved": True,
        "object_internal_mixed_term_image_binder_witness_independent_unique_fiber_proved": True,
        "object_internal_mixed_term_image_original_numeric_list_codec_proved": True,
        "object_internal_mixed_term_image_codec_pure_typing_exact_input_fibers_proved": True,
        "object_internal_coded_mixed_term_substitution_unique_total_proved": True,
        "object_internal_coded_mixed_term_substitution_exact_input_fibers_proved": True,
        "object_internal_coded_mixed_term_substitution_original_fields_iff_proved": True,
        "object_internal_coded_mixed_binder_lift_unique_total_proved": True,
        "object_internal_coded_mixed_binder_lift_exact_input_fibers_proved": True,
        "object_internal_coded_mixed_binder_lift_original_fields_iff_proved": True,
        "object_internal_original_free_substitution_term_list_code_preserved_proved": True,
        "object_internal_original_free_substitution_independent_program_specialization_proved": True,
        "object_internal_original_free_weakening_independent_program_specialization_proved": True,
        "object_internal_original_free_variable_programs_exact_domain_typed_unique_fibers_proved": True,
        "object_internal_original_free_weakening_actual_successor_program_state_proved": True,
        "object_internal_free_substitution_binder_same_list_code_stability_proved": True,
        "object_internal_free_substitution_binder_child_program_closure_proved": True,
        "object_internal_strict_lookup_zero_cons_recursion_and_outer_failure_proved": True,
        "object_internal_strict_lookup_all_internal_zero_sink_induction_proved": True,
        "object_internal_strict_lookup_valid_list_exact_success_and_rejection_domain_proved": True,
        "object_internal_strict_lookup_actual_unique_output_fibers_proved": True,
        "object_internal_strict_lookup_original_free_image_field_correspondence_proved": True,
        "strict_lookup_program_direct_field_reference_guard_checked": True,
        "object_internal_lookup_table_code_recursive_operator_actual_graph_and_values_proved": True,
        "object_internal_lookup_table_code_induction_all_runtime_candidates_proved": True,
        "object_internal_lookup_table_program_actual_unique_fixed_code_and_uniform_sentence_proved": True,
        "object_internal_lookup_table_program_success_and_no_output_correspondence_proved": True,
        "object_internal_lookup_table_program_outcome_exhaustive_disjoint_and_unique_proved": True,
        "lookup_table_program_independent_core_reference_guard_checked": True,
        "object_original_Horn_Expr_relational_compilation_all_internal_unique_values_proved": True,
        "object_original_Horn_Expr_occurring_variable_internal_assignment_bounds_proved": True,
        "object_original_Horn_list_node_cons_structural_compilation_correspondence_proved": True,
        "object_original_lookupHead_lookupTail_actual_head_and_premise_compilation_proved": True,
        "object_original_lookupHead_lookupTail_relational_local_matrices_proved": True,
        "original_Horn_relational_compiler_direct_oracle_reference_guard_checked": True,
        "object_original_lookup_full_trace_condition_and_numeric_interface_proved": False,
        "object_original_Horn_all_arity_existential_assignment_intro_elim_proved": True,
        "object_original_Horn_natural_assignment_guard_derived_from_search_bound_proved": True,
        "object_original_Horn_quantified_application_exact_successor_membership_bound_proved": True,
        "object_original_Horn_whole_table_actual_successor_search_equivalence_proved": True,
        "object_original_Horn_full_original_table_nonlookup_branches_rejected_on_tag_zero_proved": True,
        "object_original_Horn_full_original_table_tag_zero_lookup_dispatch_proved": True,
        "object_original_Horn_actual_bounded_search_lookup_dispatch_proved": True,
        "original_Horn_bounded_search_core_direct_oracle_reference_guard_checked": True,
        "object_compiled_original_lookup_quantified_Cons_index_child_extraction_proved": True,
        "object_compiled_original_lookup_arbitrary_internal_closed_trace_soundness_proved": True,
        "object_original_Horn_all_rules_trace_membership_monotonicity_proved": True,
        "object_original_Horn_five_field_head_inversion_proved": True,
        "object_original_variable_expression_actual_code_graph_iff_proved": True,
        "object_original_freeWeaken_arbitrary_internal_trace_soundness_and_completeness_proved": True,
        "object_original_freeWeaken_all_internal_exact_guard_successor_code_iff_proved": True,
        "object_original_freeWeaken_has_output_iff_guard_no_output_iff_invalid_guard_proved": True,
        "object_original_freeWeaken_parameter_depth_input_output_rejection_and_unique_proved": True,
        "object_original_mode_0_3_all_four_variable_relational_trace_values_proved": True,
        "object_original_nil_cons_arity_assignments_eliminated_proved": True,
        "object_original_argument_trace_cases_without_shared_trace_premise_proved": True,
        "object_original_argument_all_internal_whole_run_nil_cons_equation_proved": True,
        "object_original_argument_root_rows_eliminated_from_whole_run_equation_proved": True,
        "object_original_numeric_term_modes_zero_three_bridge_proved": True,
        "object_typed_argument_list_internal_nil_cons_construction_proved": True,
        "object_typed_argument_list_actual_predecessor_head_tail_proved": True,
        "object_typed_argument_list_all_internal_case_equation_proved": True,
        "object_original_numeric_term_typed_actual_unique_output_fibers_proved": True,
        "object_original_numeric_term_all_internal_source_term_promises_proved": True,
        "object_original_numeric_term_program_agreement_discharged_under_actual_environments_proved": True,
        "object_original_argument_typed_code_member_induction_closed_proved": True,
        "object_original_argument_all_internal_typed_list_actual_unique_outputs_proved": True,
        "object_original_argument_actual_output_target_list_exact_length_proved": True,
        "object_original_argument_mode_zero_three_term_promises_discharged_proved": True,
        "object_original_argument_all_internal_index_field_soundness_proved": True,
        "object_original_argument_all_internal_program_field_image_both_directions_proved": True,
        "object_original_argument_field_image_reverse_by_actual_code_injectivity_proved": True,
        "independent_argument_program_field_image_definitions_checked": True,
        "object_original_formula_kind_three_all_eleven_rules_dispatch_proved": True,
        "object_original_formula_application_pure_numeric_structure_iff_proved": True,
        "object_original_formula_all_eleven_local_numeric_matrices_proved": True,
        "object_original_formula_binder_child_actual_successor_depth_proved": True,
        "object_original_formula_selected_real_child_trace_composition_proved": True,
        "object_original_formula_pure_numeric_local_definitions_checked": True,
        "object_original_formula_arity_assignments_eliminated_proved": True,
        "object_original_formula_whole_run_eleven_cases_equation_proved": True,
        "object_original_formula_application_constructor_head_forest_iff_proved": True,
        "object_original_formula_pure_member_zero_symbol_two_argument_forest_iff_proved": True,
        "object_original_formula_pure_member_application_case_exact_iff_proved": True,
        "object_original_argument_finite_forest_typed_list_and_program_fields_iff_proved": True,
        "object_original_argument_pair_actual_output_forest_decomposition_proved": True,
        "object_original_argument_pair_mode_zero_three_all_candidate_program_iff_proved": True,
        "independent_argument_forest_pair_program_definitions_checked": True,
        "object_original_member_formula_pair_agreement_discharged_for_modes_zero_three_proved": True,
        "object_original_member_formula_argument_forest_witnesses_constructed_and_eliminated_proved": True,
        "object_original_member_formula_other_ten_cases_rejected_proved": True,
        "object_original_member_formula_whole_run_all_candidate_term_program_iff_proved": True,
        "independent_member_term_program_definition_checked": True,
        "object_original_member_formula_existing_atom_interface_iff_proved": True,
        "object_original_numeric_term_checked_agreement_discharged_proved": True,
        "object_original_equality_local_case_existing_atom_interface_iff_proved": True,
        "object_original_constants_local_data_existing_atom_interface_iff_proved": True,
        "object_original_application_actual_tag_two_exclusion_proved": True,
        "object_original_equality_whole_run_existing_atom_interface_iff_proved": True,
        "object_original_constants_whole_run_existing_atom_interface_iff_proved": True,
        "object_original_nonbinder_logical_whole_run_dispatch_proved": True,
        "object_original_logical_child_formula_code_types_recovered_proved": True,
        "object_original_nonbinder_logical_history_conditional_iff_proved": True,
        "object_actual_formula_history_read_executed_iff_proved": True,
        "object_original_formula_history_agreement_from_actual_graph_and_object_induction_proved": True,
        "object_original_formula_agreed_history_exists_from_object_induction_proved": True,
        "object_original_nonbinder_logical_history_premise_replaced_by_actual_graph_and_object_induction_proved": True,
        "object_original_actual_free_image_conversion_code_contract_proved": True,
        "object_original_mode_zero_existing_environment_admissible_frame_proved": True,
        "object_original_admissible_frame_atomic_program_iff_proved": True,
        "object_original_admissible_frame_binder_lift_closed_proved": True,
        "object_original_uniform_object_induction_parameters_internalized": True,
        "object_original_uniform_object_induction_prefix_instances_proved": True,
        "object_original_binder_prefix_from_uniform_object_induction_proved": True,
        "object_original_uniform_formula_code_induction_discharged_proved": True,
        "object_original_formula_correctness_scope": "OriginalOperationFrameSyntax.frame mode0/3; bound identity and free-variable image conversion; all internal typed source codes and candidate outputs",
        "object_original_mode_three_free_variable_image_contract_final_checker_applicability_proved": False,
        "object_pure_empty_bound_term_list_free_image_iff_proved": True,
        "object_original_mode_three_free_substitution_whole_formula_typed_lists_proved": True,
        "object_original_mode_three_empty_bound_argument_contract_proved": True,
        "object_original_mode_three_formula_actual_output_and_unique_proved": True,
        "original_mode_three_checker_call_sites_source_audited": True,
        "object_original_pure_syntax_checker_term_list_query_bridge_proved": False,
        "object_pure_syntax_full_fifteen_rule_trace_AST_implemented": True,
        "object_pure_syntax_actual_premiseless_trace_constructed_proved": True,
        "object_pure_syntax_term_query_all_internal_iff_proved": True,
        "object_pure_syntax_trace_insertion_actual_condition_proved": True,
        "object_pure_syntax_two_actual_traces_joined_proved": True,
        "object_pure_syntax_nil_rule_sound_and_complete_proved": True,
        "object_pure_syntax_nil_query_actual_trace_proved": True,
        "object_pure_syntax_cons_local_actual_trace_step_proved": True,
        "object_pure_syntax_cons_query_soundness_induction_proved": True,
        "object_pure_syntax_checker_arguments_query_bridge_proved": True,
        "object_pure_syntax_arguments_query_uniform_IH_discharged": True,
        "object_pure_syntax_empty_bound_argument_query_free_list_iff_proved": True,
        "object_original_mode_three_from_pure_argument_trace_proved": True,
        "object_pure_syntax_formula_constant_rules_sound_and_query_constructed_proved": True,
        "object_pure_syntax_formula_equality_rule_sound_and_query_constructed_proved": True,
        "object_pure_syntax_formula_membership_rule_sound_and_query_constructed_proved": True,
        "object_pure_syntax_all_four_atomic_queries_constructed_proved": True,
        "object_pure_syntax_formula_membership_rule_query_bridge_proved": True,
        "object_pure_syntax_formula_uniform_all_parameters_IH_AST_implemented": True,
        "object_pure_syntax_formula_binary_rules_under_uniform_IH_proved": True,
        "object_pure_syntax_formula_binary_actual_trace_constructed_proved": True,
        "object_pure_syntax_formula_uniform_IH_discharged": True,
        "object_pure_syntax_formula_logical_rule_queries_bridge_proved": True,
        "object_pure_syntax_checker_formula_query_bridge_proved": True,
        "object_pure_syntax_checker_full_typing_query_bridge_proved": True,
        "pure_syntax_definition_guard": pure_syntax_definition,
        "original_mode_three_checker_scope": mode_three_scope,
        "object_original_quantifier_child_step_advanced_iff_from_uniform_induction_proved": True,
        "object_original_quantifier_local_case_actual_history_from_uniform_induction_proved": True,
        "object_original_quantifier_whole_run_dispatch_proved": True,
        "object_original_quantifier_whole_run_actual_history_from_uniform_induction_proved": True,
        "object_formula_transform_full_program_target_type_on_actual_history_proved": True,
        "object_formula_transform_actual_root_guarded_step_equation_proved": True,
        "object_formula_transform_actual_root_execution_program_iff_proved": True,
        "object_original_full_eleven_formula_cases_with_uniform_induction_assembled_proved": True,
        "object_original_formula_actual_history_agreement_discharged_proved": True,
        "object_original_nonbinder_logical_program_cases_proved": True,
        "object_original_all_atomic_formula_program_cases_proved": True,
        "object_original_atomic_internal_source_field_witnesses_eliminated_proved": True,
        "object_original_atomic_compiled_program_all_candidates_iff_proved": True,
        "independent_atomic_subprogram_definitions_checked": True,
        "object_original_argument_typed_list_transform_correctness_on_all_internal_lists_proved": True,
        "object_original_nil_arguments_mode_0_3_guard_discharged_proved": True,
        "object_original_argument_head_and_child_numeric_rows_proved": True,
        "object_original_nil_cons_full_local_matrices_numeric_iff_proved": True,
        "object_original_nil_cons_local_matrices_at_all_candidate_rows_proved": True,
        "object_original_universal_closed_trace_set_actual_separation_proved": True,
        "object_original_whole_table_child_trace_composition_proved": True,
        "object_original_kind2_argument_full_table_dispatch_proved": True,
        "object_original_nil_cons_argument_trace_introduction_proved": True,
        "object_original_argument_trace_all_internal_list_recursion_proved": True,
        "object_original_mode_0_3_pure_signature_typed_term_trace_program_bridge_proved": True,
        "object_original_mode_0_3_checked_term_trace_coded_substitution_iff_proved": True,
        "object_original_identity_shift_converted_term_list_fields_proved": True,
        "original_term_trace_execution_definition_direct_oracle_reference_guard_checked": True,
        "original_freeWeaken_value_and_trace_definition_direct_oracle_reference_guard_checked": True,
        "object_original_freeReplace_arbitrary_internal_trace_soundness_and_completeness_proved": True,
        "object_original_freeReplace_all_internal_success_graph_guard_execution_iff_proved": True,
        "object_original_freeReplace_has_no_output_strict_failure_and_unique_proved": True,
        "original_freeReplace_trace_definition_direct_oracle_reference_guard_checked": True,
        "object_original_Horn_full_table_modes_0_3_variable_exact_dispatch_proved": True,
        "object_original_Horn_variable_actual_search_and_candidate_rejection_dispatch_proved": True,
        "object_original_Horn_bound_modes_0_3_all_internal_trace_identity_iff_and_rejection_proved": True,
        "object_original_Horn_actual_root_insertion_closed_trace_proved": True,
        "object_compiled_original_modes_0_3_variable_positive_trace_branches_proved": True,
        "object_compiled_original_freeReplace_actual_lookup_premise_and_power_trace_proved": True,
        "object_compiled_original_lookup_canonical_Separation_trace_actual_set_and_closure_proved": True,
        "object_compiled_original_full_table_lookup_trace_execution_positive_and_negative_equivalence_proved": True,
        "object_compiled_original_actual_successor_search_trace_equivalence_proved": True,
        "object_compiled_original_lookup_actual_power_omega_trace_domain_equivalence_proved": True,
        "object_compiled_original_lookup_all_internal_success_and_no_output_interface_proved": True,
        "compiled_original_lookup_trace_execution_definitions_reference_guard_checked": True,
        "object_original_free_strengthening_compatibility_proved": False,
        "object_internal_index_code_variable_term_image_conversion_unique_fiber_proved": True,
        "object_internal_index_term_rename_independent_program_correspondence_proved": True,
        "object_internal_index_rename_dual_environment_binder_commutation_proved": True,
        "object_internal_formula_index_rename_all_metadata_induction_closed_proved": True,
        "object_internal_formula_index_rename_independent_program_correspondence_proved": True,
        "object_internal_formula_arbitrary_index_graph_rename_proved": True,
        "object_internal_arbitrary_noninjective_capture_avoiding_substitution_proved": False,
        "object_ZF_context_maps_only_original_axioms": True,
        "object_natural_addition_actual_witness_reassociation_proved": True,
        "object_natural_multiplication_both_distributive_iff_proved": True,
        "object_natural_multiplication_left_successor_iff_proved": True,
        "object_natural_multiplication_commutative_and_associative_proved": True,
        "object_natural_multiplication_internal_successor_of_zero_unit_iff_proved": True,
        "object_relational_natural_semiring_laws_proved": True,
        "object_natural_addition_left_successor_bidirectional_proved": True,
        "object_natural_addition_commutative_associative_and_both_cancellations_proved": True,
        "object_natural_addition_both_addends_bounded_by_sum_proved": True,
        "object_natural_addition_nonzero_addends_give_strict_member_bounds_proved": True,
        "object_natural_sum_empty_iff_both_addends_empty_proved": True,
        "object_natural_semiring_algebra_and_coding_bounds_proved": False,
        "object_full_natural_addition_and_multiplication_proved": False,
        "object_internal_godel_structural_code_correctness_proved": False,
        "dedicated_ZF_U_proof_checker_AST_implemented": False,
        "proof_checker_correctness_on_arbitrary_internal_codes_proved": False,
        "object_Con_theorem_proved": False,
        "trust_level": 0,
        "original_openai_build_rerun_in_this_verification": False,
        "original_openai_baseline_record": source_lock["original_build"],
        "relative_consistency_proved": False,
        "internal_explicit_declaration_audit_coverage_complete": True,
        "internal_explicit_declarations_coverage_checked": len(internal_explicit),
        "object_forcing_condition_rebind_all_internal_total_typed_unique_proved": True,
        "object_forcing_condition_rebind_scope": "Given Omega, successor target bound scope, and an actual source FormulaCode, construct bvar0 head, shift all old bounds, replace designated free condition index, construct both actual image lists, and run existing full mixed substitution; internal scopes and candidates may be nonstandard. Two independent executions have one output. This is an operation for the pinned negative/existential forcing branches, not the full recursive compiler, uniform internal axiom forcing, Proof/Con reduction, or final goal.",
        "object_forcing_literal_guard_code_total_typed_unique_proved": True,
        "object_forcing_actual_negative_branch_rebind_and_bound_guard_inputs_proved": True,
        "object_forcing_literal_guard_scope": "Exact membership/order templates, fixed external R/free parameter count, arbitrary internal target bounds/term/candidates; both guards at an actually constructed bvar0 and actual consumption of child rebind. Not the outer neg/ex constructor, full recursion, uniform internal axiom forcing, Proof/Con reduction or final goal.",
        "audited_declarations": len(footprints),
        "declarations_without_axioms": sum(not value for value in footprints.values()),
        "declarations_with_allowed_axioms": sum(bool(value) for value in footprints.values()),
        "allowed_standard_axioms": sorted(allowed | {"Classical.choice"}),
        "semantic_bridge_choice_origin": "Lean core Fin.lastCases_castSucc; proof-only, not object AC or extracted data",
        "inherited_native_certificate_axioms": sorted(inherited),
        "additional_active_inherited_recursion_certificate_axioms": recursion_lock["native_bool_certificate_axioms"],
        "inherited_recursion_certificate_Bool_operands_natively_rechecked": True,
        "inherited_recursion_certificate_recheck_is_kernel_reduction": False,
        "additional_active_inherited_choice_bridge_certificate_axioms": sorted(inherited_choice),
        "native_choice_bridge_trust_scope": choice_baseline["scope"],
        "native_ZF_seven_certificate_baseline_unchanged": True,
        "standard_axiom_only": False,
        "new_custom_axioms": [],
        "warning_lines": sum("warning:" in line for item in COMMANDS for line in (OUT / item["log"]).read_text(encoding="utf-8").splitlines()),
        "object_internal_mixed_formula_state_uses_pure_mixed_term_lists_proved": True,
        "object_internal_mixed_formula_quantifier_updates_both_numeric_environments_proved": True,
        "object_internal_mixed_formula_concrete_separation_operator_actual_total_unique_proved": True,
        "object_internal_mixed_formula_actual_recursors_and_evaluation_set_unique_proved": True,
        "object_internal_mixed_formula_recursive_iff_on_all_internal_candidates_proved": True,
        "object_internal_mixed_formula_substitution_actual_total_unique_proved": True,
        "object_internal_mixed_formula_actual_exists_unique_fiber_input_iff_proved": True,
        "object_internal_mixed_formula_eleven_constructor_exact_endpoint_laws_proved": True,
        "object_internal_mixed_formula_original_operation_quotation_correspondence_proved": False,
        "object_internal_mixed_formula_InstantiateTop_AbstractFreeTop_proved": False,
        "object_internal_index_graph_to_variable_term_image_actual_unique_proved": True,
        "object_internal_identity_shift_variable_term_tables_actual_unique_proved": True,
        "object_internal_InstantiateTop_complete_environment_tables_actual_unique_proved": True,
        "object_internal_AbstractFreeTop_complete_environment_tables_actual_unique_proved": True,
        "object_internal_top_environment_original_numeric_code_pairs_actual_unique_proved": True,
        "object_internal_top_environment_actual_unique_fiber_input_iff_proved": True,
        "object_internal_top_environment_scoped_original_list_field_laws_proved": True,
        "object_internal_top_environment_instantiated_mixed_formula_actual_fibers_proved": True,
        'object_internal_top_formula_environment_witnesses_internalized_proved': True,
        'object_internal_top_formula_actual_total_unique_output_proved': True,
        'object_internal_top_formula_exists_and_unique_fiber_input_iff_proved': True,
        'object_internal_top_formula_all_eleven_constructor_endpoints_proved': True,
        'object_internal_top_formula_quantifiers_actual_dual_lift_proved': True,
        'pure_signature_embedding_preserves_original_eleven_constructor_encoding': True,
        'pure_original_tree_substitution_AST_commutation_proved': True,
        'object_original_tree_quotation_schema_actual_total_unique_proved': True,
        'object_pure_syntax_quotation_schema_actual_total_unique_proved': True,
        'object_original_quotation_forest_constructor_field_biconditionals_proved': True,
        'object_original_quotation_scalar_variable_correspondence_proved': True,
        'object_pure_quotation_Term_FormulaCode_scope_proved': True,
        'object_pure_quotation_typed_actual_unique_fibers_proved': True,
        'object_original_quotation_forest_internal_length_and_field_read_proved': True,
        'object_term_image_quotation_actual_environment_unique_fiber_proved': True,
        'object_mixed_term_external_quotation_correspondence_proved': True,
        'object_term_weakenBound_external_quotation_correspondence_proved': True,
        'object_external_term_image_quotation_full_field_extensionality_proved': True,
        'object_external_term_image_lifted_binder_quotation_correspondence_proved': True,
        'object_external_term_image_lifted_binder_joint_unique_fiber_proved': True,
        'object_external_native_substitution_image_environment_binder_alignment_proved': True,
        'object_external_native_formula_substitution_full11_quotation_correspondence_proved': True,
        'object_external_native_formula_substitution_typed_joint_unique_fiber_proved': True,
        'object_external_top_coded_environments_native_substitution_quotation_proved': True,
        'object_external_top_operations_original_numeric_quotation_correspondence_proved': True,
        'object_external_top_operations_typed_joint_unique_fibers_proved': True,
        "object_internal_top_formula_operation_original_numeric_quotation_proved": False,
        "object_fixed_pure_term_program_independent_compiled_control_flow_proved": True,
        "object_fixed_pure_term_program_all_internal_checked_equivalence_proved": True,
        "object_fixed_pure_term_program_exact_domain_and_typed_unique_output_proved": True,
        "object_fixed_pure_term_program_actual_unique_code_uniform_sentence_proved": True,
        "object_fixed_pure_formula_program_independent_compiled_eleven_branches_proved": True,
        "object_fixed_pure_formula_program_actual_internal_recursors_and_evaluation_proved": True,
        "object_fixed_pure_formula_program_all_internal_execution_equivalence_proved": True,
        "object_fixed_pure_formula_program_exact_domain_and_typed_unique_output_proved": True,
        "object_fixed_pure_formula_program_actual_unique_code_uniform_sentence_proved": True,
        "object_internal_formula_independent_program_uniform_correctness_proved": True,
        "object_internal_arbitrary_program_interpreter_correctness_proved": False,
        "independent_formula_program_core_reference_guard_checked": True,
        "independent_formula_program_core_modules_checked": ['FormulaAtomicProgramSyntax', 'FormulaTransformHistorySyntax', 'FormulaTransformAtomSyntax', 'FormulaTransformLogicalSyntax', 'FormulaTransformProgramSyntax', 'FormulaTransformOperatorSyntax', 'FormulaTransformRecursionSyntax', 'FormulaTransformEvaluationSyntax', 'FormulaTransformExecutionSyntax'],
        "object_pure_syntax_unary_three_rules_actual_applications_proved": True,
        "object_pure_syntax_quantifier_bound_successor_internalized_proved": True,
        "object_pure_syntax_unary_complete_queries_under_uniform_IH_proved": True,
        "object_pure_syntax_expr_queries_type_iff_proved": True,
        "object_original_substitution_shape_pure_syntax_queries_proved": True,
        "object_original_substitution_shape_mode_three_query_under_pure_guards_proved": True,
        "object_original_substitution_shape_syntax_transform_bundle_iff_proved": True,
        "object_original_substitution_shape_full_local_checker_proved": False,
        "pure_proof_query_definition_guard": pure_proof_query_definition,
        "object_raw_pairing_component_projection_total_unique_proved": True,
        "object_raw_node_positive_and_zero_decode_domain_proved": True,
        "object_raw_head_tail_arbitrary_tag_exact_iff_proved": True,
        "object_raw_head_tail_actual_natural_recursors_proved": True,
        "object_raw_get_all_internal_indices_actual_unique_proved": True,
        "object_raw_get_zero_successor_index_equations_proved": True,
        "object_raw_get_zero_input_all_internal_indices_proved": True,
        "object_original_projection_full_seven_rule_trace_bridge_proved": True,
        "object_original_projection_proof_node_queries_proved": False,
        "raw_projection_definition_guard": raw_projection_definition,
        "object_raw_field_payload_get_composition_AST_implemented": True,
        "object_raw_field_all_internal_indices_actual_unique_proved": True,
        "object_raw_field_zero_input_all_internal_indices_iff_proved": True,
        "object_raw_field_finite_constructor_slot_iff_schema_proved": True,
        "raw_field_definition_guard": raw_field_definition,
        "projection_trace_definition_guard": projection_trace_definition,
        "projection_rule_partition_guard": projection_rule_partition,
        "object_original_projection_tag_all_internal_iff_proved": True,
        "object_original_projection_query_natural_domains_proved": True,
        "object_original_projection_rule_outer_dispatch_proved": True,
        "object_original_projection_get_all_internal_iff_proved": True,
        "object_original_projection_get_object_IH_discharged": True,
        "object_original_projection_field_all_internal_iff_proved": True,
        "object_original_projection_numeric_quotation_correspondence_proved": False,
        "pure_substitution_node_definition_guard": pure_substitution_node_definition,
        "pure_mp_node_definition_guard": pure_mp_node_definition,
        "pure_strengthening_node_definition_guard": pure_strengthening_node_definition,
        "original_mode_one_scalar_definition_guard": original_mode_one_scalar_definition,
        "mode_one_variable_numeric_values_guard": mode_one_variable_numeric_values,
        "small_mode_arguments_and_pure_term_values_guard": small_mode_arguments_and_pure_term_values,
        "actual_abstract_pure_term_operation_guard": actual_abstract_pure_term_operation,
        "actual_abstract_argument_operation_guard": actual_abstract_argument_operation,
        "actual_abstract_frame_guard": actual_abstract_frame,
        "actual_abstract_frame_programs_guard": actual_abstract_frame_programs,
        "small_mode_formula_and_abstract_atomic_programs_guard": small_mode_formula_and_abstract_atomic_programs,
        "mode_one_full_formula_correctness_guard": mode_one_full_formula_correctness,
        "actual_top_formula_and_forall_node_guard": actual_top_formula_and_forall_node,
        "mode_two_variables_and_frame_terms_guard": mode_two_variables_and_frame_terms,
        "mode_two_actual_root_guard": mode_two_actual_root,
        "mode_two_actual_binder_guard": mode_two_actual_binder,
        "mode_two_full_formula_guard": mode_two_full_formula,
        "logical_instantiation_nodes_guard": logical_instantiation_nodes,
        "static_logical_nodes_guard": static_logical_nodes,
        "abstract_logical_nodes_and_exact_table_guard": abstract_logical_nodes_and_exact_table,
        "base_proof_nodes_and_parameterized_six_table_guard": base_proof_nodes_and_parameterized_six_table,
        "proof_tree_checked_trace_equation_guard": proof_tree_checked_trace_equation,
        "proof_tree_root_closed_fields_guard": proof_tree_root_closed_fields,
        "proof_tree_six_node_equation_guard": proof_tree_six_node_equation,
        "proof_tree_internal_induction_guard": proof_tree_internal_induction,
        "proof_tree_equation_unique_guard": proof_tree_equation_unique,
        "fixed_axiom_partial_test_guard": fixed_axiom_partial_test,
        "all_internal_forall_closure_guard": all_internal_forall_closure,
        "three_schema_index_system_guard": three_schema_index_system,
        "Project_atomic_compile_guard": Project_atomic_compile,
        "Project_source_recursive_grammar_guard": Project_source_recursive_grammar,
        "Project_actual_compiler_guard": Project_actual_compiler,
        "Project_compiler_recursive_equation_guard": Project_compiler_recursive_equation,
        "Project_compiler_output_typing_guard": Project_compiler_output_typing,
        "Project_compiler_source_completeness_guard": Project_compiler_source_completeness,
        "Project_compiler_scalar_uniqueness_guard": Project_compiler_scalar_uniqueness,
        "Project_compiler_source_validity_guard": Project_compiler_source_validity,




























        'object_Horn_explicit_table_internal_closed_trace_value_constructed': True,



        'object_full_varint_internal_program_proved': False,

        'object_Project_compiler_source_validation_member_IH_Foundation_discharged': True,
        'object_Project_structural_compiler_exact_source_acceptance_proved': True,
        'object_Project_structural_compiler_exact_typed_unique_acceptance_proved': True,

        'object_Project_compiler_scalar_output_functionality_proved': True,
        'object_Project_compiler_scalar_IH_Foundation_discharged': True,
        'object_Project_compiler_actual_output_implies_source_code_proved': True,

        'object_Project_compiler_all_source_inputs_actual_output_exists_proved': True,
        'object_Project_compiler_all_source_inputs_have_actual_typed_output_proved': True,
        'object_Project_compiler_source_completeness_member_IH_Foundation_discharged': True,

        'object_Project_compiler_all_actual_outputs_target_typed_proved': True,
        'object_Project_compiler_output_typing_member_IH_Foundation_discharged': True,

        'object_Project_compiler_actual_child_query_migration_proved': True,
        'object_Project_compiler_all_internal_recursive_equation_proved': True,
        'object_Project_compiler_recursive_history_carrier_witnesses_eliminated': True,

        'object_Project_compiler_actual_set_recursion_constructed_proved': True,
        'object_Project_compiler_produced_output_actual_parent_certificate_proved': True,
        'object_Project_compiler_constants_and_atomic_execution_proved': True,
        'object_Project_compiler_all_source_inputs_output_typed_unique_proved': True,
        'object_Project_source_twelve_constructor_recursive_code_equation_proved': True,
        'object_Project_source_actual_carriers_and_recursors_object_eliminated': True,
        'object_Project_bound_term_internal_shift_proved': True,
        'object_Project_subset_internal_expansion_typed_unique_proved': True,
        'object_Project_three_atomic_internal_compile_proved': True,
        'object_Project_all_twelve_constructor_internal_compile_proved': True,
        'object_three_schema_index_complete_graphs_proved': True,
        'object_three_schema_index_actual_list_codes_proved': True,
        'object_three_schema_index_uniform_formula_renaming_proved': True,
        'object_all_internal_unary_node_iteration_proved': True,
        'object_all_internal_parameter_forall_closure_typed_proved': True,
        'object_all_internal_forall_closure_closed_unique_output_proved': True,
        'object_original_Project_schema_numeric_test_proved': False,

        'object_fixed_axiom_packet_arithmetic_proved': True,
        'object_fixed_7_ZF_plus_3_target_partial_test_exact_proved': True,
        'object_fixed_axiom_test_witnesses_object_eliminated': True,
        'object_actual_schema_shell_and_all_internal_count_closure_output_exists_unique': True,
        'object_schema_shell_exact_native_quotation_for_every_original_matrix': True,
        'object_original_schema_raw_body_actual_compilation_and_three_renaming_sites_proved': True,
        'object_original_schema_raw_body_to_shell_and_all_internal_closure_output_exists': True,
        'object_original_forall_closure_all_internal_scope_type_preservation_proved': True,
        'object_original_forall_closure_actual_closed_typed_unique_fiber_proved': True,
        'object_original_schema_exact_finite_core_type_all_internal_counts_proved': True,
        'object_original_schema_full_output_type_from_raw_body_proved': True,
        'object_original_schema_full_output_unique_integration_proved': True,
        'object_original_schema_full_output_type_unique_integration_proved': True,
        'object_original_schema_scope_chain_witness_independence_proved': True,
        'object_original_structural_axiom_certificate_tree_row_interface_proved': True,
        'object_original_structural_schema_certificate_output_exists_typed_unique_proved': True,
        'object_original_fixed_structural_certificate_tags_and_Choice_rejection_proved': True,
        'object_original_Project_compiler_exact_native_quotation_schema_original_kernel_proved': True,
        'object_original_Project_compiler_quotation_body_depth_indices_external': True,
        'object_original_Project_compiler_quotation_uniform_nonstandard_body_claimed': False,
        'object_original_whole_forall_closure_exact_native_quotation_schema_original_kernel_proved': True,
        'object_original_whole_forall_closure_quotation_count_body_indices_external': True,
        'object_original_whole_forall_closure_quotation_uniform_nonstandard_count_claimed': False,
        'object_original_finite_schema_templates_and_whole_closure_exact_native_quotation_schema_original_kernel_proved': True,
        'object_original_schema_template_quotation_actual_renamed_matrix_parents_retained': True,
        'object_original_schema_template_quotation_uniform_nonstandard_body_count_claimed': False,
        'object_original_three_schema_graphs_exact_native_embedding_values_proved': True,
        'object_actual_index_to_term_conversion_native_quotation_environment_identification_proved': True,
        'object_actual_pure_index_renaming_native_formula_quotation_schema_original_kernel_proved': True,
        'object_pure_index_renaming_quotation_body_context_map_indices_external': True,
        'object_actual_Project_schema_compiled_matrix_quotation_discharge_complete': True,
        'original_Project_fo_formula_native_bound_renaming_commutation_all_constructors_proved': True,
        'object_original_raw_schema_pipeline_exact_native_Separation_Collection_quotation_original_kernel_proved': True,
        'object_original_raw_schema_pipeline_intermediate_quotation_parents_discharged': True,
        'object_original_raw_schema_quotation_body_count_indices_external': True,
        'object_original_raw_schema_quotation_uniform_nonstandard_axiom_forcing_claimed': False,
        'object_pure_index_renaming_quotation_uniform_nonstandard_body_claimed': False,
        'object_full_Separation_Collection_axiom_test_proved': False,

        'object_original_proof_tree_all_object_code_recursive_equation_unique_proved': True,
        'object_original_proof_tree_canonical_Node_formula_satisfies_equation_proved': True,
        'object_original_proof_tree_equation_solution_natural_range_proved': True,
        'object_original_proof_tree_dedicated_Bool_Proof_equation_proved': False,

        'object_original_proof_tree_internal_Foundation_induction_schema_proved': True,
        'object_original_proof_tree_internal_member_IH_discharged': True,
        'object_original_proof_tree_conditional_root_property_and_rejection_proved': True,
        'object_original_proof_tree_dedicated_Proof_local_closure_proved': False,

        'object_original_proof_tree_six_node_recursive_equation_proved': True,
        'object_original_proof_tree_node_tag0_local_table_iff_proved': True,
        'object_original_proof_tree_payload_fields_strictly_below_code_proved': True,

        'object_original_proof_tree_root_closedness_exact_conclusion_iff_proved': True,
        'object_original_proof_tree_root_actual_strict_guard_zero_proved': True,
        'object_original_proof_tree_all_twelve_root_tag_separation_proved': True,

        'object_original_proof_tree_twelve_branch_checked_trace_AST_implemented': True,
        'object_original_proof_tree_all_trace_roots_Separation_and_closure_proved': True,
        'object_original_proof_tree_full_internal_closed_trace_equation_proved': True,
        'object_original_proof_tree_twelve_branch_bounds_and_positive_composition_proved': True,
        'object_original_proof_tree_node_root_entry_recursive_equations_proved': True,
        'object_original_proof_tree_rank_induction_root_closedness_and_full_checker_correctness_proved': False,

        'object_original_logical_proof_node_full_pure_relation_proved': True,
        'object_original_theory_proof_node_object_formula_parameter_interface_proved': True,
        'object_original_six_rule_pure_local_table_with_axiom_formula_parameter_proved': True,
        'object_original_six_rule_exact_local_table_independent_specification_iff_proved': True,
        'object_original_six_rule_numeric_quotation_Bool_checker_correspondence_proved': False,

        'object_original_logical_21_24_full_pure_relational_nodes_proved': True,
        'object_original_all_27_logical_full_pure_relational_nodes_proved': True,
        'object_original_all_27_exact_Shape_query_table_pure_relation_proved': True,
        'object_original_all_27_exact_table_independent_specification_iff_proved': True,
        'object_original_all_27_numeric_quotation_Bool_checker_correspondence_proved': False,

        'object_original_logical_0_to_19_22_26_full_pure_relational_nodes_proved': True,
        'object_original_static_logical_exact_query_list_interpretation_proved': True,
        'object_original_static_logical_all_assignment_bounds_proved': True,
        'object_original_static_logical_all_numeric_nested_heads_proved': True,
        'object_original_static_logical_numeric_quotation_Bool_checker_correspondence_proved': False,

        'object_original_logical_20_23_25_full_pure_relational_nodes_proved': True,
        'object_original_logical_20_23_25_exact_queries_proved': True,
        'object_original_logical_20_23_25_all_assignment_bounds_proved': True,
        'object_original_logical_20_23_25_numeric_nested_heads_proved': True,
        'object_original_logical_20_23_25_numeric_quotation_Bool_checker_correspondence_proved': False,

        "object_original_mode_two_typed_argument_program_proved": True,
        "object_original_mode_two_full_formula_run_proved": True,
        "object_original_mode_two_actual_InstantiateTop_proved": True,
        "object_original_mode_two_actual_top_code_witnesses_discharged": True,
        "object_original_mode_two_actual_binder_frame_proved": True,
        "object_original_mode_two_actual_root_frame_proved": True,
        "object_original_mode_two_closed_parameter_binder_rename_identity_proved": True,
        "object_original_mode_two_actual_root_typed_terms_proved": True,
        "object_original_mode_two_variable_numeric_value_iff_proved": True,
        "object_original_mode_two_whole_variable_run_iff_proved": True,
        "object_original_mode_two_frame_typed_term_program_iff_proved": True,
        "object_original_mode_two_frame_root_and_binder_proved": True,
        "object_original_mode_two_full_formula_operation_proved": True,
        "object_original_small_mode_complete_formula_Run3_equations_proved": True,
        "object_original_mode_one_complete_atomic_whole_run_program_proved": True,
        "object_original_mode_one_atomic_term_and_pair_agreements_discharged": True,
        "object_original_mode_one_atomic_source_field_witnesses_discharged": True,

        "object_original_mode_one_arbitrary_depth_frame_term_program_iff_proved": True,
        "object_original_mode_one_arbitrary_depth_frame_coded_term_iff_proved": True,
        "object_original_mode_one_arbitrary_depth_frame_term_promise_discharged": True,
        "object_original_mode_one_arbitrary_depth_frame_argument_map_proved": True,

        "object_original_mode_one_arbitrary_internal_depth_variable_binder_covariance_proved": True,
        "object_original_mode_one_actual_abstract_root_frame_proved": True,
        "object_original_mode_one_actual_binder_frame_eight_witnesses_discharged": True,

        "object_original_small_mode_typed_argument_fiber_and_field_map_proved": True,
        "object_original_mode_one_zero_depth_actual_abstract_argument_map_proved": True,
        "object_original_mode_one_zero_depth_argument_Promise_and_IH_discharged": True,
        "object_original_mode_one_zero_depth_argument_code_witnesses_discharged": True,
        "object_original_mode_one_zero_depth_guarded_argument_actual_operation_proved": True,

        "object_original_mode_one_numeric_variable_specializations_proved": True,
        "object_original_mode_one_zero_depth_actual_abstract_table_agreement_proved": True,
        "object_original_mode_one_zero_depth_actual_abstract_pure_term_program_proved": True,
        "object_original_mode_one_zero_depth_pure_term_actual_abstract_operation_proved": True,
        "object_original_mode_one_zero_depth_pure_term_code_witnesses_discharged": True,
        "object_original_mode_one_binder_lifted_abstract_frame_proved": True,
        "object_original_small_mode_argument_nil_guard_proved": True,
        "object_original_small_mode_argument_whole_run_equations_proved": True,
        "object_original_mode_one_pure_term_guarded_numeric_iff_proved": True,
        "object_original_mode_one_pure_term_typed_numeric_iff_proved": True,
        "object_original_mode_one_abstract_environment_argument_map_proved": True,
        "object_original_mode_one_variable_numeric_output_iff_proved": True,
        "object_original_mode_one_whole_variable_numeric_run_iff_proved": True,
        "object_original_mode_one_variable_root_witness_discharged": True,
        "object_original_mode_one_variable_output_naturality_derived": True,
        "object_original_mode_one_term_five_rule_dispatch_proved": True,
        "object_original_mode_one_variable_two_rule_whole_trace_unfold_proved": True,
        "object_original_mode_one_scalar_numeric_guards_proved": True,
        "object_original_mode_one_four_variable_positive_traces_proved": True,
        "object_original_mode_one_full_formula_run_proved": True,
        "object_original_forall_full_pure_relational_node_proved": True,
        "object_original_forall_exact_four_queries_pure_correspondence_proved": True,
        "object_original_forall_all_four_assignment_bounds_proved": True,
        "object_original_forall_nested_head_normalization_proved": True,
        "object_original_mode_one_actual_top_formula_operation_proved": True,
        "object_original_forall_shape_numeric_quotation_checker_correspondence_proved": False,
        "object_original_mode_zero_full_formula_run_weakening_proved": True,
        "object_original_strengthening_exact_four_queries_pure_correspondence_proved": True,
        "object_original_strengthening_successor_witness_discharged": True,
        "object_original_strengthening_all_four_assignment_bounds_proved": True,
        "object_original_strengthening_full_pure_relational_node_proved": True,
        "object_original_strengthening_shape_numeric_quotation_checker_correspondence_proved": False,
        "object_original_mp_exact_six_queries_pure_correspondence_proved": True,
        "object_original_mp_composite_implication_projection_proved": True,
        "object_original_mp_all_five_assignment_bounds_proved": True,
        "object_original_mp_full_pure_relational_node_proved": True,
        "object_original_mp_shape_numeric_quotation_checker_correspondence_proved": False,
        "object_original_substitution_shape_projection_queries_proved": True,
        "object_original_substitution_shape_all_five_queries_iff_proved": True,
        "object_raw_get_bound_object_IH_discharged": True,
        "object_raw_field_all_internal_numeric_bound_proved": True,
        "object_original_substitution_shape_all_six_assignment_bounds_proved": True,
        "object_original_substitution_shape_pure_relational_node_iff_proved": True,
        "object_original_substitution_shape_numeric_quotation_checker_correspondence_proved": False,

        "object_original_seven_projection_rule_trace_AST_implemented": True,
        "object_original_seven_projection_rule_positive_closure_proved": True,
        "object_original_projection_trace_all_root_unfold_proved": True,
        "object_original_projection_rule_assignment_bound_discharged": True,

        "pure_syntax_full_typing_scope": "Independent full15 pure Horn term/list/formula query ASTs are equivalent to the corresponding types on all internal candidates under Omega; formula object IH is discharged with original ZF SetInduction. Original extended-signature/numeric quotation and final-checker applicability remain unproved.",
        "scope": "Original substitution, MP and strengthening nodes, small-mode argument Run2 equations and pure mode1 numeric terms remain proved. Mode1 at empty depth now agrees with actual AbstractFreeTop code tables, the independent term program and coded mixed term substitution on all valid pure terms; actual code-table witnesses are constructed and eliminated and the type guard is inside the conclusion. The zero-depth actual argument-list program map is now proved for arbitrary internal lengths, with list IH, term Promise and both code-table witnesses discharged and source type inside the conclusion. An independent compatible frame now covers arbitrary internal depths and actual typed tables; the real top environment supplies the root, actual original binder lifting preserves it, and old variable/field plus all eight lifting witnesses are discharged. Arbitrary-depth compatible frames now prove original term Run1 versus actual term program/coded substitution, typed unique outputs and their internal Promise, and list Run2 versus actual field maps with Promise/list IH discharged and source guards inside final conclusions. Every fixed mode below four now has the original whole Run3 versus the unchanged eleven-outcomes unfold equation, and actual mode1 compatible frames give complete four-atomic program correctness without assumed term/pair agreement or source-field witnesses. Full recursive mode1 formula correctness is now proved for every internal typed code under the actual arbitrary-depth compatible frame, with all ten changing frame/output parameters object-quantified. Real binder lifting uses independent source/target successors. Original ZF SetInduction discharges the formula IH and actual history witnesses. The actual AbstractFreeTop environment supplies the root frame. Actual mode1 top formula operation is now proved with both actual code tables eliminated and source type inside the final conclusion. The original Hilbert forall local pure relational node is now proved with the original four queries, both successor witnesses eliminated, all four assignment bounds derived, and the nested node3/node9 head normalized by actual numeric constructors. Genuine mode2 now has exact original scalar/variable dispatch and numeric value correctness on all internal variable inputs and candidate outputs, with whole Run1 root row witnesses and output naturality discharged. Under an explicit closed-parameter/typed-table/compatible-variable frame, all valid pure terms agree with the independent term program and coded mixed substitution. Mode2 actual zero-depth root frame is now derived from the real instantiateCoded tables, with parameter/depth naturality and variable compatibility discharged. Its typed/guarded term Run1 agrees with the independent program and coded mixed substitution. Closed parameters are proved invariant under the real binder bound-shift/free-identity renaming. Actual mode2 binder frame closure is now proved with independent source/target successors aligned by object uniqueness. All scoped old bound indices split below/at the depth point, and closed-parameter rename identity handles the point while P remains unchanged. Old variable/field values and both four-witness lifting blocks are internally eliminated. Mode2 term fibers and arbitrary internal argument-list programs are now proved with term Promise and list IH discharged. Full recursive typed Num2 formulas cover all eleven constructors; an object ALL10 correctness predicate varies every frame/output parameter, and original ZF SetInduction discharges the formula IH. Actual internal history witnesses and the real binder lifting are used. The existing empty-bound-target InstantiateTop operation is now proved, with both actual code tables constructed and eliminated and source type inside the final conclusion. This does not prove shared original quotation/checker applicability, remaining proof/theory nodes, internal Proof/compiler/interpretation or final Con. Shared quotation/Bool for these nodes, remaining logical/theory shapes, internal Proof/compiler/interpretation and final Con remain unproved.",
        "original_pure_signature_term_bridge_scope": "Original modes0/3 checked term traces with internal depth/parameter metadata correspond to the independent term program and coded mixed term substitution for every internal input/output. Actual identity/shift/converted-list hypotheses are explicit; input legality is inside the checked formula. Pure signature terms have only bound/free variable branches. This is not original parameter-list/formula mode0/3 correctness, extended-language quotation elimination, rule checking, arbitrary ProofZF/U correctness, or the final internal Con theorem.",
        "original_universal_argument_trace_scope": "Separation constructs the actual set V of natural rows with an original internal closed trace. Every closed subtrace embeds in V, V is closed for the full original table, and on natural rows Trace is equivalent to originalStep at V. All actual 28 rules compose their child traces with natural bounded assignments and exact head/guards. Kind2 rows dispatch exactly to original nilArguments/consArguments; their positive trace introductions are proved. This is not exact nil/cons output equations, arbitrary internal list recursion, complete formula transformation, extended-language quotation elimination, generic internally encoded rule interpretation, ProofZF/U correctness, or final Con.",
        "original_argument_numeric_matrix_scope": "Original nil/cons heads and both cons premises correspond to actual numeric kind1/kind2 five-field rows. Internal Num0/Num3 discharges the original nil mode<4 guard. At a given original kind2 candidate row and natural actual assignment, nil/cons full local matrices are equivalent to exact input/output Nil/Cons structure and real child traces, without preassuming candidate structure. This does not yet eliminate original arity assignment blocks, construct all root rows, prove full raw argument-run equations or arbitrary internal list induction; formula/checker/Proof/Con gates remain unproved.",
        "original_argument_whole_run_equation_scope": "Original nil/cons arity=3/7 object assignment blocks are eliminated in both directions. Exact original metadata equalities align all three parameters; four cons components are internally existentially quantified, and their naturality follows from actual child runs. Original whole-table relational Trace at any original kind2 row is exactly Nil/Nil or the cons case, without a shared-trace premise. Actual root construction eliminates the given row and preassumed input/output naturality: under Omega, Num0/3 and natural depth/parameter, Run2 is equivalent to those outcomes for every internal input/output. This is an exact recursive equation, not yet all-internal typed-list transformation correctness/totality/uniqueness, original extended-language quotation equivalence, full formulas, rules/Proof checker or Con.",
        "footprints": footprints,
        "sha256": {str(path.relative_to(ROOT)).replace("\\", "/"): source_sha256(path) for path in hashed},
    }
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    print(f"PASS: {len(footprints)} audited declarations; "
          f"{summary['declarations_without_axioms']} without axioms; "
          f"{summary['declarations_with_allowed_axioms']} with recorded dependencies; "
          f"{summary['warning_lines']} warning lines; inherited native certificate axioms recorded.")


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-check-only", action="store_true",
                        help="Check source/dependency guards without a Lean build or axiom audit")
    args = parser.parse_args()
    main(source_check_only=args.source_check_only)

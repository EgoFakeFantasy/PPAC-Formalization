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


def check_mode_three_scope() -> dict:
    """Audit pinned finite call sites; this does not prove internal checker applicability."""
    inventory = json.loads((ROOT / "docs/MODE3_CHECKER_SCOPE.json").read_text(encoding="utf-8"))
    base = ROOT / ".lake/packages/YesMetaZFC"
    text = {}
    for name, expected_hash in inventory["files"].items():
        path = base / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected_hash:
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


def check_Packet_affine_arithmetic() -> dict:
    modules = ['PacketAffineSyntax', 'PacketAffineTransport', 'PacketAffineCore', 'PacketAffineZero', 'PacketAffineFiber', 'PacketAffineStep', 'PacketAffineRecursive', 'PacketAffineRuleData', 'PacketAffineLiteralSyntax', 'PacketAffineLiteral', 'ObjectPacketAffine']
    schemas = ['packetAffineExistsUnique', 'packetAffineOutputsUnique', 'packetAffineZeroIff', 'packetAffineAdvance', 'packetAffineRecursiveIff', 'packetAffineAllInternalRecursiveLaw', 'packetAffineAllInternalFibers', 'packetAffineLiteralSystemExists', 'packetAffineLiteralFramesUnique', 'packetAffineZeroBelowLiteralBase', 'packetAffineTwoBelowLiteralBase', 'packetAffineRejectDigit', 'packetAffineRejectTail', 'packetAffineRejectOutput']
    required = {'PacketAffineSyntax': ['def affine', 'Formula.mem B w', 'Formula.mem d B', 'Formula.mem t w', 'Formula.mem n w', 'NaturalMultiplicationSyntax.product', 'NaturalAdditionSyntax.sum', 'def criterion'], 'PacketAffineCore': ['theorem exists_value', 'theorem equation_unique', 'theorem unique', 'mul_exists', 'add_exists'], 'PacketAffineStep': ['theorem advance', 'theorem retreat', 'mul_succ_backward', 'mul_succ_forward'], 'PacketAffineRecursive': ['theorem recursive_iff', 'theorem all_law', 'OriginalUniversalBlock.allMany 3', 'OmegaStructureInduction.decomposition', 'PacketAffineZero.zero_iff'], 'PacketAffineRuleData': ['rulesFor ObjectPacket.rules (relation wide) = [baseRule wide,stepRule wide]', 'if wide then 256 else 128', 'ObjectPacket.Expr.addConst (radix wide) (.var 2)'], 'PacketAffineLiteralSyntax': ['def frame', 'def totalLaw', 'def system', 'def existsSystem'], 'PacketAffineLiteral': ['theorem exists_system', 'SyntaxNumerals.exists_numeral', 'PacketAffineRecursive.all_law', 'theorem all_fibers'], 'ObjectPacketAffine': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b', text):
            raise RuntimeError('Packet affine forbidden gap: '+mod)
        texts[mod] = text
        for clause in required.get(mod, []):
            if clause not in text: raise RuntimeError('Packet affine proof drift: '+mod+': '+clause)
    for mod,name,expected in [('PacketAffineLiteral','exists_system',{'hw'}),('PacketAffineRecursive','all_law',{'hw','hB'}),('PacketAffineLiteral','all_fibers',{'hw','hB'})]:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Packet affine hidden premise: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketAffine.native_'+name not in check:
            raise RuntimeError('Missing Packet affine native fixture: '+name)
    return {'all_internal_affine_existence_and_unique_output':True,
            'all_internal_zero_successor_and_recursive_equation':True,
            'actual_128_256_literal_system_witnesses_object_existentially_eliminated':True,
            'original_four_affine_rule_metadata_exact':True,
            'invalid_digit_tail_output_candidates_explicitly_rejected':True,
            'original_Horn_condition_affine_correspondence':False,
            'full_NatPacket_byte_tree_bridge':False,
            'varint_inverse_quotient_digit_totality':False,
            'full_Proof_and_Con':False}


def check_Packet_original_affine_local_matrices() -> dict:
    modules = ['HornExprAddConst', 'PacketHornAffineSyntax', 'PacketHornAffineExpr', 'PacketHornAffineMatrix', 'PacketHornAffineLocal', 'PacketHornAffineLawSyntax', 'PacketHornAffineLaws', 'ObjectPacketHornAffine']
    schemas = ['packetOriginalAddConstGraphIff', 'packetOriginalRadixAddConstGraphIff', 'packetOriginalAffineBaseHeadIff', 'packetOriginalAffineStepHeadIff', 'packetOriginalAffineBaseGuardIff', 'packetOriginalAffineStepPremiseIff', 'packetOriginalAffineBaseMatrixAtIff', 'packetOriginalAffineStepMatrixAtIff', 'packetOriginalAffineBaseMatrixIff', 'packetOriginalAffineStepMatrixIff', 'packetOriginalAffineAllInternalBaseMatrixLaw', 'packetOriginalAffineAllInternalStepMatrixLaw', 'packetOriginalAffineLiteralMatrixSystemExists']
    required = {'HornExprAddConst': ['ObjectPacket.Expr.addConst', 'theorem backward', 'theorem forward', 'theorem graph_iff', 'HornExprUnique.unique', 'NaturalRecursionLaws.evaluation_zero', 'add_succ_forward'], 'PacketHornAffineSyntax': ['def row', 'def entry', 'def base', 'def stepBody', 'NaturalAdditionSyntax.sum', 'def step', 'theorem intro_step'], 'PacketHornAffineExpr': ['theorem actual_base_head', 'theorem actual_step_head', 'ObjectPacket.Expr.addConst', 'HornExprConstructor.constructor_iff', 'HornExprAddConst.backward', 'HornRuleValue.guard_at', 'FormulaCodeCongruence.ex_congr', 'theorem step_premise_iff'], 'PacketHornAffineMatrix': ['theorem base_at', 'theorem step_at', 'HornRuleSyntax.matrix (baseRule wide)', 'HornRuleSyntax.matrix (stepRule wide)', 'PacketHornAffineExpr.base_guard_iff', 'PacketHornAffineExpr.step_premise_iff'], 'PacketHornAffineLocal': ['theorem base_iff', 'theorem step_iff', 'SyntaxNumerals.exists_numeral hZ 0', 'OriginalBinderStepSyntax.successor_exists', 'ZFArithmetic.add_exists', 'HornBinderRules.eliminate_many 2', 'PacketHornAffineMatrix.step_at'], 'PacketHornAffineLawSyntax': ['OriginalUniversalBlock.allMany 3', 'OriginalUniversalBlock.allMany 5', 'def existsSystem', 'PacketAffineLiteralSyntax.frame'], 'PacketHornAffineLaws': ['theorem base_law', 'theorem step_law', 'theorem exists_system', 'SyntaxNumerals.exists_numeral', 'PacketHornAffineLocal.base_iff', 'PacketHornAffineLocal.step_iff'], 'ObjectPacketHornAffine': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(r'Expr\.eval|addConst_eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b', text):
            raise RuntimeError('Packet original affine matrix forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Packet original affine matrix proof drift: '+mod+': '+clause)
    signatures = [('HornExprAddConst','graph_iff',{'hw','hn','hx','hB'}),('PacketHornAffineLocal','base_iff',{'hw','hn','hB'}),('PacketHornAffineLocal','step_iff',{'hw','hn','hB'}),('PacketHornAffineLaws','base_law',{'hw','hB'}),('PacketHornAffineLaws','step_law',{'hw','hB'}),('PacketHornAffineLaws','exists_system',{'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Packet original affine matrix hidden premise: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketHornAffine.native_'+name not in check:
            raise RuntimeError('Missing original Packet affine native fixture: '+name)
    return {'original_addConst_graph_iff_internal_addition':True,
            'actual_four_affine_heads_guard_premise_complete_matrices':True,
            'auxiliary_zero_successor_and_sum_witnesses_object_discharged':True,
            'all_internal_natural_assignments_and_arbitrary_rows_and_traces':True,
            'final_ALL3_base_and_ALL5_step_laws':True,
            'literal_radix_local_matrix_system_exists_under_only_omega':True,
            'original_condition_iff_affine_relation':False,
            'whole_NatPacket_byte_tree_bridge':False,
            'full_Proof_and_Con':False}


def check_Packet_affine_bounded_applications() -> dict:
    modules = ['PacketAffineApplicationBounds', 'PacketAffineApplicationSyntax', 'PacketAffineApplicationNatural', 'PacketAffineApplication', 'HornApplicationRange', 'PacketAffineApplicationLawSyntax', 'PacketAffineApplicationLaws', 'ObjectPacketAffineApplication']
    schemas = ['packetAffineBaseHeadSearchBound', 'packetAffineBaseMatrixSuppliesBoundedApplication', 'packetAffineStepHeadSearchBound', 'packetAffineStepMatrixSuppliesBoundedApplication', 'packetAffineRowAssignmentsNatural', 'packetAffineEntryAssignmentsNatural', 'packetAffineBaseDigitNatural', 'packetAffineStepAssignmentsNatural', 'packetAffineWholeBaseApplicationIff', 'packetAffineWholeStepApplicationIff', 'packetAllInternalAffineApplicationsLaw', 'packetAffineLiteralApplicationSystemExists', 'originalRuleApplicationRowNatural', 'originalRuleRejectNonNaturalRow']
    required = {'PacketAffineApplicationBounds': ['theorem base_variables', 'theorem step_variables', 'ObjectPacket.Expr.addConst_variables', 'variable_bound hZ (baseRule wide).head', 'variable_bound hZ (stepRule wide).head', 'HornApplicationRules.intro_application'], 'PacketAffineApplicationSyntax': ['def baseOutcome', 'def stepOutcomeBody', 'def stepOutcome', 'existsMany 3', 'theorem intro_base', 'theorem intro_step'], 'PacketAffineApplicationNatural': ['theorem row_environment', 'theorem entry_environment', 'theorem base_digit', 'theorem step_environment', 'SyntaxNodeInjective.constructor_range', 'SyntaxConstructors.child_member', 'StructuralListTraceOrder.member_member'], 'PacketAffineApplication': ['HornApplicationRules.eliminate_application (baseRule wide)', 'HornApplicationRules.eliminate_application (stepRule wide)', 'PacketAffineApplicationBounds.base_intro', 'PacketAffineApplicationBounds.step_intro', 'PacketAffineApplicationNatural.base_digit', 'PacketAffineApplicationNatural.step_environment', 'theorem base_iff', 'theorem step_iff', 'HornBinderRules.eliminate_many 3'], 'HornApplicationRange': ['theorem range', 'theorem reject', 'HornExprRange.range', 'HornApplicationRules.eliminate_application rule'], 'PacketAffineApplicationLawSyntax': ['OriginalUniversalBlock.allMany 2', 'def existsSystem', 'PacketAffineLiteralSyntax.frame', 'HornApplicationSyntax.application (baseRule wide)', 'HornApplicationSyntax.application (stepRule wide)'], 'PacketAffineApplicationLaws': ['theorem all_law', 'theorem exists_system', 'SyntaxNumerals.exists_numeral', 'PacketAffineApplication.base_iff', 'PacketAffineApplication.step_iff'], 'ObjectPacketAffineApplication': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(r'Expr\.eval|addConst_eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b', text):
            raise RuntimeError('Packet affine bounded application forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Packet affine bounded application proof drift: '+mod+': '+clause)
    signatures = [('PacketAffineApplicationBounds','base_bound',{'hw','hn','hh'}),('PacketAffineApplicationBounds','step_bound',{'hw','hn','hh'}),('PacketAffineApplication','base_iff',{'hw','hB'}),('PacketAffineApplication','step_iff',{'hw','hB'}),('PacketAffineApplicationNatural','step_environment',{'hw','hs'}),('PacketAffineApplicationLaws','all_law',{'hw','hB'}),('PacketAffineApplicationLaws','exists_system',{'hw'}),('HornApplicationRange','range',{'hw','ha'}),('HornApplicationRange','reject',{'hw','hr'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Packet affine bounded application hidden premise: '+mod+'.'+name)
    outcome = texts['PacketAffineApplicationSyntax'].split('theorem baseOutcome_rename')[0]
    if 'environmentNat' in outcome or 'environmentBound' in outcome:
        raise RuntimeError('Structural outcomes must derive naturality and bounds, not assume them')
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketAffineApplication.native_'+name not in check:
            raise RuntimeError('Missing Packet affine bounded application native fixture: '+name)
    return {'original_head_contains_all_arity_1_3_parameters':True,
            'original_search_bounds_derived_from_actual_head_graph':True,
            'full_original_arity_1_3_blocks_eliminated_both_directions':True,
            'outcome_naturality_derived_from_actual_structural_rows_and_entries':True,
            'exact_base_and_step_application_iff_for_all_internal_rows_traces':True,
            'no_row_naturality_or_assignment_bound_oracle_in_final_iff':True,
            'ALL2_both_application_laws_and_only_omega_literal_system':True,
            'any_fixed_original_rule_rejects_non_natural_row':True,
            'whole_Packet_condition_iff_affine_and_byte_tree_bridge':False,
            'full_Proof_and_Con':False}


def check_Packet_explicit_table_closed_trace() -> dict:
    modules = ['HornClosedTraceSyntax', 'HornClosedTraceExtension', 'PacketTraceSyntax', 'PacketAffineDispatchData', 'HornClosedTraceValueSyntax', 'HornClosedTraceValue', 'HornClosedTraceValueClosed', 'PacketAffineDispatch', 'HornClosedTraceSystemSyntax', 'HornClosedTraceProperties', 'PacketTraceCore', 'ObjectPacketClosedTrace']
    schemas = ['closedTraceMemberHasActualStep', 'closedTraceInsertPreservesClosure', 'closedTraceInsertAcceptsActualRoot', 'closedTraceAcceptedRootSetExists', 'closedTraceAcceptedRootMembershipIff', 'closedTraceContainsEveryInternalSubtrace', 'closedTraceAcceptedRootSetClosed', 'closedTraceAllCandidateUnfoldIff', 'closedTraceAllCandidateSystemExists', 'closedTraceRejectNonNaturalRoot', 'packetActualTenRuleAcceptedRootSetExists', 'packetActualTenRuleAcceptedRootSetClosed', 'packetActualTenRuleConditionUnfoldIff', 'packetActualTenRuleTraceSystemExists', 'packetAffineForeignRuleRejected', 'packetAffineActualTenRuleDispatch', 'packetAffineActualTenRuleStepIffOutcomes', 'packetAffineConditionIffActualOutcomes', 'packetAffineBaseConditionAccepted', 'packetAffineSuccessorConditionAccepted']
    required = {'HornClosedTraceSyntax': ['def closed', 'def witness', 'def condition', 'HornStepSyntax.step rules', 'theorem closed_at', 'theorem step_row_subst'], 'HornClosedTraceExtension': ['HornTraceMonotone.step rules', 'HornClosedTraceSyntax.step_row_subst rules', 'InsertExistence.exists_insert', 'theorem condition'], 'PacketTraceSyntax': ['HornStepSyntax.step ObjectPacket.rules', 'HornClosedTraceSyntax.closed ObjectPacket.rules', 'HornClosedTraceSyntax.witness ObjectPacket.rules', 'HornClosedTraceSyntax.condition ObjectPacket.rules'], 'PacketAffineDispatchData': ['def others', 'ObjectPacket.rules.drop 4', 'theorem others_classified', 'theorem rule_cases', 'theorem base_member', 'theorem step_member'], 'HornClosedTraceValueSyntax': ['def matrix (rules : List Rule)', 'MinimalPredicates.separated (matrix rules)', 'HornClosedTraceSyntax.condition rules', 'theorem value_at'], 'HornClosedTraceValue': ['ZFContext.separation hZ (HornClosedTraceValueSyntax.matrix rules)', 'theorem exists_value', 'theorem subtrace_included', 'theorem member_iff'], 'HornClosedTraceValueClosed': ['HornTraceMonotone.step rules', 'HornClosedTraceValue.subtrace_included rules', 'theorem closed', 'HornClosedTraceExtension.condition rules'], 'PacketAffineDispatch': ['HornNodeDisjoint.node_contradiction', 'PacketAffineDispatchData.rule_cases', 'HornStepSyntax.step_elim ObjectPacket.rules', 'theorem step_iff_applications', 'theorem step_iff_outcomes'], 'HornClosedTraceSystemSyntax': ['def allLaw', 'def existsSystem', 'HornClosedTraceValueSyntax.value rules', 'HornClosedTraceSyntax.closed rules'], 'HornClosedTraceProperties': ['theorem step_natural', 'HornApplicationRange.range', 'theorem reject_non_natural', 'theorem unfold_iff', 'theorem all_unfold', 'theorem exists_system', 'HornClosedTraceValue.exists_value rules hZ w'], 'PacketTraceCore': ['HornClosedTraceValueSyntax.value ObjectPacket.rules', 'theorem affine_condition_iff_outcomes', 'theorem base_accept', 'theorem step_accept', 'PacketAffineApplication.base_backward', 'PacketAffineApplication.step_backward', 'PacketAffineDispatch.step_iff_outcomes', 'PacketAffineDispatchData.base_member', 'PacketAffineDispatchData.step_member'], 'ObjectPacketClosedTrace': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|addConst_eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b|HornLookupConditionSyntax|HornLookupSoundSyntax|HornUniversalTraceSyntax|HornStepSyntax\.originalStep|ObjectSyntaxTransform\.rules'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden, text):
            raise RuntimeError('Packet explicit-table trace forbidden gap or wrong table: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Packet explicit-table trace proof drift: '+mod+': '+clause)
    signatures = [('HornClosedTraceValue','exists_value',set()),('HornClosedTraceValueClosed','condition_step',{'hv','ht'}),('HornClosedTraceProperties','unfold_iff',{'hw','hv'}),('HornClosedTraceProperties','exists_system',{'hw'}),('PacketAffineDispatch','dispatch',{'hw','hc','hs'}),('PacketAffineDispatch','step_iff_applications',{'hw','hc'}),('PacketAffineDispatch','step_iff_outcomes',{'hw','hB','hc'}),('PacketTraceCore','affine_condition_iff_outcomes',{'hw','hB','hv','hr'}),('PacketTraceCore','base_accept',{'hw','hB','hb'}),('PacketTraceCore','step_accept',{'hw','hB','hq','hc','hs','hn','hr'}),('PacketTraceCore','exists_system',{'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Packet explicit-table trace hidden premise: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketClosedTrace.native_'+name not in check:
            raise RuntimeError('Missing Packet explicit-table trace native fixture: '+name)
    return {'fixed_rule_table_explicit_in_generic_closed_trace_and_value':True,
            'Packet_uses_actual_original_ten_rules':True,
            'original_Separation_constructs_all_internal_accepted_roots':True,
            'every_internal_subtrace_included_and_universal_value_closed':True,
            'all_candidate_roots_unfold_without_root_naturality_premise':True,
            'only_omega_premise_for_actual_internal_uniform_trace_system':True,
            'all_eight_foreign_affine_branches_object_rejected':True,
            'actual_ten_rule_affine_dispatch_to_exact_prior_application_outcomes':True,
            'base_and_successor_acceptance_eliminate_universal_trace_witness':True,
            'original_Basic_AST_condition_translation':False,
            'full_condition_iff_affine_arithmetic_and_byte_tree_bridge':False,
            'full_Proof_and_Con':False}


def check_Packet_relational_affine_arithmetic() -> dict:
    modules = ['PacketAffineRootTransport', 'PacketAffineRootSyntax', 'PacketAffineRootBase', 'PacketAffineRootStep', 'PacketAffineRootEquation', 'PacketAffineInductionSyntax', 'PacketAffineInductionEntry', 'PacketAffineInductionPredecessor', 'PacketAffineInductionPoint', 'PacketAffineInduction', 'PacketAffineAcceptedSyntax', 'PacketAffineAccepted', 'PacketAffineAcceptedProperties', 'ObjectPacketAffineArithmetic']
    schemas = ['packetAffineRootBaseFieldsIff', 'packetAffineRootStepFieldsIff', 'packetAffineExactRootStepEquation', 'packetAffineExactRootMemberEquation', 'packetAffineInternalEntryFromIH', 'packetAffineInternalEntryConstructedFromIH', 'packetAffineZeroPointMembershipIff', 'packetAffineSuccessorPointMembershipIff', 'packetAffineAllInternalTailIHDischarged', 'packetAffineAllInternalRootMembershipIff', 'packetAffineConditionExactArithmeticIff', 'packetAffineAcceptedExactArithmeticIff', 'packetAffineAllInternalAcceptedExactArithmetic', 'packetAffineAllInternalRootExactArithmetic', 'packetAffineActualLiteralExactArithmeticSystemExists', 'packetAffineAcceptedOutputExists', 'packetAffineAcceptedOutputsUnique', 'packetAffineAcceptedRejectDigit', 'packetAffineAcceptedRejectTail', 'packetAffineAcceptedRejectOutput']
    required = {'PacketAffineRootTransport': ['Derives.eqSubst', 'theorem row_output', 'theorem entry_digit', 'theorem entry_tail'], 'PacketAffineRootSyntax': ['def zeroCase', 'def predecessorBody', 'PacketHornAffineSyntax.entry', 'def criterion'], 'PacketAffineRootBase': ['theorem actual_witness', 'existsMany 2', 'SyntaxNodeInjective.constructor_input_eq', 'theorem base_iff'], 'PacketAffineRootStep': ['theorem actual_witness', 'existsMany 5', 'SyntaxNodeInjective.constructor_input_eq', 'PacketAffineRootTransport.entry_digit', 'theorem step_iff'], 'PacketAffineRootEquation': ['PacketAffineDispatch.step_iff_outcomes', 'PacketTraceCore.unfold_iff', 'theorem member_iff'], 'PacketAffineInductionSyntax': ['def propertyBody', 'def correct', 'def matrix', 'OriginalUniversalBlock.allMany 3', 'PacketAffineSyntax.affine', 'theorem at_correct'], 'PacketAffineInductionEntry': ['theorem entry_to_affine', 'theorem affine_to_entry', 'SyntaxConstructors.exists_constructor', 'PacketTraceCore.intro_entry'], 'PacketAffineInductionPredecessor': ['StructuralListCodeLength.predecessor_unique', 'PacketAffineRootTransport.entry_tail', 'PacketAffineInductionEntry.entry_to_affine', 'PacketAffineInductionEntry.affine_to_entry', 'PacketAffineStep.advance', 'PacketAffineStep.retreat'], 'PacketAffineInductionPoint': ['theorem no_empty_predecessor', 'theorem zero', 'theorem successor', 'OmegaStructureAlgebra.successor_not_empty'], 'PacketAffineInduction': ['theorem all_correct', 'ZFArithmetic.induction hZ (matrix wide)', 'theorem membership_iff', 'base hZ wide w B V', 'step hZ wide w B V'], 'PacketAffineAcceptedSyntax': ['def accepted', 'PacketHornAffineSyntax.row', 'PacketTraceSyntax.condition', 'OriginalUniversalBlock.allMany 3', 'OriginalUniversalBlock.allMany 4', 'def existsSystem'], 'PacketAffineAccepted': ['theorem condition_iff', 'theorem accepted_iff', 'PacketTraceCore.exists_value hZ w', 'theorem all_law', 'theorem all_root_law', 'theorem exists_system', 'SyntaxNumerals.exists_numeral'], 'PacketAffineAcceptedProperties': ['theorem exists_value', 'theorem unique', 'theorem reject_digit', 'theorem reject_tail', 'theorem reject_output', 'PacketAffineCore.exists_value', 'PacketAffineCore.unique'], 'ObjectPacketAffineArithmetic': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|addConst_eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b|HornLookupConditionSyntax|HornStepSyntax\.originalStep|ObjectSyntaxTransform\.rules'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden, text) or re.search(r'(?m)^\s+induction\b', text):
            raise RuntimeError('Packet affine arithmetic forbidden gap, wrong table or host induction: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Packet affine arithmetic proof drift: '+mod+': '+clause)
    signatures = [('PacketAffineRootBase','base_iff',{'hw','hr'}),('PacketAffineRootStep','step_iff',{'hw','hr'}),('PacketAffineInduction','all_correct',{'hw','hB','hv'}),('PacketAffineInduction','membership_iff',{'hw','hB','hv','hr'}),('PacketAffineAccepted','condition_iff',{'hw','hB','hr'}),('PacketAffineAccepted','accepted_iff',{'hw','hB'}),('PacketAffineAccepted','all_law',{'hw','hB'}),('PacketAffineAccepted','all_root_law',{'hw','hB'}),('PacketAffineAccepted','exists_system',{'hw'}),('PacketAffineAcceptedProperties','exists_value',{'hw','hB','hd','ht'}),('PacketAffineAcceptedProperties','unique',{'hw','hB','hn','ha'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Packet affine arithmetic hidden premise: '+mod+'.'+name)
    accepted = texts['PacketAffineAcceptedSyntax'].split('def lawBody')[0]
    if 'PacketAffineSyntax.affine' in accepted or 'condition' not in accepted or 'PacketHornAffineSyntax.row' not in accepted:
        raise RuntimeError('Actual accepted relation must not be defined by the arithmetic answer')
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketAffineArithmetic.native_'+name not in check:
            raise RuntimeError('Missing Packet affine arithmetic native fixture: '+name)
    return {'exact_original_root_fields_aligned_by_object_constructor_injectivity':True,
            'original_base_EX2_and_step_EX5_witnesses_object_eliminated':True,
            'original_object_omega_induction_discharges_all_internal_tail_IH':True,
            'independent_actual_relational_acceptance_iff_guarded_product_plus_sum':True,
            'all_internal_digit_tail_output_candidates_retained_in_ALL3':True,
            'exact_root_condition_iff_arithmetic_ALL4':True,
            'universal_trace_and_root_witnesses_object_discharged':True,
            'only_omega_premise_for_actual_literal_arithmetic_system':True,
            'actual_relational_affine_output_total_unique_and_invalid_candidates_rejected':True,
            'original_Basic_AST_condition_translation':False,
            'full_NatPacket_byte_tree_bridge':False,
            'full_Proof_and_Con':False}


def check_Packet_internal_radix_division() -> dict:
    modules = ['PacketDivisionSyntax', 'PacketDivisionTransitions', 'PacketDivisionStep', 'PacketDivisionInduction', 'PacketDivisionBand', 'PacketDivisionUnique', 'PacketDivisionValueSyntax', 'PacketDivisionValue', 'ObjectPacketDivision']
    schemas = ['packetDivisionIncrement', 'packetDivisionCarry', 'packetDivisionSuccessorExists', 'packetDivisionAllNaturalOutputs', 'packetDivisionDecompositionExists', 'packetDivisionLowerBand', 'packetDivisionUpperBand', 'packetDivisionQuotientUnique', 'packetDivisionRemainderUnique', 'packetDivisionPairUnique', 'packetDivisionExactDomain', 'packetDivisionQuantifiedPairUnique', 'packetDivisionUniqueFiberExists', 'packetDivisionUniqueFiberExactDomain', 'packetDivisionAcceptedInverseExists', 'packetDivisionAcceptedInverseExactDomain', 'packetDivisionAcceptedInverseUnique', 'packetDivisionAllInternalUniqueFibers', 'packetDivisionAllInternalAcceptedInverse', 'packetDivisionActualLiteralSystemExists']
    required = {'PacketDivisionSyntax': ['def decompositionBody', 'existsMany 2', 'PacketAffineSyntax.affine', 'def matrix'], 'PacketDivisionTransitions': ['theorem increment', 'theorem carry', 'add_succ_backward', 'mul_succ_backward'], 'PacketDivisionStep': ['theorem from_affine', 'GodelPairArithmetic.successor_below', 'carry_exists', 'PacketDivisionTransitions.increment', 'theorem from_decomposition'], 'PacketDivisionInduction': ['theorem zero_point', 'theorem base', 'theorem step', 'ZFArithmetic.induction hZ PacketDivisionSyntax.matrix', 'theorem all_decomposes', 'theorem exists_decomposition'], 'PacketDivisionBand': ['theorem sum_at_product', 'theorem lower', 'theorem upper', 'NaturalAdditionBounds.lower_bound', 'NaturalAdditionMonotone.strict_monotone'], 'PacketDivisionUnique': ['theorem quotient_not_less', 'PacketDivisionBand.upper', 'PacketDivisionBand.lower', 'NaturalMultiplicationOrderLaws.left_monotone', 'NaturalOrderBasic.transitive', 'NaturalOrderBasic.below_not_reverse', 'NaturalAdditionCancellation.cancel_right', 'theorem unique'], 'PacketDivisionValueSyntax': ['def uniquePair', 'OriginalUniversalBlock.allMany 2', 'def fiberBody', 'def fiber', 'def acceptedBody', 'PacketAffineAcceptedSyntax.accepted', 'def allLaw', 'def allAcceptedLaw', 'def existsSystem'], 'PacketDivisionValue': ['theorem unique_pair', 'PacketDivisionUnique.unique', 'theorem exists_fiber', 'theorem fiber_iff', 'theorem accepted_exists', 'theorem accepted_iff', 'theorem accepted_unique', 'PacketAffineAccepted.accepted_iff', 'theorem exists_system', 'SyntaxNumerals.exists_numeral'], 'ObjectPacketDivision': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden, text) or re.search(r'(?m)^\s+induction\b', text):
            raise RuntimeError('Internal radix division forbidden gap or host induction: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Internal radix division proof drift: '+mod+': '+clause)
    signatures = [('PacketDivisionInduction', 'all_decomposes', {'hB', 'hw'}), ('PacketDivisionUnique', 'unique', {'hb', 'ha', 'hw'}), ('PacketDivisionValue', 'fiber_iff', {'hB', 'hw'}), ('PacketDivisionValue', 'accepted_iff', {'hB', 'hw'}), ('PacketDivisionValue', 'accepted_unique', {'hb', 'ha', 'hB', 'hw'}), ('PacketDivisionValue', 'exists_system', {'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Internal radix division hidden premise: '+mod+'.'+name)
    accepted = texts['PacketDivisionValueSyntax'].split('def acceptedBody')[1].split('def acceptedDecomposition')[0]
    if 'PacketAffineSyntax.affine' in accepted or 'PacketAffineAcceptedSyntax.accepted' not in accepted:
        raise RuntimeError('Inverse accepted fiber must reference the independently defined actual relation')
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketDivision.native_'+name not in check:
            raise RuntimeError('Missing internal radix division native fixture: '+name)
    return {'internal_output_existence_by_original_object_omega_induction':True,
            'both_increment_and_actual_radix_carry_object_proved':True,
            'distinct_quotient_bands_object_disjoint':True,
            'quotient_and_remainder_jointly_unique_by_order_and_cancellation':True,
            'quantified_unique_inverse_fiber_and_exact_omega_domain':True,
            'independent_actual_relational_Packet_inverse_exists_unique':True,
            'all_internal_and_invalid_output_candidates_retained':True,
            'actual_128_256_system_exists_under_only_omega':True,
            'original_Basic_AST_condition_translation':False,
            'full_varint_Proof_and_Con':False}


def check_Packet_quotient_descent_and_induction() -> dict:
    modules = ['PacketDivisionDescentOrder', 'PacketDivisionDescentCore', 'PacketQuotientInductionSyntax', 'PacketQuotientInduction', 'PacketDivisionDescentSyntax', 'PacketDivisionDescentAccepted', 'ObjectPacketDescent']
    schemas = ['packetDescentOneProduct', 'packetDescentProductBounds', 'packetDescentQuotientBounds', 'packetDescentQuotientBelow', 'packetDescentNonzeroOutputStrict', 'packetDescentTerminalDigit', 'packetDescentExactStoppingThreshold', 'packetDescentZeroOutputExactFields', 'packetDescentLargeOutputNonzero', 'packetDescentQuotientInductionPoint', 'packetDescentQuotientInductionProgressive', 'packetDescentAllInternalQuotientInduction', 'packetDescentAffineProperties', 'packetDescentAffineTerminalRecursiveBranches', 'packetDescentAcceptedProperties', 'packetDescentAllInternalAcceptedLaw', 'packetDescentActualLiteralSystemExists']
    required = {'PacketDivisionDescentOrder': ['theorem one_product', 'SyntaxNumeralSyntax.eliminate_succ 0', 'NaturalMultiplicationAlgebraLaws.right_unit', 'NaturalMultiplicationMonotone.monotone', 'NaturalMultiplicationMonotone.strict_monotone', 'SyntaxNumerals.exists_numeral hZ 1'], 'PacketDivisionDescentCore': ['theorem quotient_bounds', 'PacketDivisionBand.lower', 'NaturalOrderBasic.transitive', 'theorem quotient_strict', 'theorem terminal_iff', 'PacketDivisionUnique.unique', 'PacketAffineZero.zero_iff', 'theorem zero_output'], 'PacketQuotientInductionSyntax': ['def base', 'def stepBody', 'def step', 'OriginalUniversalBlock.allMany 3', 'pred p', 'BoundedInduction.below', 'theorem below_at'], 'PacketQuotientInduction': ['theorem large_nonempty', 'theorem point', 'PacketDivisionInduction.exists_decomposition', 'PacketDivisionDescentCore.quotient_strict', 'theorem progressive', 'theorem all_holds', 'BoundedInduction.induction_on_set p ρ w', 'ZFContext.separation hZ p.neg', '(ZFContext.arithmetic hZ).base.foundation'], 'PacketDivisionDescentSyntax': ['def properties', 'def branch', 'def lawBody', 'PacketAffineAcceptedSyntax.accepted', 'OriginalUniversalBlock.allMany 3', 'PacketDivisionValueSyntax.system', 'def existsSystem'], 'PacketDivisionDescentAccepted': ['theorem affine_properties', 'theorem affine_branch', 'theorem accepted_properties', 'PacketAffineAccepted.accepted_iff', 'theorem all_law', 'theorem exists_system', 'SyntaxNumerals.exists_numeral'], 'ObjectPacketDescent': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden, text) or re.search(r'(?m)^\s+induction\b', text):
            raise RuntimeError('Quotient descent forbidden gap or host induction: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Quotient descent proof drift: '+mod+': '+clause)
    signatures = [('PacketDivisionDescentCore', 'quotient_bounds', {'hB', 'hw', 'ha'}), ('PacketDivisionDescentCore', 'quotient_strict', {'hB', 'hw', 'hn', 'ha'}), ('PacketDivisionDescentCore', 'terminal_iff', {'hw', 'ha'}), ('PacketQuotientInduction', 'all_holds', {'hB', 'hs', 'hw', 'hb'}), ('PacketDivisionDescentAccepted', 'accepted_properties', {'hB', 'hw', 'ha'}), ('PacketDivisionDescentAccepted', 'all_law', {'hB', 'hw'}), ('PacketDivisionDescentAccepted', 'exists_system', {'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Quotient descent hidden premise: '+mod+'.'+name)
    if '(p : Formula (k+1))' not in texts['PacketQuotientInduction'] or '(ρ : Fin k → Fin m)' not in texts['PacketQuotientInduction']:
        raise RuntimeError('Quotient induction must retain arbitrary object matrices and parameters')
    law = texts['PacketDivisionDescentSyntax'].split('def lawBody')[1].split('def allLaw')[0]
    if 'PacketAffineAcceptedSyntax.accepted' not in law or 'PacketAffineSyntax.affine' in law:
        raise RuntimeError('Descent law must use actual independent relational Packet acceptance')
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketDescent.native_'+name not in check:
            raise RuntimeError('Missing quotient descent native fixture: '+name)
    return {'actual_internal_unit_witness_and_strict_radix_comparison':True,
            'quotient_below_output_and_strict_for_nonzero_output':True,
            'zero_quotient_iff_output_below_actual_radix':True,
            'zero_output_iff_both_fields_zero':True,
            'arbitrary_object_matrix_quotient_induction_by_original_Foundation_Separation':True,
            'internal_IH_discharged_with_explicit_object_base_step_premises':True,
            'all_internal_actual_relational_Packet_descent_and_stopping_branches':True,
            'actual_literal_system_exists_under_only_omega':True,
            'concrete_full_varint_program_termination_correctness':False,
            'original_Basic_AST_bridge_and_final_Con':False}


def check_Packet_original_token_applications() -> dict:
    modules = ['PacketTokenRuleData', 'PacketTokenSyntax', 'PacketTokenExpr', 'PacketTokenMatrix', 'PacketTokenLocal', 'PacketTokenNatural', 'PacketTokenEntryArithmetic', 'PacketTokenApplicationBounds', 'PacketTokenApplicationSyntax', 'PacketTokenApplication', 'PacketTokenDispatchData', 'PacketTokenDispatch', 'PacketTokenSystemSyntax', 'PacketTokenSystem', 'ObjectPacketToken']
    schemas = ['packetTokenSmallExactMatrix', 'packetTokenLargeExactMatrixAt', 'packetTokenLargeExactMatrixWitnessesDischarged', 'packetTokenLargeAssignmentNatural', 'packetTokenCanonicalAffineEntryArithmetic', 'packetTokenDigitBelowAffineOutput', 'packetTokenAllSixActualAssignmentBoundsAt', 'packetTokenAllSixActualAssignmentBounds', 'packetTokenSmallApplicationIff', 'packetTokenLargeApplicationIff', 'packetTokenOriginalTwoRuleDispatch', 'packetTokenCompleteStepEquation', 'packetTokenActualConditionEquation', 'packetTokenAllInternalRootEquation', 'packetTokenActualTwoRadixSystemExists']
    required = {'PacketTokenRuleData': ['ObjectPacket.tokenSmall', 'ObjectPacket.tokenLarge', 'theorem actual_rules', 'largeRule.arity = 6', 'theorem large_guards', 'theorem large_premises'], 'PacketTokenSyntax': ['def tagRow', 'def tagEntry', 'def row', 'def small', 'def largeAt', 'tagEntry 0', 'tagEntry 1', 'entry w V (env 4) (env 1) (env 5)', 'existsMany 2'], 'PacketTokenExpr': ['HornExprConstructor.constructor_iff', 'theorem variable_premise_iff', 'ObjectPacket.Expr.addConst 128', 'HornExprAddConst.backward', 'theorem shifted_premise_iff'], 'PacketTokenMatrix': ['theorem small_at', 'theorem large_at', 'HornRuleValue.guard_at', 'SyntaxAtomSyntax.three (3 : Fin 6) 4 0', 'SyntaxAtomSyntax.three (4 : Fin 6) 1 5', 'PacketTokenExpr.shifted_premise_iff'], 'PacketTokenLocal': ['SyntaxNumerals.exists_numeral hZ 0', 'ZFArithmetic.add_exists', 'theorem large_forward', 'theorem large_backward', 'HornBinderRules.eliminate_many 2', 'theorem large_iff'], 'PacketTokenNatural': ['theorem row_environment', 'theorem entry_environment', 'theorem largeAt_environment', 'theorem large_environment', 'SyntaxConstructors.child_member'], 'PacketTokenEntryArithmetic': ['theorem affine_of_entry', 'PacketAffineInduction.membership_iff', 'theorem digit_below_output', 'GodelPairArithmetic.sum_left_bound'], 'PacketTokenApplicationBounds': ['theorem largeAt_bounds', 'PacketTokenEntryArithmetic.affine_of_entry hZ false', 'PacketTokenEntryArithmetic.affine_of_entry hZ true', 'PacketDivisionDescentCore.quotient_below hZ false', 'PacketDivisionDescentCore.quotient_below hZ true', 'theorem large_bounds', 'intro_environmentBound r env'], 'PacketTokenApplicationSyntax': ['existsMany 3', 'existsMany 6', 'def smallOutcome', 'def largeOutcome'], 'PacketTokenApplication': ['theorem small_iff', 'theorem large_iff', 'HornBinderRules.eliminate_many 6', 'PacketTokenNatural.large_environment', 'PacketTokenApplicationBounds.large_bounds', 'HornApplicationRules.intro_application largeRule'], 'PacketTokenDispatchData': ['ObjectPacket.rules.take 4 ++ ObjectPacket.rules.drop 6', 'theorem others_classified', 'theorem rule_cases'], 'PacketTokenDispatch': ['HornNodeDisjoint.node_contradiction', 'HornStepSyntax.step_elim ObjectPacket.rules', 'theorem step_iff_outcomes', 'theorem condition_iff_outcomes', 'PacketTraceCore.unfold_iff'], 'PacketTokenSystemSyntax': ['OriginalUniversalBlock.allMany 4', 'PacketTokenSyntax.row', 'PacketTraceSyntax.condition', 'PacketTokenApplicationSyntax.smallOutcome', 'PacketTokenApplicationSyntax.largeOutcome', 'existsMany 3'], 'PacketTokenSystem': ['theorem all_law', 'theorem exists_system', 'SyntaxNumerals.exists_numeral hZ 128', 'SyntaxNumerals.exists_numeral hZ1 256', 'PacketTraceCore.exists_value hZ2'], 'ObjectPacketToken': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden, text) or re.search(r'(?m)^\s+induction\b', text):
            raise RuntimeError('Original token application forbidden gap or host induction: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Original token application proof drift: '+mod+': '+clause)
    signatures = [('PacketTokenLocal', 'large_iff', {'hB', 'hw', 'hn'}), ('PacketTokenNatural', 'large_environment', {'hw', 'hl'}), ('PacketTokenApplicationBounds', 'large_bounds', {'hw', 'hl', 'hv', 'hB', 'hC'}), ('PacketTokenApplication', 'small_iff', {'hw', 'hB'}), ('PacketTokenApplication', 'large_iff', {'hw', 'hv', 'hB', 'hC'}), ('PacketTokenDispatch', 'condition_iff_outcomes', {'hw', 'hB', 'hv', 'hC', 'hc'}), ('PacketTokenSystem', 'all_law', {'hw', 'hv', 'hB', 'hC'}), ('PacketTokenSystem', 'exists_system', {'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Original token application hidden premise: '+mod+'.'+name)
    if 'PacketTokenEntryArithmetic.affine_of_entry' not in texts['PacketTokenApplicationBounds']:
        raise RuntimeError('Auxiliary assignments require actual canonical premise arithmetic')
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketToken.native_'+name not in check:
            raise RuntimeError('Missing original token native fixture: '+name)
    return {'original_tokenSmall_tokenLarge_metadata_exact':True,
            'all_two_guards_and_three_ordered_large_premises_retained':True,
            'actual_addConst_128_and_object_zero_sum_witnesses_discharged':True,
            'all_six_assignments_natural_from_real_rows':True,
            'auxiliary_digit_quotient_recursive_output_search_bounds_by_actual_affine_arithmetic':True,
            'complete_original_arity_3_6_bounded_applications_equivalent_under_actual_canonical_value':True,
            'all_eight_foreign_rules_excluded_by_object_tag_disjointness':True,
            'actual_relational_Packet_condition_complete_token_outcome_equation_ALL4':True,
            'both_radices_and_canonical_value_object_exist_under_only_omega':True,
            'specified_root_fields_full_normalization':True,
            'all_internal_token_execution_total_unique':True,
            'full_varint_Basic_AST_bridge_Proof_Con':False}


def check_Packet_token_exact_arithmetic_recursion() -> dict:
    modules = ['PacketTokenRootTransport', 'PacketTokenRootSyntax', 'PacketTokenRootSmall', 'PacketTokenRootLarge', 'PacketTokenRootEquation', 'PacketTokenAcceptedSyntax', 'PacketTokenCanonicalEntry', 'PacketTokenArithmeticSyntax', 'PacketTokenArithmeticBridge', 'PacketTokenAcceptedNatural', 'PacketTokenArithmeticEquation', 'PacketTokenArithmeticProperties', 'PacketTokenArithmeticSystemSyntax', 'PacketTokenArithmeticSystem', 'ObjectPacketTokenArithmetic']
    schemas = ['packetTokenRootSmallFieldsIff', 'packetTokenRootLargeFieldsIff', 'packetTokenSpecifiedRootConditionEquation', 'packetTokenSpecifiedRootMemberEquation', 'packetTokenCanonicalEntryActualAcceptanceIff', 'packetTokenCanonicalEntryAffineIff', 'packetTokenZeroGuardFromNonzeroQuotient', 'packetTokenSmallExactArithmeticBridge', 'packetTokenLargeExactArithmeticBridge', 'packetTokenFullExactArithmeticBridge', 'packetTokenActualAcceptanceNaturalFields', 'packetTokenArithmeticCriterionNaturalFields', 'packetTokenConditionExactArithmeticWithoutCanonicalWitness', 'packetTokenActualAcceptedExactArithmeticRecursion', 'packetTokenLargeBranchExcludesSmallInput', 'packetTokenActualSmallBranchIff', 'packetTokenActualLargeBranchIff', 'packetTokenActualRejectInvalidField', 'packetTokenAllInternalAcceptedArithmeticRecursion', 'packetTokenAllInternalRootArithmeticRecursion', 'packetTokenActualArithmeticRecursionSystemExists']
    required = {'PacketTokenRootTransport': ['Derives.eqSubst', 'theorem entry_first', 'theorem entry_second', 'theorem entry_third'], 'PacketTokenRootSyntax': ['def smallCase', 'def largeBody', 'existsMany 5', 'def criterion', 'theorem intro_large'], 'PacketTokenRootSmall': ['HornBinderRules.eliminate_many 3', 'SyntaxNodeInjective.constructor_input_eq', 'PacketTokenRootTransport.entry_first', 'PacketTokenRootTransport.entry_second', 'PacketTokenRootTransport.entry_third', 'theorem small_iff'], 'PacketTokenRootLarge': ['existsMany 8', 'theorem actual_witness', 'SyntaxNodeInjective.constructor_input_eq', 'PacketTokenRootTransport.entry_third 0', 'PacketTokenRootTransport.entry_second 2', 'PacketTokenRootTransport.entry_third 1', 'theorem large_iff'], 'PacketTokenRootEquation': ['PacketTokenDispatch.condition_iff_outcomes', 'PacketTokenRootSmall.small_iff', 'PacketTokenRootLarge.large_iff', 'theorem member_iff'], 'PacketTokenAcceptedSyntax': ['def tagAccepted', 'PacketTraceSyntax.condition', 'def accepted', 'tagAccepted 2', 'theorem intro_accepted'], 'PacketTokenCanonicalEntry': ['theorem entry_iff', 'PacketTraceCore.member_iff', 'theorem affine_entry_iff', 'PacketAffineAccepted.accepted_iff'], 'PacketTokenArithmeticSyntax': ['def largeBody', 'existsMany 4', 'affine (old 4 w) (old 4 B)', 'accepted (old 4 w) (slot 4 1) (old 4 t) (slot 4 2)', 'affine (old 4 w) (old 4 C)', 'theorem intro_large'], 'PacketTokenArithmeticBridge': ['theorem zero_member', 'GodelUnpairArithmetic.zero_below', 'PacketTokenCanonicalEntry.affine_entry_iff', 'PacketTokenCanonicalEntry.entry_iff 2', 'theorem large_forward', 'theorem large_backward', 'SyntaxNumerals.exists_numeral hZ4 0', 'theorem criterion_iff'], 'PacketTokenAcceptedNatural': ['theorem accepted_environment', 'PacketTokenNatural.row_environment', 'theorem criterion_environment', 'PacketAffineCore.output_guard'], 'PacketTokenArithmeticEquation': ['PacketTraceCore.exists_value hZ w', 'theorem condition_iff', 'theorem accepted_iff', 'PacketTokenAcceptedNatural.criterion_environment', 'SyntaxConstructors.exists_constructor', 'intro_accepted'], 'PacketTokenArithmeticProperties': ['theorem large_not_small', 'PacketDivisionDescentCore.terminal_iff', 'theorem accepted_small_iff', 'theorem accepted_large_iff', 'theorem reject_field'], 'PacketTokenArithmeticSystemSyntax': ['OriginalUniversalBlock.allMany 3', 'OriginalUniversalBlock.allMany 4', 'existsMany 2', 'def existsSystem'], 'PacketTokenArithmeticSystem': ['theorem all_law', 'theorem all_root_law', 'theorem exists_system', 'SyntaxNumerals.exists_numeral hZ 128', 'SyntaxNumerals.exists_numeral hZ1 256'], 'ObjectPacketTokenArithmetic': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden, text) or re.search(r'(?m)^\s+induction\b', text):
            raise RuntimeError('Token exact arithmetic recursion forbidden gap or host induction: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Token exact arithmetic recursion proof drift: '+mod+': '+clause)
    signatures = [('PacketTokenRootSmall', 'small_iff', {'hr', 'hw'}), ('PacketTokenRootLarge', 'large_iff', {'hr', 'hw'}), ('PacketTokenArithmeticBridge', 'criterion_iff', {'hv', 'hB', 'hC', 'hw'}), ('PacketTokenArithmeticEquation', 'condition_iff', {'hB', 'hr', 'hC', 'hw'}), ('PacketTokenArithmeticEquation', 'accepted_iff', {'hB', 'hC', 'hw'}), ('PacketTokenArithmeticSystem', 'all_law', {'hB', 'hC', 'hw'}), ('PacketTokenArithmeticSystem', 'all_root_law', {'hB', 'hC', 'hw'}), ('PacketTokenArithmeticSystem', 'exists_system', {'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Token exact arithmetic recursion hidden premise: '+mod+'.'+name)
    definition = texts['PacketTokenAcceptedSyntax'].split('def tagAccepted')[1].split('theorem tagAccepted_rename')[0]
    if 'affine' in definition or 'criterion' in definition or 'PacketTraceSyntax.condition' not in definition or 'tagRow' not in definition:
        raise RuntimeError('Actual token acceptance must be independent of the arithmetic recurrence answer')
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketTokenArithmetic.native_'+name not in check:
            raise RuntimeError('Missing exact token arithmetic native fixture: '+name)
    return {'original_EX3_EX8_fields_aligned_by_object_injectivity':True,
            'original_zero_guard_and_arithmetic_shift_witnesses_object_eliminated':True,
            'actual_independent_recursive_token_acceptance_retained':True,
            'canonical_value_and_actual_root_witnesses_object_eliminated':True,
            'all_internal_actual_acceptance_iff_exact_arithmetic_recurrence_ALL3':True,
            'all_internal_specified_root_arithmetic_equation_ALL4':True,
            'actual_small_large_test_exact_and_invalid_fields_rejected':True,
            'actual_two_radix_recursion_system_exists_under_only_omega':True,
            'all_internal_token_execution_total_unique':True,
            'full_varint_Basic_AST_bridge_Proof_Con':False}


def check_Packet_actual_token_execution() -> dict:
    modules = ['SyntaxNumeralAddition', 'PacketTokenByteBounds', 'PacketTokenExistenceSyntax', 'PacketTokenExistencePoint', 'PacketTokenExistenceInduction', 'PacketTokenValueTransport', 'PacketTokenUniqueSyntax', 'PacketTokenUniqueValues', 'PacketTokenUniquePoint', 'PacketTokenUniqueInduction', 'PacketTokenExecutionSyntax', 'PacketTokenExecutionFiber', 'PacketTokenExecution', 'ObjectPacketTokenExecution']
    schemas = ['packetTokenFiniteNumeralSum', 'packetTokenActualDouble128', 'packetTokenSmallDigitByteBound', 'packetTokenShiftedDigitByteBound', 'packetTokenActualSmallOutputConstructed', 'packetTokenActualRecursiveOutputConstructed', 'packetTokenAllInternalOutputExistenceIHDischarged', 'packetTokenActualOutputExistsAtRadices', 'packetTokenAllInternalOutputUniquenessIHDischarged', 'packetTokenActualOutputUniqueAtRadices', 'packetTokenActualUniqueOutputFiberAtRadices', 'packetTokenUniqueOutputFiberDomainAtRadices', 'packetTokenAllInternalExactUniqueOutputFibers', 'packetTokenActualUniqueOutputFiberExactDomain', 'packetTokenActualOutputExistsOnlyOmega', 'packetTokenActualOutputUniqueOnlyOmega']
    required = {'SyntaxNumeralAddition': ['theorem sum_at', '(i j : Nat)', '(numeral (i+j) c)', 'induction j generalizing m with', 'add_succ_backward'], 'PacketTokenByteBounds': ['SyntaxNumeralAddition.sum_at hZ 128 128', 'theorem small_digit_byte', 'NaturalAdditionMonotone.strict_monotone', 'theorem shifted_digit_byte'], 'PacketTokenExistenceSyntax': ['def existsOutput', 'accepted w.castSucc', 'def property', 'def matrix', 'theorem property_at'], 'PacketTokenExistencePoint': ['theorem small_point', 'theorem step_values', 'PacketTokenByteBounds.shifted_digit_byte', 'PacketAffineCore.exists_value', 'PacketTokenArithmeticSyntax.intro_large', 'theorem large_point'], 'PacketTokenExistenceInduction': ['theorem small_property', 'theorem large_property', 'theorem all_property', 'PacketQuotientInduction.all_holds hZ false PacketTokenExistenceSyntax.matrix', 'theorem exists_output'], 'PacketTokenValueTransport': ['Derives.eqSubst', 'theorem accepted_input', 'theorem sum_first'], 'PacketTokenUniqueSyntax': ['OriginalUniversalBlock.allMany 3', 'def property', 'def matrix', 'theorem property_at', 'theorem input_subst'], 'PacketTokenUniqueValues': ['PacketDivisionUnique.unique', 'PacketTokenValueTransport.accepted_input', 'ZFArithmetic.add_unique', 'PacketAffineTransport.digit', 'PacketAffineTransport.tail', 'PacketAffineCore.unique'], 'PacketTokenUniquePoint': ['theorem large_cases_unique', 'HornBinderRules.eliminate_many 4 L', 'HornBinderRules.eliminate_many 4 M', 'PacketTokenUniqueValues.unique', 'theorem large_point'], 'PacketTokenUniqueInduction': ['theorem all_property', 'PacketQuotientInduction.all_holds hZ false PacketTokenUniqueSyntax.matrix', 'theorem unique'], 'PacketTokenExecutionSyntax': ['def uniqueAt', 'def fiber', 'def allLaw', 'OriginalUniversalBlock.allMany 2', 'theorem uniqueAt_at'], 'PacketTokenExecutionFiber': ['theorem exists_fiber', 'PacketTokenExistenceInduction.exists_output', 'PacketTokenUniqueInduction.unique', 'theorem fiber_iff'], 'PacketTokenExecution': ['theorem all_law_at', 'theorem all_law', 'SyntaxNumerals.exists_numeral hZ 128', 'SyntaxNumerals.exists_numeral hZ1 256', 'theorem fiber_iff', 'theorem exists_output', 'theorem unique'], 'ObjectPacketTokenExecution': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden, text):
            raise RuntimeError('Actual token execution forbidden gap: '+mod)
        inductions = re.findall(r'(?m)^\s+induction[^\n]*',text)
        if mod == 'SyntaxNumeralAddition':
            if [x.strip() for x in inductions] != ['induction j generalizing m with'] or '(i j : Nat)' not in text:
                raise RuntimeError('Only external finite numeral-index induction is permitted')
        elif inductions:
            raise RuntimeError('Internal token runtime values cannot use host induction: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Actual token execution proof drift: '+mod+': '+clause)
    signatures = [('PacketTokenExistenceInduction', 'all_property', {'hB', 'hC', 'hw'}), ('PacketTokenExistenceInduction', 'exists_output', {'hB', 'hC', 'hn', 'hw', 'ht'}), ('PacketTokenUniqueInduction', 'all_property', {'hB', 'hC', 'hw'}), ('PacketTokenUniqueInduction', 'unique', {'hb', 'hB', 'hC', 'hw', 'ha'}), ('PacketTokenExecution', 'all_law', {'hw'}), ('PacketTokenExecution', 'fiber_iff', {'hw'}), ('PacketTokenExecution', 'exists_output', {'hn', 'hw', 'ht'}), ('PacketTokenExecution', 'unique', {'hb', 'hw', 'ha'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Actual token execution hidden premise: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketTokenExecution.native_'+name not in check:
            raise RuntimeError('Missing actual token execution native fixture: '+name)
    return {'external_finite_numeral_index_only_object_addition_certificate':True,
            'actual_128_plus_128_256_and_shifted_digit_byte_bound':True,
            'actual_output_existence_internal_quotient_IH_fully_discharged':True,
            'actual_output_uniqueness_both_full_large_witness_blocks_compared':True,
            'actual_output_uniqueness_internal_quotient_IH_fully_discharged':True,
            'typed_unique_output_fiber_exactly_internal_natural_input_tail_pairs':True,
            'all_internal_and_invalid_input_tail_candidates_retained_ALL2':True,
            'actual_radix_witnesses_object_eliminated_only_omega_premise':True,
            'full_varint_canonical_bytes_Basic_AST_bridge_Proof_Con':False}


def check_Packet_actual_token_numeric_bounds() -> dict:
    modules = ['PacketTokenBoundComparison', 'PacketTokenBoundsSyntax', 'PacketTokenBoundsPoint', 'PacketTokenBoundsInduction', 'PacketTokenBoundsSystemSyntax', 'PacketTokenBounds', 'ObjectPacketTokenBounds']
    schemas = ['packetTokenTwoCoordinateSumComparison', 'packetTokenTwoCoordinateProductComparison', 'packetTokenActualAffineComparison', 'packetTokenSmallInputTailBounds', 'packetTokenAllInternalBoundsIHDischarged', 'packetTokenInputTailBoundsAtRadices', 'packetTokenAllNumericBoundsAtRadices', 'packetTokenAllInternalNumericBoundsOnlyOmega', 'packetTokenActualInputTailBoundsOnlyOmega', 'packetTokenActualInputBelowOutput', 'packetTokenActualTailBelowOutput', 'packetTokenActualContainedInputTailBounds']
    required = {'PacketTokenBoundComparison': ['theorem sum_compare', 'theorem product_compare', 'theorem affine_compare', 'NaturalMultiplicationOrderLaws.left_monotone', 'NaturalOrderBasic.transitive'], 'PacketTokenBoundsSyntax': ['def bounds', 'def property', 'def matrix', 'OriginalUniversalBlock.allMany 2', 'Derives.eqSubst'], 'PacketTokenBoundsPoint': ['theorem small_point', 'theorem large_point', 'PacketDivisionUnique.unique', 'PacketTokenBoundComparison.affine_compare', 'property_at', 'quotient_below'], 'PacketTokenBoundsInduction': ['theorem all_property', 'PacketQuotientInduction.all_holds hZ false PacketTokenBoundsSyntax.matrix', 'theorem bounds_at'], 'PacketTokenBoundsSystemSyntax': ['def lawBody', 'def allLaw', 'OriginalUniversalBlock.allMany 3'], 'PacketTokenBounds': ['theorem all_law', 'SyntaxNumerals.exists_numeral hZ 128', 'SyntaxNumerals.exists_numeral hZ1 256', 'theorem input_below', 'theorem tail_below', 'theorem contained_bounds'], 'ObjectPacketTokenBounds': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Actual token numeric bounds forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Actual token numeric bounds proof drift: '+mod+': '+clause)
    signatures = [('PacketTokenBoundsInduction','all_property',{'hw','hB','hC'}),('PacketTokenBoundsInduction','bounds_at',{'hw','hB','hC','ha'}),('PacketTokenBounds','all_law',{'hw'}),('PacketTokenBounds','bounds',{'hw','ha'}),('PacketTokenBounds','input_below',{'hw','ha'}),('PacketTokenBounds','tail_below',{'hw','ha'}),('PacketTokenBounds','contained_bounds',{'hw','ha','hr','har'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Actual token numeric bounds hidden premise: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketTokenBounds.native_'+name not in check:
            raise RuntimeError('Missing actual token numeric bounds native fixture: '+name)
    return {'actual_input_and_tail_below_actual_output':True,
            'fixed_object_matrix_original_quotient_induction_all_IH_discharged':True,
            'all_internal_input_tail_output_candidates_retained_ALL3':True,
            'actual_radix_witnesses_eliminated_only_omega_and_actual_Tok':True,
            'numeric_containment_corollary_requires_actual_output_bound':True,
            'full_tree_forest_packet_search_bounds_Basic_AST_Proof_Con':False}


def check_Packet_original_structural_forward_unfolding() -> dict:
    modules = ['PacketStructureRuleData', 'PacketStructureSyntax', 'PacketStructureExpr', 'PacketStructureMatrix', 'PacketStructureLocalSyntax', 'PacketStructureLocal', 'PacketStructureApplicationSyntax', 'PacketStructureApplication', 'PacketStructureDispatchData', 'PacketStructureDispatch', 'PacketStructureSystemSyntax', 'PacketStructureSystem', 'ObjectPacketStructure']
    schemas = ['packetStructureTreeExactMatrix', 'packetStructureForestNilExactMatrix', 'packetStructureForestConsExactMatrix', 'packetStructurePacketExactMatrix', 'packetStructureAllFourCompleteLocalMatrices', 'packetStructureOriginalBoundedApplicationsIff', 'packetStructureOriginalApplicationForward', 'packetStructureOriginalThreeTagDispatch', 'packetStructureActualConditionBoundedIff', 'packetStructureActualConditionForward', 'packetStructureActualRootLaw', 'packetStructureAllInternalRootLaws', 'packetStructureActualSystemExistsOnlyOmega']
    required = {'PacketStructureRuleData': ['ObjectPacket.treeRule', 'ObjectPacket.forestNil', 'ObjectPacket.forestCons', 'ObjectPacket.packetRule', 'treeRule.arity = 7', 'nilRule.arity = 1', 'consRule.arity = 6', 'packetRule.arity = 3', 'theorem tree_premises', 'theorem cons_premises', 'theorem packet_premises'], 'PacketStructureSyntax': ['def four', 'def forestRow', 'row 4 4', 'def packetRow', 'row 2 5', 'def treeAt', 'def nilAt', 'def consAt', 'def packetAt', 'PacketTokenSyntax.entry w V (env 0) (env 6) (env 3)'], 'PacketStructureExpr': ['HornExprConstructor.constructor_iff', 'FormulaCodeCongruence.ex_congr', 'theorem var_graph'], 'PacketStructureMatrix': ['theorem tree_at', 'theorem nil_at', 'theorem cons_at', 'theorem packet_at', 'HornExprStructural.raw_graph', 'StructuralNil.at_unit', 'HornExprStructural.cons_graph', 'intro_succ', 'have hp2'], 'PacketStructureLocalSyntax': ['def treeBody', 'def nilBody', 'def consBody', 'def packetBody', 'existsMany 1', 'existsMany 2', 'StructuralNodeSyntax.raw', 'StructuralListSyntax.consCode', 'SyntaxNumeralSyntax.numeral 1'], 'PacketStructureLocal': ['StructuralNodeExistence.exists_raw', 'StructuralListUnits.exists_units', 'StructuralConsCore.exists_cons', 'OriginalBinderStepSyntax.successor_exists', 'SyntaxNumerals.exists_numeral hZ 1', 'theorem tree_iff', 'theorem nil_iff', 'theorem cons_iff', 'theorem packet_iff'], 'PacketStructureApplicationSyntax': ['inductive Branch', 'def boundedAt', 'environmentNat (rule b).arity', 'environmentBound (rule b).arity', 'def boundedOutcome', 'def outcome'], 'PacketStructureApplication': ['theorem bounded_iff', 'theorem bounded_forward', 'theorem bounded_backward', 'theorem forward', 'HornApplicationRules.intro_application', 'HornApplicationRules.eliminate_application'], 'PacketStructureDispatchData': ['inductive Family', '| .tree => 3', '| .forest => 4', '| .packet => 5', 'ObjectPacket.rules.filter', 'theorem rule_cases', 'List.mem_filter.mpr'], 'PacketStructureDispatch': ['HornNodeDisjoint.node_contradiction', 'HornStepSyntax.step_elim ObjectPacket.rules', 'theorem step_iff_applications', 'theorem condition_iff_bounded', 'theorem condition_forward'], 'PacketStructureSystemSyntax': ['OriginalUniversalBlock.allMany (width f+1)', 'allLaw .tree w V', 'allLaw .forest w V', 'allLaw .packet w V', 'def existsSystem'], 'PacketStructureSystem': ['theorem all_law', 'theorem exists_system', 'PacketTraceCore.exists_value hZ w', 'all_law hZ1 .forest'], 'ObjectPacketStructure': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Original structural unfolding forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Original structural unfolding proof drift: '+mod+': '+clause)
    signatures = [('PacketStructureApplication','bounded_iff',{'hw'}),('PacketStructureApplication','forward',{'hw','ha'}),('PacketStructureDispatch','condition_iff_bounded',{'hw','hv','hc'}),('PacketStructureDispatch','condition_forward',{'hw','hv','hc','hr'}),('PacketStructureSystem','all_law',{'hw','hv'}),('PacketStructureSystem','exists_system',{'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Original structural unfolding hidden premise: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketStructure.native_'+name not in check: raise RuntimeError('Missing original structure native fixture: '+name)
    return {'four_original_arities_heads_guards_ordered_premises_preserved':True,
            'rawNode_nil_cons_successor_unit_witnesses_object_eliminated':True,
            'four_full_local_matrices_equivalent_for_natural_internal_environments':True,
            'exact_bounded_applications_keep_original_natural_and_search_guards':True,
            'four_original_applications_imply_unbounded_structural_outcomes':True,
            'three_actual_root_tags_dispatch_against_full_original_ten_rule_table':True,
            'ALL4_ALL5_ALL3_all_internal_root_candidates_preserved':True,
            'common_canonical_accepting_set_and_three_root_laws_exist_only_omega':True,
            'external_Branch_Family_indices_only_finite_metadata_no_runtime_values':True,
            'specified_root_witness_fields_fully_normalized':True,
            'joint_internal_tree_forest_tail_bound':True,
            'reverse_unbounded_assignment_search_bounds_discharged':True,
            'full_bytes_Basic_AST_schema_Proof_Con':False}


def check_Packet_specified_structural_root_recursion() -> dict:
    modules = ['PacketStructureRootTransport', 'PacketStructureRootSyntax', 'PacketStructureRootWitness', 'PacketStructureRootTree', 'PacketStructureRootNil', 'PacketStructureRootCons', 'PacketStructureRootPacket', 'PacketStructureRootEquation', 'PacketStructureAcceptedSyntax', 'PacketStructureCanonicalCases', 'PacketStructureAcceptedForward', 'PacketStructureRootLawSyntax', 'PacketStructureRootLaws', 'ObjectPacketStructureRoot']
    schemas = ['packetStructureRootTreeFieldsIff', 'packetStructureRootForestNilFieldsIff', 'packetStructureRootForestConsFieldsIff', 'packetStructureRootPacketFieldsIff', 'packetStructureRootAllActualOutcomesNormalized', 'packetStructureRootCanonicalEntryActualAcceptanceIff', 'packetStructureRootCanonicalCriterionActualRecursiveCasesIff', 'packetStructureRootConditionNormalizedForward', 'packetStructureRootActualRecursiveCasesWithoutCanonicalSet', 'packetStructureRootActualAcceptedRecursiveCasesOnlyOmega', 'packetStructureRootActualAcceptedAllFieldsNatural', 'packetStructureRootAllInternalOutcomeFieldNormalization', 'packetStructureRootAllInternalAcceptedRecursion', 'packetStructureRootActualTreeForward', 'packetStructureRootActualForestForward', 'packetStructureRootActualPacketForward', 'packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmega']
    required = {'PacketStructureRootTransport': ['Derives.eqSubst', 'theorem forest_tail', 'theorem forest_row_output', 'theorem tree_input'], 'PacketStructureRootSyntax': ['def treeCaseBody', 'existsMany 5', 'def nilCase', 'successor n l', 'def consCaseBody', 'existsMany 4', 'def packetCaseBody', 'existsMany 2'], 'PacketStructureRootWitness': ['theorem actual_tree_witness', 'existsMany 8', 'theorem actual_nil_witness', 'existsMany 3', 'theorem actual_cons_witness', 'theorem actual_packet_witness', 'existsMany 4'], 'PacketStructureRootTree': ['constructor_input_eq hZ8 3 3 3', 'StructuralNodeSyntax.output_subst', 'forest_tail', 'entry_third 2', 'theorem backward', 'theorem root_iff'], 'PacketStructureRootNil': ['constructor_input_eq hZ3 4 4 4', 'successor_base_subst', 'successor_subst_target', 'eq_trans (eq_symm (he 2)) (he 3)', 'theorem root_iff'], 'PacketStructureRootCons': ['constructor_input_eq hZ8 4 4 4', 'cons_output_subst', 'successor_subst_target', 'forest_tail', 'tree_output', 'theorem root_iff'], 'PacketStructureRootPacket': ['constructor_input_eq hZ4 2 5 5', 'SyntaxAtomSyntax.two (slot 4 1) (slot 4 0)', 'entry_third 1', 'tree_input', 'theorem root_iff'], 'PacketStructureRootEquation': ['theorem outcomes_iff', 'PacketStructureRootTree.root_iff', 'PacketStructureRootNil.root_iff', 'PacketStructureRootCons.root_iff', 'PacketStructureRootPacket.root_iff', 'theorem condition_forward'], 'PacketStructureAcceptedSyntax': ['def accepted', 'PacketTraceSyntax.condition', 'def tree', 'def forest', 'def packet', 'def criterion', 'PacketTokenAcceptedSyntax.accepted'], 'PacketStructureCanonicalCases': ['theorem entry_iff', 'PacketTraceCore.member_iff', 'theorem tree_iff', 'theorem cons_iff', 'theorem packet_iff', 'theorem criterion_iff'], 'PacketStructureAcceptedForward': ['theorem accepted_environment', 'theorem root_forward', 'PacketTraceCore.exists_value hZ w', 'theorem accepted_forward', 'PacketStructureCanonicalCases.criterion_iff'], 'PacketStructureRootLawSyntax': ['def allRootLaw', 'def allAcceptedLaw', 'OriginalUniversalBlock.allMany (width f)', 'def allSystem', 'allAcceptedLaw .tree w', 'allAcceptedLaw .forest w', 'allAcceptedLaw .packet w'], 'PacketStructureRootLaws': ['theorem all_root_law', 'theorem all_accepted_law', 'theorem tree_forward', 'theorem forest_forward', 'theorem packet_forward', 'theorem all_system'], 'ObjectPacketStructureRoot': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Specified structure root forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Specified structure root proof drift: '+mod+': '+clause)
    signatures = [('PacketStructureRootEquation','outcomes_iff',{'hw','hr'}),('PacketStructureCanonicalCases','criterion_iff',{'hv'}),('PacketStructureAcceptedForward','root_forward',{'hw','hr','hc'}),('PacketStructureAcceptedForward','accepted_forward',{'hw','ha'}),('PacketStructureRootLaws','all_root_law',{'hw'}),('PacketStructureRootLaws','all_accepted_law',{'hw'}),('PacketStructureRootLaws','tree_forward',{'hw','ha'}),('PacketStructureRootLaws','forest_forward',{'hw','ha'}),('PacketStructureRootLaws','packet_forward',{'hw','ha'}),('PacketStructureRootLaws','all_system',{'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Specified structure root hidden premise: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketStructureRoot.native_'+name not in check: raise RuntimeError('Missing specified structure root native fixture: '+name)
    return {'original_full_witness_blocks_8_3_8_4_retained_before_alignment':True,
            'all_specified_head_fields_aligned_by_original_constructor_injectivity':True,
            'normalized_cases_iff_unbounded_outcomes_under_actual_root_row':True,
            'actual_acceptance_independent_of_recursive_criterion':True,
            'canonical_entries_iff_independent_actual_acceptance':True,
            'canonical_set_and_root_witnesses_object_eliminated':True,
            'ALL3_ALL4_ALL2_actual_forward_acceptance_laws_only_omega':True,
            'all_internal_invalid_nonstandard_field_candidates_retained':True,
            'all_actual_accepted_fields_natural_from_real_row':True,
            'joint_internal_tree_forest_tail_bound':True,
            'reverse_unbounded_assignment_search_bounds_discharged':True,
            'full_bytes_Basic_AST_schema_Proof_Con':False}


def check_Packet_joint_internal_structural_tail_bounds() -> dict:
    modules = ['PacketStructureTailSyntax', 'PacketStructureTailChildren', 'PacketStructureTailPoint', 'PacketStructureTailInduction', 'PacketStructureTailBounds', 'PacketStructureTailLawSyntax', 'PacketStructureTailLaws', 'ObjectPacketStructureTail']
    schemas = ['packetStructureTailActualRawPayloadStrictSubcode', 'packetStructureTailActualConsChildrenStrictSubcodes', 'packetStructureTailTreePointFromJointChildIH', 'packetStructureTailForestPointFromJointChildIH', 'packetStructureTailJointPoint', 'packetStructureTailJointObjectProgressive', 'packetStructureTailAllInternalJointIHDischarged', 'packetStructureTailActualTreeBelowOutput', 'packetStructureTailActualForestBelowOutput', 'packetStructureTailActualTreeContained', 'packetStructureTailActualForestContained', 'packetStructureTailAllInternalTreeLaw', 'packetStructureTailAllInternalForestLaw', 'packetStructureTailAllInternalCoupledLawsOnlyOmega']
    required = {'PacketStructureTailSyntax': ['def treeProperty', 'def forestProperty', 'def property', '(treeProperty w n).conj (forestProperty w n)', 'def matrix : Formula 2', 'def hypothesis', 'theorem ih_at'], 'PacketStructureTailChildren': ['theorem raw_payload', 'StructuralNodeProperties.components', 'theorem cons_children', 'StructuralConsCore.components', 'accepted_environment hZ 4 4', 'PacketTokenAcceptedNatural.accepted_environment'], 'PacketStructureTailPoint': ['theorem tree_point', 'theorem forest_point', 'PacketStructureRootLaws.tree_forward', 'PacketStructureRootLaws.forest_forward', 'raw_payload hZ5', 'cons_children hZ4', 'PacketTokenBounds.tail_below', '(.conjR hPq)', '(.conjL hPh)'], 'PacketStructureTailInduction': ['theorem point', 'theorem progressive', 'theorem all_property', 'BoundedInduction.induction_on_set PacketStructureTailSyntax.matrix', 'ZFContext.separation hZ PacketStructureTailSyntax.matrix.neg', '(ZFContext.arithmetic hZ).base.foundation'], 'PacketStructureTailBounds': ['theorem tree_tail', 'theorem forest_tail', 'property_at hZ w n hw', 'theorem tree_contained', 'theorem forest_contained'], 'PacketStructureTailLawSyntax': ['OriginalUniversalBlock.allMany 3', 'OriginalUniversalBlock.allMany 4', 'def allLaw', '(allTree w).conj (allForest w)'], 'PacketStructureTailLaws': ['theorem all_tree', 'theorem all_forest', 'theorem all_law', 'PacketStructureTailBounds.tree_tail', 'PacketStructureTailBounds.forest_tail'], 'ObjectPacketStructureTail': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Joint actual structural tail forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Joint actual structural tail proof drift: '+mod+': '+clause)
    signatures = [('PacketStructureTailInduction','all_property',{'hw'}),('PacketStructureTailBounds','tree_tail',{'hw','ha'}),('PacketStructureTailBounds','forest_tail',{'hw','ha'}),('PacketStructureTailBounds','tree_contained',{'hw','ha','hr','har'}),('PacketStructureTailBounds','forest_contained',{'hw','ha','hr','har'}),('PacketStructureTailLaws','all_tree',{'hw'}),('PacketStructureTailLaws','all_forest',{'hw'}),('PacketStructureTailLaws','all_law',{'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Joint actual structural tail hidden premise: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketStructureTail.native_'+name not in check: raise RuntimeError('Missing joint actual structural tail native fixture: '+name)
    return {'one_fixed_object_Formula2_couples_actual_tree_and_forest_tail_properties':True,
            'real_accepted_children_supply_naturality_and_strict_Raw_Cons_subcode_descent':True,
            'tree_point_uses_smaller_forest_and_two_actual_Tok_tail_bounds':True,
            'forest_cons_point_uses_both_smaller_tree_and_smaller_forest':True,
            'original_Foundation_full_Separation_discharge_all_internal_child_IH':True,
            'final_ALL3_ALL4_actual_tail_laws_require_only_omega':True,
            'all_internal_invalid_nonstandard_field_candidates_retained':True,
            'containment_corollaries_retain_actual_output_bound_and_naturality':True,
            'reverse_unbounded_assignment_search_bounds_discharged':True,
            'full_bytes_Basic_AST_schema_Proof_Con':False}


def check_Packet_structural_search_bounds_and_typed_recursion() -> dict:
    modules = ['PacketStructureSearchEnvironment', 'PacketStructureSearchArithmetic', 'PacketStructureSearchHead', 'PacketStructureSearchBounds', 'PacketStructureSearchApplication', 'PacketStructureSearchEquation', 'PacketStructureSearchAccepted', 'PacketStructureSearchLawSyntax', 'PacketStructureSearchLaws', 'ObjectPacketStructureSearch']
    schemas = ['packetStructureSearchAllOriginalAssignmentNaturality', 'packetStructureSearchAllOriginalAssignmentBounds', 'packetStructureSearchActualAffineTailOnlyOmega', 'packetStructureSearchFourOriginalApplicationsIff', 'packetStructureSearchActualRootConditionRecursionIff', 'packetStructureSearchTypedActualAcceptanceBackward', 'packetStructureSearchActualAcceptanceTypedRecursionIff', 'packetStructureSearchActualTreeTypedRecursionIff', 'packetStructureSearchActualForestTypedRecursionIff', 'packetStructureSearchActualPacketTypedRecursionIff', 'packetStructureSearchAllInternalRootConditionIff', 'packetStructureSearchAllInternalActualTypedRecursion', 'packetStructureSearchAllThreeActualTypedRecursionLaws', 'packetStructureSearchCanonicalRootSystemExistsOnlyOmega']
    required = {'PacketStructureSearchEnvironment': ['theorem entry_environment', 'theorem tree_at_natural', 'theorem nil_at_natural', 'theorem cons_at_natural', 'theorem packet_at_natural', 'theorem local_natural'], 'PacketStructureSearchArithmetic': ['PacketTokenBounds.input_below', 'PacketTokenBounds.tail_below', 'PacketStructureTailBounds.tree_tail', 'PacketStructureTailBounds.forest_tail', 'theorem affine_tail', 'SyntaxNumerals.exists_numeral hZ 256', 'PacketDivisionDescentCore.quotient_below'], 'PacketStructureSearchHead': ['theorem matrix_of_local', 'theorem root_natural', 'theorem variable_bound', 'HornExprBounds.variable_bound', 'PacketStructureSearchEnvironment.local_natural'], 'PacketStructureSearchBounds': ['theorem tree_bounds', 'environmentBound 7', 'theorem nil_bounds', 'environmentBound 1', 'theorem cons_bounds', 'environmentBound 6', 'theorem packet_bounds', 'environmentBound 3', 'PacketStructureSearchArithmetic.token_input', 'PacketStructureSearchArithmetic.tree_tail', 'PacketStructureSearchArithmetic.affine_tail', 'theorem local_bounds'], 'PacketStructureSearchApplication': ['theorem backward', 'PacketStructureSearchBounds.local_bounds', 'PacketStructureSearchEnvironment.local_natural', 'HornApplicationRules.intro_application', 'theorem application_iff'], 'PacketStructureSearchEquation': ['theorem applications_iff_outcomes', 'theorem condition_iff_criterion', 'PacketStructureSearchApplication.application_iff', 'PacketStructureRootEquation.outcomes_iff'], 'PacketStructureSearchAccepted': ['theorem backward', 'SyntaxConstructors.exists_constructor', 'PacketStructureSearchEquation.condition_iff_criterion', 'theorem accepted_iff', '(environmentNat (width f) w xs).conj (criterion f w xs)'], 'PacketStructureSearchLawSyntax': ['OriginalUniversalBlock.allMany (width f+1)', 'OriginalUniversalBlock.allMany (width f)', 'environmentNat (width f)', 'def allSystem', 'def existsCanonical'], 'PacketStructureSearchLaws': ['theorem all_actual', 'theorem all_root', 'theorem all_system', 'theorem exists_canonical', 'theorem tree_iff', 'theorem forest_iff', 'theorem packet_iff', 'environmentNat 4 w (four n l t a)'], 'ObjectPacketStructureSearch': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Actual structural search forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Actual structural search proof drift: '+mod+': '+clause)
    signatures = [('PacketStructureSearchBounds','local_bounds',{'hw','hv','hl'}),('PacketStructureSearchApplication','application_iff',{'hw','hv'}),('PacketStructureSearchAccepted','backward',{'hw','hn','hc'}),('PacketStructureSearchAccepted','accepted_iff',{'hw'}),('PacketStructureSearchLaws','all_actual',{'hw'}),('PacketStructureSearchLaws','all_system',{'hw'}),('PacketStructureSearchLaws','exists_canonical',{'hw'}),('PacketStructureSearchLaws','tree_iff',{'hw'}),('PacketStructureSearchLaws','forest_iff',{'hw'}),('PacketStructureSearchLaws','packet_iff',{'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Actual structural search hidden premise: '+mod+'.'+name)
    check = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketStructureSearch.native_'+name not in check: raise RuntimeError('Missing actual structural search native fixture: '+name)
    return {'all_original_7_1_6_3_assignment_naturality_derived_from_actual_rows':True,
            'actual_head_variables_bounded_by_original_expression_variable_bound':True,
            'tree_auxiliary_fields_bounded_by_real_token_input_and_tail':True,
            'cons_middle_tail_bounded_by_joint_actual_tree_tail':True,
            'packet_middle_tail_bounded_by_actual_affine_quotient_only_omega':True,
            'all_original_reverse_assignment_search_bounds_discharged':True,
            'four_full_original_bounded_applications_iff_unbounded_outcomes':True,
            'actual_root_condition_iff_normalized_canonical_recursive_cases':True,
            'actual_acceptance_iff_original_field_naturality_and_recursive_criterion':True,
            'Nil_tail_naturality_guard_preserved_for_all_invalid_candidates':True,
            'final_ALL3_ALL4_ALL2_actual_typed_recursion_requires_only_omega':True,
            'canonical_set_and_root_witnesses_constructed_and_object_eliminated':True,
            'full_bytes_Basic_AST_schema_Proof_Con':False}


def check_Packet_actual_token_prefix_inverse() -> dict:
    modules = ['PacketTokenPrefixTransport','PacketTokenPrefixSyntax','PacketTokenPrefixValues','PacketTokenPrefixPoint','PacketTokenPrefixInduction','PacketTokenPrefixLawSyntax','PacketTokenPrefixLaws','ObjectPacketTokenPrefix']
    required = {
        'PacketTokenPrefixTransport':['Derives.eqSubst','theorem accepted_output','theorem sum_output'],
        'PacketTokenPrefixSyntax':['OriginalUniversalBlock.allMany 4','def matrix : Formula 2','theorem property_at','theorem input_subst'],
        'PacketTokenPrefixValues':['theorem shifted_not_small','GodelPairArithmetic.sum_right_bound','NaturalOrderBasic.below_not_reverse','theorem small_large_false','PacketDivisionUnique.unique','theorem large_values','PacketTokenPrefixTransport.accepted_output','GodelPairArithmetic.cancel_sum_left','PacketAffineCore.unique'],
        'PacketTokenPrefixPoint':['theorem small_point','theorem large_cases_unique','theorem large_point','HornBinderRules.eliminate_many 4 L','HornBinderRules.eliminate_many 4 M','PacketTokenPrefixValues.small_large_false','PacketTokenPrefixValues.large_values'],
        'PacketTokenPrefixInduction':['theorem base','theorem step','theorem all_property','PacketQuotientInduction.all_holds hZ false PacketTokenPrefixSyntax.matrix','PacketTokenAcceptedNatural.accepted_environment'],
        'PacketTokenPrefixLawSyntax':['OriginalUniversalBlock.allMany 5','def five','def allLaw'],
        'PacketTokenPrefixLaws':['SyntaxNumerals.exists_numeral hZ 128','SyntaxNumerals.exists_numeral hZ1 256','theorem all_law','theorem unique','theorem fiber_iff','theorem output_iff','PacketTokenExecution.unique'],
        'ObjectPacketTokenPrefix':['TheoryTransport.sentence','ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Actual token prefix forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Actual token prefix proof drift: '+mod+': '+clause)
    for name,expected in [('all_law',{'hw'}),('unique',{'hw','ha','hb'}),('input_unique',{'hw','ha','hb'}),('tail_unique',{'hw','ha','hb'}),('fiber_iff',{'hw','ha'}),('output_iff',{'hw','ha','hb'})]:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts['PacketTokenPrefixLaws'])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Actual token prefix hidden premise: '+name)
    schemas = ['packetTokenPrefixShiftedByteNotSmall', 'packetTokenPrefixTerminalContinuationDisjoint', 'packetTokenPrefixTerminalInverse', 'packetTokenPrefixLargeWitnessInverse', 'packetTokenPrefixAllQuotientInduction', 'packetTokenPrefixAllAtRadices', 'packetTokenPrefixAllInternalOnlyOmega', 'packetTokenPrefixJointInverseOnlyOmega', 'packetTokenPrefixInputOnlyOmega', 'packetTokenPrefixTailOnlyOmega', 'packetTokenPrefixActualFiberIffOnlyOmega', 'packetTokenPrefixOutputIffOnlyOmega']
    checks = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketTokenPrefix.native_'+name not in checks: raise RuntimeError('Missing actual token prefix fixture: '+name)
    return {'actual_Tok_independently_defined_acceptance_preserved':True,
            'terminal_continuation_byte_disjointness_object_derived':True,
            'all_internal_numeric_inputs_and_remaining_tails_jointly_unique':True,
            'both_full_large_witness_blocks_object_eliminated':True,
            'original_Foundation_Separation_quotient_induction_all_IH_discharged':True,
            '128_256_radix_witnesses_constructed_and_object_eliminated':True,
            'final_ALL5_and_scalar_inverse_require_only_omega':True,
            'exact_actual_prefix_fiber_and_output_iff_proved':True,
            'all_invalid_and_nonstandard_candidates_remain_quantified':True,
            'full_canonical_byte_sequence_readTokens_bridge_proved':False,
            'full_Basic_AST_schema_Proof_Con_proved':False}


def check_Packet_ordered_byte_fold_trace() -> dict:
    modules = ['PacketBytesRowSyntax', 'PacketBytesTraceSyntax', 'PacketBytesRowMap', 'PacketBytesTraceProperties', 'PacketBytesTraceTransport', 'PacketBytesTraceAppend', 'PacketBytesTraceBase', 'PacketBytesLaws', 'ObjectPacketBytesTrace']
    required = {
        'PacketBytesRowSyntax':['def rowAt','successor j i','StructuralListSyntax.consCode w h x y','PacketAffineSyntax.affine w C h u v','existsMany 6','theorem intro_row'],
        'PacketBytesTraceSyntax':['StructuralListTraceSyntax.trace w z e l d f n','SequenceSyntax.sequence g d w','edge g z t','edge g l a','links w C l f g','def foldAt','def bytes','SyntaxNumeralSyntax.numeral 256'],
        'PacketBytesRowMap':['theorem row_map','theorem links_map','theorem append_links','edgeIncluded f F','edgeIncluded g G','HornBinderRules.eliminate_many 6'],
        'PacketBytesTraceProperties':['theorem length','theorem valid','theorem tail_natural','theorem output_natural','SequenceSyntax.bounded_at'],
        'PacketBytesTraceTransport':['Derives.eqSubst','theorem input_subst','theorem output_subst','theorem radix_subst'],
        'PacketBytesTraceAppend':['StructuralListTraceAppend.from_append','SequenceAppend.exists_append','PacketBytesRowMap.append_links','theorem at_successor','theorem extend_trace','theorem cons_fold','HornBinderRules.eliminate_many 6'],
        'PacketBytesTraceBase':['StructuralListTraceBase.exists_base','SequenceAppend.exists_append','StructuralListUnits.with_units','theorem nil_fold','theorem nil_value','theorem nil_iff','GraphProperties.single_valued'],
        'PacketBytesLaws':['SyntaxNumerals.unique','SyntaxNumerals.exists_numeral hZ 256','PacketAffineAccepted.accepted_iff','theorem fold_iff','theorem nil_iff','theorem cons_bytes','theorem singleton_bytes'],
        'ObjectPacketBytesTrace':['TheoryTransport.sentence','ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Ordered byte fold forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Ordered byte fold proof drift: '+mod+': '+clause)
    for name,expected in [('fold_iff',{'hC'}),('domain',{'hb'}),('nil_fold',{'hw','hn','ht'}),('nil_iff',{'hw','hn'}),('cons_bytes',{'hw','hf','hc','ha'}),('singleton_bytes',{'hw','he','ht','hc','ha'})]:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts['PacketBytesLaws'])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Ordered byte fold hidden premise: '+name)
    upstream = (ROOT/'.lake/packages/YesMetaZFC/YesMetaZFC/Automation/ObjectPacketData.lean').read_text(encoding='utf-8')
    if 'input.foldr (fun byte rest => byte + 256 * rest) tail' not in upstream:
        raise RuntimeError('Locked original byte fold definition drift')
    schemas = ['packetBytesBothSequenceRowTransport', 'packetBytesBothSequenceLinksAppend', 'packetBytesOriginalDualSequenceAppend', 'packetBytesTraceExtensionWitnessesEliminated', 'packetBytesFullConsForwardAtRadix', 'packetBytesNilExactFiberAtRadix', 'packetBytesFoldOriginalValidityAndNaturalDomain', 'packetBytesActual256ExactGraphIff', 'packetBytesActualByteDomain', 'packetBytesActualNilExistsOnlyOmega', 'packetBytesActualNilIffOnlyOmega', 'packetBytesActualConsForwardOnlyOmega', 'packetBytesActualSingletonOnlyOmega']
    checks = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketBytesTrace.native_'+name not in checks: raise RuntimeError('Missing ordered byte fold fixture: '+name)
    return {'independent_dual_sequence_ordered_byte_fold_graph_constructed':True,
            'original_list_trace_and_value_sequence_share_every_internal_index':True,
            'each_step_real_Cons_and_bounded_affine_byte_equation':True,
            'full_old_rows_preserved_and_new_last_row_constructed':True,
            'original_pairing_union_sequence_append_operations_construct_both_graphs':True,
            'Nil_exact_fiber_keeps_internal_natural_tail_guard':True,
            'Cons_forward_closure_all_sequence_and_literal_witnesses_eliminated':True,
            'actual_256_Cons_closure_uses_actual_Packet_affine_acceptance_only_omega':True,
            'all_internal_and_nonstandard_trace_lengths_preserved':True,
            'full_internal_byte_fold_totality_uniqueness_proved':True,
            'reverse_Cons_decomposition_and_full_recursion_iff_proved':True,
            'canonical_varint_readTokens_byte_program_bridge_proved':False,
            'full_Basic_AST_schema_Proof_Con_proved':False}


def check_Packet_exact_ordered_byte_fold_recursion() -> dict:
    modules = ['PacketBytesRowRestrict', 'PacketBytesTracePrefix', 'PacketBytesRecursionSyntax', 'PacketBytesTerminal', 'PacketBytesDecomposition', 'PacketBytesRecursionEquation', 'PacketBytesRecursionBridge', 'PacketBytesRecursionLaws', 'ObjectPacketBytesRecursion']
    required = {
        'PacketBytesRowRestrict':['theorem row_restrict','theorem links_restrict','GodelPairArithmetic.successor_below','NaturalOrderBasic.below_successor','RestrictionEdges.restricted_edge','HornBinderRules.eliminate_many 6'],
        'PacketBytesTracePrefix':['SequencePrefix.exists_prefix','ZFContext.separation hZ RestrictionSyntax.matrix','ZFContext.separation hZ1 RestrictionSyntax.matrix','StructuralListTracePrefix.links_restrict','PacketBytesRowRestrict.links_restrict','theorem from_prefixes','theorem exists_prefix'],
        'PacketBytesRecursionSyntax':['def nilCase','Formula.mem t w','def terminalBody','def consBody','def caseAt','def actualBody','def criterion','PacketAffineAcceptedSyntax.accepted true','bytes (old 3 w) (slot 3 1) (old 3 t) (slot 3 2)','Derives.eqSubst'],
        'PacketBytesTerminal':['theorem of_row','OmegaUniversal.successor_unique','GraphProperties.single_valued','PacketAffineTransport.output','cons_output','theorem terminal_row'],
        'PacketBytesDecomposition':['theorem successor_case','PacketBytesTracePrefix.exists_prefix','theorem nil_trace_case','OmegaStructureAlgebra.decomposition_at','theorem trace_forward','theorem fold_forward','HornBinderRules.eliminate_many 6'],
        'PacketBytesRecursionEquation':['theorem cons_backward','PacketBytesTraceAppend.cons_fold','PacketBytesTraceBase.nil_fold','theorem backward','theorem fold_iff'],
        'PacketBytesRecursionBridge':['theorem cons_to_actual','theorem actual_to_cons','PacketAffineAccepted.accepted_iff','PacketBytesLaws.fold_at','theorem cases_iff'],
        'PacketBytesRecursionLaws':['SyntaxNumerals.exists_numeral hZ 256','PacketBytesLaws.fold_iff','PacketBytesRecursionEquation.fold_iff','PacketBytesRecursionBridge.cases_iff','OriginalUniversalBlock.allMany 3','theorem actual_iff','theorem all_law'],
        'ObjectPacketBytesRecursion':['TheoryTransport.sentence','ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Exact ordered byte recursion forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Exact ordered byte recursion proof drift: '+mod+': '+clause)
    for mod,name,expected in [('PacketBytesRecursionLaws','actual_iff',{'hw'}),('PacketBytesRecursionLaws','all_law',{'hw'}),('PacketBytesRecursionEquation','fold_iff',{'hw'}),('PacketBytesDecomposition','fold_forward',{'hw','hf'}),('PacketBytesRecursionBridge','cases_iff',{'hw','hC'})]:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Exact ordered byte recursion hidden premise: '+mod+'.'+name)
    schemas = ['packetBytesRecursionBothSequenceRowRestriction', 'packetBytesRecursionAllOldRowsRestriction', 'packetBytesRecursionFullDualPrefixFromActualRestrictions', 'packetBytesRecursionDualPrefixGraphsObjectEliminated', 'packetBytesRecursionCompleteTerminalRowNormalized', 'packetBytesRecursionTerminalWitnessesFromFullTrace', 'packetBytesRecursionSuccessorFullReverseDecomposition', 'packetBytesRecursionAllInternalTraceReverseDecomposition', 'packetBytesRecursionAllInternalFoldReverseDecomposition', 'packetBytesRecursionIndependentCriterionBackward', 'packetBytesRecursionExactAllInternalRadixRecursion', 'packetBytesRecursionActual256CriterionEquivalence', 'packetBytesRecursionActualBytesExactRecursionOnlyOmega', 'packetBytesRecursionAllInternalActualRecursionOnlyOmega']
    checks = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketBytesRecursion.native_'+name not in checks: raise RuntimeError('Missing exact byte recursion fixture: '+name)
    return {'both_original_Separation_prefix_graphs_constructed_and_eliminated':True,
            'all_old_byte_rows_preserved_under_both_actual_restrictions':True,
            'complete_terminal_row_normalized_by_both_original_sequence_functions':True,
            'internal_length_zero_successor_decomposition_no_external_standardness':True,
            'all_internal_numeric_candidates_exact_independent_recursive_iff':True,
            'real_byte_head_tail_and_intermediate_value_internally_bound':True,
            'unguarded_external_Cons_fields_not_assumed_natural':True,
            'Nil_exact_natural_tail_guard_preserved':True,
            'original_actual_Packet_affine_acceptance_preserved_in_recursive_criterion':True,
            'all_prefix_graph_terminal_and_radix_witnesses_object_eliminated':True,
            'final_ALL3_and_scalar_exact_recursion_require_only_omega':True,
            'full_internal_byte_fold_totality_uniqueness_proved':True,
            'canonical_varint_readTokens_byte_program_bridge_proved':False,
            'full_Basic_AST_schema_Proof_Con_proved':False}


def check_Packet_independent_valid_byte_input() -> dict:
    modules = ['PacketByteInputSyntax', 'PacketByteInputGraph', 'PacketByteInputBounds', 'PacketByteInputProperties', 'PacketByteInputRecursionSyntax', 'PacketByteInputDecomposition', 'PacketByteInputBridge', 'PacketByteInputLaws', 'ObjectPacketByteInput']
    required = {
        'PacketByteInputSyntax':['StructuralListEncodeSyntax.encoding','SequenceSyntax.bounded','def inputAt','def bounds','def byteList','SyntaxNumeralSyntax.numeral 256','theorem bounds_at'],
        'PacketByteInputGraph':['theorem graph_to_bounds','theorem bounds_to_graph','law_at','StructuralListFieldGraphFiber.exists_unique','theorem from_length_at','theorem length_iff'],
        'PacketByteInputBounds':['theorem empty_bounds','theorem cons_point','StructuralListFieldCons.zero_point','StructuralListFieldCons.successor_forward','StructuralListFieldCons.successor_backward','theorem head_bound','theorem tail_bounds','GodelPairArithmetic.successor_below'],
        'PacketByteInputProperties':['theorem at_length','StructuralListLengthUnique.unique','theorem nil_input','theorem cons_input','theorem typed_cons_inverse','StructuralListLengthRules.cons_predecessor','PacketByteInputGraph.from_length_at'],
        'PacketByteInputRecursionSyntax':['def consBody','def criterionAt','def actualBody','def criterion','byteList (old 2 w) (slot 2 1)','byte (slot 2 0)'],
        'PacketByteInputDecomposition':['StructuralListTraceInvert.valid_decomposition','PacketByteInputProperties.typed_cons_inverse','PacketByteInputProperties.cons_input','theorem forward','theorem backward','theorem input_iff'],
        'PacketByteInputBridge':['SyntaxNumerals.unique','theorem byte_at','theorem actual_at','theorem actual_iff_at','theorem cases_iff'],
        'PacketByteInputLaws':['SyntaxNumerals.range','SyntaxNumerals.exists_numeral hZ 256','theorem byte_natural','theorem valid','theorem actual_iff','theorem all_law','PacketByteInputDecomposition.input_iff'],
        'ObjectPacketByteInput':['TheoryTransport.sentence','ZFReplay.replay']}
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b|PacketBytesTraceSyntax\.bytes|PacketBytesLaws\.'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Independent byte input forbidden gap or execution dependence: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Independent byte input proof drift: '+mod+': '+clause)
    for mod,name,expected in [('PacketByteInputLaws','actual_iff',{'hw'}),('PacketByteInputLaws','all_law',{'hw'}),('PacketByteInputLaws','valid',{'hi'}),('PacketByteInputLaws','byte_natural',{'hw','hb'}),('PacketByteInputDecomposition','input_iff',{'hw','hC'}),('PacketByteInputProperties','typed_cons_inverse',{'hw','hh','ht','hc','hi'}),('PacketByteInputGraph','length_iff',{'hw'})]:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Independent byte input hidden premise: '+mod+'.'+name)
    schemas = ['packetByteInputCompleteFieldsToAllFieldBounds', 'packetByteInputAllFieldBoundsToActualGraph', 'packetByteInputOriginalGraphAndLengthBoundsIff', 'packetByteInputFullConsFieldBoundsForward', 'packetByteInputFirstActualFieldByteBound', 'packetByteInputAllSuccessorFieldsTailBounds', 'packetByteInputBoundsAtAnyActualLength', 'packetByteInputNilGuardConstructed', 'packetByteInputFullConsGuardConstructed', 'packetByteInputTypedConsHeadAndTailRecovered', 'packetByteInputAllInternalRadixGuardRecursion', 'packetByteInputActual256ExactGuardIff', 'packetByteInputActualByteNaturalOnlyOmega', 'packetByteInputActualGuardImpliesOriginalListValidity', 'packetByteInputActualGuardExactRecursionOnlyOmega', 'packetByteInputAllInternalActualGuardOnlyOmega']
    checks = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketByteInput.native_'+name not in checks: raise RuntimeError('Missing independent byte input fixture: '+name)
    return {'independent_input_guard_original_encoding_HasLength_full_Fields_and_bounded_range':True,
            'complete_graph_byte_bounds_iff_all_internal_pointwise_field_bounds':True,
            'actual_head_zero_field_and_successor_tail_fields_use_original_correspondence':True,
            'all_internal_Nil_Cons_input_guard_recursion_proved':True,
            'typed_Cons_auxiliaries_keep_natural_field_premises':True,
            'global_decomposition_derives_field_naturality_from_actual_valid_list':True,
            'full_length_field_graph_and_radix_witnesses_object_eliminated':True,
            'actual_256_guard_ALL1_requires_only_omega':True,
            'input_guard_definition_and_proofs_do_not_use_Bytes_execution':True,
            'nonstandard_lengths_and_invalid_candidates_remain_quantified':True,
            'full_internal_byte_fold_totality_uniqueness_proved':True,
            'canonical_varint_readTokens_byte_program_bridge_proved':False,
            'full_Basic_AST_schema_Proof_Con_proved':False}


def check_Packet_actual_byte_execution() -> dict:
    modules = ['PacketBytesExecutionSyntax', 'PacketBytesExecutionTransport', 'PacketBytesExecutionAffine', 'PacketBytesExecutionDescent', 'PacketBytesExecutionTotal', 'PacketBytesExecutionDomain', 'PacketBytesExecutionUniqueValues', 'PacketBytesExecutionUnique', 'PacketBytesExecutionInduction', 'PacketBytesExecutionFiberSyntax', 'PacketBytesExecution', 'ObjectPacketBytesExecution']
    required = {'PacketBytesExecutionSyntax': ['def matrix : Formula 2 := property 0 1', 'def property', 'def total', 'def domain', 'def unique', 'def earlier', 'OriginalUniversalBlock.allMany 3'], 'PacketBytesExecutionTransport': ['Derives.eqSubst', 'theorem input_subst', 'theorem affine_digit', 'theorem affine_tail'], 'PacketBytesExecutionAffine': ['SyntaxNumerals.exists_numeral hZ 256', 'PacketAffineCore.exists_value', 'PacketAffineCore.unique', 'PacketAffineAccepted.accepted_iff', 'theorem bytes_input_natural'], 'PacketBytesExecutionDescent': ['StructuralConsCore.components', 'PacketByteInputLaws.byte_natural', 'PacketBytesExecutionAffine.bytes_input_natural', 'earlier_at'], 'PacketBytesExecutionTotal': ['PacketBytesExecutionDescent.input_tail_property', 'PacketBytesExecutionAffine.exists_cell', 'PacketBytesLaws.cons_bytes', 'PacketBytesLaws.nil_fold', 'HornBinderRules.eliminate_many 2', 'theorem total_property'], 'PacketBytesExecutionDomain': ['PacketBytesExecutionDescent.accepted_tail_property', 'PacketBytesExecutionAffine.data', 'PacketByteInputRecursionSyntax.intro_actual_cons', 'PacketBytesRecursionLaws.actual_iff', 'HornBinderRules.eliminate_many 3', 'theorem domain_property'], 'PacketBytesExecutionUniqueValues': ['StructuralConsUnique.injective', 'StructuralConsUnique.disjoint', 'PacketBytesExecutionTransport.input_subst', 'PacketBytesExecutionTransport.affine_digit', 'PacketBytesExecutionTransport.affine_tail', 'PacketBytesExecutionAffine.unique_cell', 'theorem cases_unique'], 'PacketBytesExecutionUnique': ['PacketBytesRecursionLaws.actual_iff', 'PacketBytesLaws.nil_value', 'PacketBytesExecutionUniqueValues.nil_cons_false', 'PacketBytesExecutionUniqueValues.cases_unique', 'theorem unique_property'], 'PacketBytesExecutionInduction': ['BoundedInduction.induction_on_set PacketBytesExecutionSyntax.matrix', 'ZFContext.separation hZ PacketBytesExecutionSyntax.matrix.neg', '(ZFContext.arithmetic hZ).base.foundation', 'theorem all_properties', 'theorem exists_output', 'theorem input_domain', 'theorem output_unique'], 'PacketBytesExecutionFiberSyntax': ['def uniqueAt', 'def fiberBody', 'def fiber', 'def lawBody', 'def allLaw', 'OriginalUniversalBlock.allMany 2'], 'PacketBytesExecution': ['PacketBytesExecutionInduction.exists_output', 'PacketBytesExecutionInduction.input_domain', 'PacketBytesExecutionInduction.output_unique', 'theorem input_to_fiber', 'theorem fiber_to_input', 'theorem fiber_iff', 'theorem exists_iff', 'theorem all_law', 'theorem reject_input'], 'ObjectPacketBytesExecution': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    schemas = ['packetBytesExecutionActualCellData', 'packetBytesExecutionActualCellTotal', 'packetBytesExecutionActualCellUnique', 'packetBytesExecutionStrictInputTailProperty', 'packetBytesExecutionStrictAcceptedTailProperty', 'packetBytesExecutionTotalJointStep', 'packetBytesExecutionDomainJointStep', 'packetBytesExecutionUniqueJointStep', 'packetBytesExecutionAllJointProperties', 'packetBytesExecutionOutputExists', 'packetBytesExecutionActualInputDomain', 'packetBytesExecutionOutputUnique', 'packetBytesExecutionExistsDomainIff', 'packetBytesExecutionUniqueFiberIff', 'packetBytesExecutionAllInternalFiberDomain', 'packetBytesExecutionInvalidInputRejected']
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Actual byte execution forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Actual byte execution proof drift: '+mod+': '+clause)
    signatures = [('PacketBytesExecutionAffine', 'data', {'hw', 'hc'}), ('PacketBytesExecutionAffine', 'exists_cell', {'hw', 'hb', 'hu'}), ('PacketBytesExecutionAffine', 'unique_cell', {'hw', 'hb', 'ha'}), ('PacketBytesExecutionInduction', 'all_properties', {'hw'}), ('PacketBytesExecutionInduction', 'exists_output', {'hw', 'ht', 'hn'}), ('PacketBytesExecutionInduction', 'input_domain', {'hw', 'ha'}), ('PacketBytesExecutionInduction', 'output_unique', {'hw', 'hb', 'ha'}), ('PacketBytesExecution', 'fiber_iff', {'hw'}), ('PacketBytesExecution', 'exists_iff', {'hw'}), ('PacketBytesExecution', 'all_law', {'hw'}), ('PacketBytesExecution', 'reject_input', {'hw', 'hn'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Actual byte execution hidden premise: '+mod+'.'+name)
    checks = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketBytesExecution.native_'+name not in checks: raise RuntimeError('Missing actual byte execution fixture: '+name)
    return {'actual_Bytes_and_independent_ByteList_definitions_preserved': True, 'fixed_object_Formula2_joint_total_domain_unique_matrix': True, 'real_Cons_field_naturality_then_strict_tail_code_descent_derived': True, 'actual_256_affine_cell_domain_totality_uniqueness_literal_eliminated': True, 'existence_uses_actual_child_Bytes_and_full_real_cell': True, 'arbitrary_actual_Bytes_implies_independent_input_guard': True, 'all_candidate_output_uniqueness_two_actual_Cons_blocks_compared': True, 'original_Foundation_full_Separation_discharge_all_internal_joint_IH': True, 'unique_output_fiber_iff_independent_ByteList_and_natural_tail': True, 'final_ALL2_requires_only_omega_no_length_radix_graph_or_IH_premise': True, 'invalid_input_rejection_and_nonstandard_candidates_covered': True, 'original_host_bytes_foldr_canonical_sequence_bridge_proved': False, 'canonical_varint_readTokens_byte_program_bridge_proved': False, 'full_Basic_AST_schema_Proof_Con_proved': False}


def check_Packet_independent_varint_prefix_construction() -> dict:
    modules = ['PacketVarintCellSyntax', 'PacketVarintCell', 'PacketVarintRowSyntax', 'PacketVarintTraceSyntax', 'PacketVarintRowMap', 'PacketVarintTraceProperties', 'PacketVarintTraceTransport', 'PacketVarintTraceAppend', 'PacketVarintTraceBase', 'PacketVarintSyntax', 'PacketVarintDomain', 'PacketVarintConstruct', 'PacketVarintCellLaws', 'PacketVarintPrefixSyntax', 'PacketVarintPrefixDomain', 'PacketVarintPrefixConstruct', 'ObjectPacketVarintPrefix']
    required = {'PacketVarintCellSyntax': ['def terminal', 'StructuralListSyntax.nilCode w x', 'empty u', 'def continuation', '(empty u.castSucc).neg', 'PacketAffineSyntax.affine w.castSucc B.castSucc', 'NaturalAdditionSyntax.sum', 'def cell'], 'PacketVarintCell': ['theorem terminal_cell', 'theorem continuation_cell', 'NaturalAdditionCore.closure', 'PacketAffineCore.digit_natural'], 'PacketVarintRowSyntax': ['def rowAt', 'successor j i', 'StructuralListSyntax.consCode w h x y', 'PacketVarintCellSyntax.cell w C x h u v', 'existsMany 6'], 'PacketVarintTraceSyntax': ['StructuralListTraceSyntax.trace w z e l d f n', 'SequenceSyntax.sequence g d w', 'edge g z t', 'edge g l a', 'links w C l f g', 'def foldAt'], 'PacketVarintRowMap': ['edgeIncluded f F', 'edgeIncluded g G', 'theorem row_map', 'theorem append_links', 'HornBinderRules.eliminate_many 6'], 'PacketVarintTraceProperties': ['theorem list_trace', 'theorem value_sequence', 'theorem length', 'theorem valid', 'SequenceSyntax.bounded_at'], 'PacketVarintTraceTransport': ['Derives.eqSubst', 'theorem input_subst', 'theorem radix_subst'], 'PacketVarintTraceAppend': ['StructuralListTraceAppend.from_append', 'SequenceAppend.exists_append', 'PacketVarintRowMap.append_links', 'PacketVarintCell.head_natural', 'PacketVarintCell.output_guard', 'theorem cons_fold'], 'PacketVarintTraceBase': ['StructuralListTraceBase.exists_base', 'SequenceAppend.exists_append', 'StructuralListUnits.with_units', 'GraphProperties.single_valued', 'theorem nil_iff'], 'PacketVarintSyntax': ['def canonicalAt', 'empty (Fin.last m)', 'foldAt w.castSucc B.castSucc s.castSucc (Fin.last m) n.castSucc', '(StructuralListSyntax.nilCode w.castSucc s.castSucc).neg', 'SyntaxNumeralSyntax.numeral 128', 'def canonical'], 'PacketVarintDomain': ['theorem at_domain', 'theorem domain', 'SyntaxNumerals.unique', 'theorem actual_iff', 'theorem reject_nil'], 'PacketVarintConstruct': ['SyntaxNumerals.exists_numeral hZ 0', 'PacketVarintTraceBase.nil_fold', 'PacketVarintTraceAppend.cons_fold', 'PacketVarintCell.terminal_cell', 'PacketVarintCell.continuation_cell', 'StructuralConsUnique.disjoint', 'theorem terminal', 'theorem continuation'], 'PacketVarintCellLaws': ['theorem continuation_nonzero', 'theorem terminal_continuation_disjoint', 'theorem zero_forces_terminal', 'theorem nonempty_previous_forces_continuation', 'PacketTokenByteBounds.small_digit_byte', 'PacketTokenByteBounds.shifted_digit_byte', 'theorem cell_byte_bound'], 'PacketVarintPrefixSyntax': ['def prefixCode', 'canonical w.castSucc n.castSucc (Fin.last m)', 'PacketBytesTraceSyntax.bytes w.castSucc (Fin.last m) t.castSucc a.castSucc', 'theorem intro_prefix'], 'PacketVarintPrefixDomain': ['PacketVarintDomain.domain', 'PacketBytesLaws.domain', 'theorem domain'], 'PacketVarintPrefixConstruct': ['StructuralConsCore.exists_cons', 'StructuralListUnits.with_units', 'PacketVarintConstruct.terminal', 'PacketVarintConstruct.continuation', 'PacketBytesLaws.singleton_bytes', 'PacketBytesLaws.cons_bytes', 'theorem terminal', 'theorem continuation'], 'ObjectPacketVarintPrefix': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    schemas = ['packetVarintTerminalCellConstructed', 'packetVarintNonzeroContinuationCellConstructed', 'packetVarintContinuationRequiresNonzeroValue', 'packetVarintTerminalContinuationDisjoint', 'packetVarintZeroPriorForcesActualTerminal', 'packetVarintNonemptyListForcesActualContinuation', 'packetVarintEveryActualCellByteBound', 'packetVarintBothOriginalGraphsRowTransport', 'packetVarintFullOldRowsAndNewLastRowPreserved', 'packetVarintRealDualSequenceExtension', 'packetVarintEmptyTraceExactNaturalSeed', 'packetVarintIndependentCanonicalAtDomain', 'packetVarintIndependentActualCanonicalDomain', 'packetVarintActual128ExactGraphIff', 'packetVarintCanonicalTerminalActualGraphs', 'packetVarintCanonicalNonzeroContinuationActualGraphs', 'packetVarintCanonicalRejectsActualNil', 'packetVarintIndependentPrefixExactNumericDomain', 'packetVarintTerminalPrefixAllCodeWitnessesEliminated', 'packetVarintContinuationPrefixAllCodeWitnessesEliminated']
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b|PacketTokenAcceptedSyntax|PacketTokenArithmeticEquation|PacketTraceSyntax\.condition'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Independent varint prefix forbidden gap or Tok dependence: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Independent varint prefix proof drift: '+mod+': '+clause)
    for mod in ['PacketVarintCellSyntax','PacketVarintRowSyntax','PacketVarintTraceSyntax','PacketVarintSyntax']:
        if 'PacketBytesTraceSyntax.bytes' in texts[mod]: raise RuntimeError('Canonical graph definition depends on byte execution: '+mod)
    signatures = [('PacketVarintTraceAppend', 'cons_fold', {'hw', 'hf', 'hc', 'ha'}), ('PacketVarintTraceBase', 'nil_iff', {'hw', 'hn'}), ('PacketVarintDomain', 'at_domain', {'hc'}), ('PacketVarintDomain', 'domain', {'hc'}), ('PacketVarintDomain', 'actual_iff', {'hB'}), ('PacketVarintConstruct', 'terminal', {'hs', 'hn', 'he', 'hw', 'hB'}), ('PacketVarintConstruct', 'continuation', {'hq', 'hf', 'hp', 'hw', 'hs', 'ha', 'hB'}), ('PacketVarintCellLaws', 'cell_byte_bound', {'hw', 'hC', 'hB', 'hc'}), ('PacketVarintPrefixDomain', 'domain', {'hp'}), ('PacketVarintPrefixConstruct', 'terminal', {'hw', 'ha', 'hB', 'hn'}), ('PacketVarintPrefixConstruct', 'continuation', {'hq', 'hf', 'hw', 'hn', 'hs', 'ha', 'hB'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Independent varint prefix hidden premise: '+mod+'.'+name)
    upstream = (ROOT/'.lake/packages/YesMetaZFC/YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/NatPacket.lean').read_text(encoding='utf-8')
    for clause in ['if scale != 1 && byte == 0 then none','else (value % 128 + 128) :: varint (value / 128)','readTokens rest 0 1 ((value + byte * scale) :: acc)']:
        if clause not in upstream: raise RuntimeError('Original canonical byte program drift: '+clause)
    checks = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketVarintPrefix.native_'+name not in checks: raise RuntimeError('Missing independent varint prefix fixture: '+name)
    return {'independent_canonical_definition_no_Tok_acceptance_or_answer_predicate': True, 'actual_original_list_and_numeric_sequence_share_every_internal_index': True, 'terminal_cell_requires_Nil_prior_list_zero_prior_value_and_low_digit': True, 'continuation_cell_requires_nonzero_prior_value_and_shifted_base128_digit': True, 'terminal_continuation_disjoint_and_zero_prior_forces_terminal': True, 'actual_128_256_arithmetic_proves_each_cell_byte_bound': True, 'original_pairing_union_append_construct_both_graphs_and_preserve_all_old_rows': True, 'canonical_graph_zero_seed_and_nonempty_original_list_preserved': True, 'real_terminal_and_continuation_graph_closure_proved': True, 'independent_prefix_uses_actual_Bytes_with_exact_remaining_numeric_tail': True, 'prefix_terminal_and_continuation_all_actual_code_witnesses_eliminated': True, 'nonstandard_lengths_and_invalid_candidates_preserved': True, 'exact_reverse_canonical_recursion_proved': True, 'full_all_internal_canonical_totality_uniqueness_byte_domain_proved': True, 'actual_Tok_iff_independent_canonical_prefix_proved': True, 'original_varint_readTokens_program_bridge_proved': False, 'full_Basic_AST_schema_Proof_Con_proved': False}


def check_Packet_exact_canonical_varint_recursion() -> dict:
    modules = ['PacketVarintRowRestrict', 'PacketVarintTracePrefix', 'PacketVarintRecursionSyntax', 'PacketVarintTerminal', 'PacketVarintDecomposition', 'PacketVarintRecursionEquation', 'PacketVarintCanonicalRecursionSyntax', 'PacketVarintCanonicalPieces', 'PacketVarintCanonicalDecomposition', 'PacketVarintCanonicalRecursionEquation', 'PacketVarintCanonicalRecursionBridge', 'PacketVarintCanonicalRecursionLaws', 'ObjectPacketVarintRecursion']
    required = {'PacketVarintRowRestrict': ['theorem row_restrict', 'theorem links_restrict', 'GodelPairArithmetic.successor_below', 'NaturalOrderBasic.below_successor', 'RestrictionEdges.restricted_edge', 'HornBinderRules.eliminate_many 6'], 'PacketVarintTracePrefix': ['SequencePrefix.exists_prefix', 'ZFContext.separation hZ RestrictionSyntax.matrix', 'ZFContext.separation hZ1 RestrictionSyntax.matrix', 'StructuralListTracePrefix.links_restrict', 'PacketVarintRowRestrict.links_restrict', 'theorem exists_prefix'], 'PacketVarintRecursionSyntax': ['def nilCase', 'def terminalBody', 'def consBody', 'PacketVarintCellSyntax.cell (old 3 w) (old 3 C) (slot 3 1)', 'def caseAt', 'theorem cell_output', 'Derives.eqSubst'], 'PacketVarintTerminal': ['OmegaUniversal.successor_unique', 'GraphProperties.single_valued', 'cell_output', 'cons_output', 'theorem terminal_row'], 'PacketVarintDecomposition': ['PacketVarintTracePrefix.exists_prefix', 'OmegaStructureAlgebra.decomposition_at', 'theorem successor_case', 'theorem nil_trace_case', 'theorem trace_forward', 'theorem fold_forward'], 'PacketVarintRecursionEquation': ['PacketVarintTraceAppend.cons_fold', 'PacketVarintTraceBase.nil_fold', 'theorem backward', 'theorem fold_iff'], 'PacketVarintCanonicalRecursionSyntax': ['def singleton', 'def smallCase', 'def recursiveInput', '| false => canonicalAt', '| true => canonical', 'def largeBody', '(empty (slot 4 1)).neg', 'def criterion', 'def allLaw', 'OriginalUniversalBlock.allMany 2'], 'PacketVarintCanonicalPieces': ['theorem cons_head', 'Derives.eqSubst', 'theorem nonempty_suffix', 'PacketVarintTraceBase.nil_value', 'NaturalMultiplicationLaws.empty_subst', 'mem_subst', 'theorem terminal_point'], 'PacketVarintCanonicalDecomposition': ['PacketVarintCanonicalPieces.nonempty_suffix', 'intro_at', 'intro_large false', 'PacketVarintDecomposition.fold_forward', 'theorem continuation_point', 'theorem cons_case', 'theorem at_forward'], 'PacketVarintCanonicalRecursionEquation': ['PacketVarintConstruct.terminal_at', 'PacketVarintConstruct.continuation_at', 'theorem small_backward', 'theorem large_backward', 'theorem at_iff'], 'PacketVarintCanonicalRecursionBridge': ['intro_actual', 'PacketVarintDomain.at_radix', 'theorem large_iff', 'SyntaxNumerals.range hZ 128', 'theorem at_actual_iff'], 'PacketVarintCanonicalRecursionLaws': ['intro_criterion', 'intro_actual', 'PacketVarintCanonicalRecursionBridge.at_actual_iff', 'theorem actual_iff', 'theorem all_law'], 'ObjectPacketVarintRecursion': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    schemas = ['packetVarintRecursionBothGraphsFullOldRowRestriction', 'packetVarintRecursionBothGraphsAllOldLinksRestriction', 'packetVarintRecursionActualPrefixGraphsConstructedAndEliminated', 'packetVarintRecursionCompleteActualLastRowNormalized', 'packetVarintRecursionAllInternalRawFoldReverseDecomposition', 'packetVarintRecursionAllInternalRawFoldExactRecursion', 'packetVarintRecursionNonzeroValueForcesActualNonemptySuffix', 'packetVarintRecursionCanonicalTerminalHeadAligned', 'packetVarintRecursionAllInternalCanonicalReverseDecomposition', 'packetVarintRecursionExactCanonicalRecursionAtNaturalRadix', 'packetVarintRecursionActual128CompleteSmallerGraphAlignment', 'packetVarintRecursionActual128CanonicalExactRecursion', 'packetVarintRecursionActualCanonicalExactRecursionOnlyOmega', 'packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmega']
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b|PacketTokenAcceptedSyntax|PacketTokenArithmeticEquation|PacketTraceSyntax\.condition|PacketBytesTraceSyntax\.bytes'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Exact canonical varint recursion forbidden gap or execution dependence: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Exact canonical varint recursion proof drift: '+mod+': '+clause)
    signatures = [('PacketVarintTerminal', 'terminal_row', {'ht', 'hs'}), ('PacketVarintRecursionEquation', 'fold_iff', {'hw'}), ('PacketVarintCanonicalPieces', 'nonempty_suffix', {'hw', 'hq', 'hf', 'hz'}), ('PacketVarintCanonicalDecomposition', 'at_forward', {'hw', 'hc'}), ('PacketVarintCanonicalRecursionEquation', 'at_iff', {'hw', 'hB'}), ('PacketVarintCanonicalRecursionBridge', 'at_actual_iff', {'hw', 'hB'}), ('PacketVarintCanonicalRecursionLaws', 'actual_iff', {'hw'}), ('PacketVarintCanonicalRecursionLaws', 'all_law', {'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Exact canonical varint recursion hidden premise: '+mod+'.'+name)
    checks = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketVarintRecursion.native_'+name not in checks: raise RuntimeError('Missing exact canonical varint recursion fixture: '+name)
    return {'independent_canonical_and_raw_graph_definitions_preserved': True, 'both_original_Separation_prefix_graphs_constructed_and_eliminated': True, 'all_old_rows_preserved_in_both_actual_restrictions': True, 'complete_terminal_row_normalized_by_both_sequence_functions': True, 'all_internal_raw_fold_exact_Nil_Cons_recursive_iff': True, 'canonical_terminal_head_aligned_by_original_equality': True, 'nonzero_suffix_value_and_zero_seed_prove_actual_nonempty_suffix': True, 'full_four_witness_continuation_branch_contains_smaller_independent_canonical_graph': True, 'actual_128_numeral_uniqueness_aligns_smaller_graphs_both_directions': True, 'all_zero_prefix_row_and_radix_witnesses_object_eliminated': True, 'final_scalar_and_ALL2_exact_canonical_recursion_require_only_omega': True, 'external_Bool_selects_two_fixed_AST_presentations_only': True, 'nonstandard_internal_lengths_and_invalid_candidates_preserved': True, 'full_all_internal_canonical_totality_uniqueness_byte_domain_proved': True, 'actual_Tok_iff_independent_canonical_prefix_proved': True, 'original_varint_readTokens_program_bridge_proved': False, 'full_Basic_AST_schema_Proof_Con_proved': False}


def check_Packet_canonical_varint_execution() -> dict:
    modules = ['PacketVarintExecutionSyntax', 'PacketVarintExecutionHelpers', 'PacketVarintExecutionTotal', 'PacketVarintExecutionDomain', 'PacketVarintExecutionUniqueValues', 'PacketVarintExecutionUniqueCases', 'PacketVarintExecutionUnique', 'PacketVarintExecutionInduction', 'PacketVarintExecutionLiterals', 'PacketVarintExecutionFiberSyntax', 'PacketVarintExecution', 'ObjectPacketVarintExecution']
    required = {'PacketVarintExecutionSyntax': ['def existsList', 'def domain', 'def unique', 'def property', 'def matrix : Formula 2 := property 0 1', 'def earlier', 'canonical w.castSucc n.castSucc (Fin.last m)', 'OriginalUniversalBlock.allMany 2'], 'PacketVarintExecutionHelpers': ['PacketDivisionDescentCore.quotient_bounds hZ false', 'earlier_at', 'PacketVarintDomain.at_radix', 'Derives.eqSubst', 'theorem cons_input', 'PacketByteInputLaws.actual_iff'], 'PacketVarintExecutionTotal': ['StructuralListUnits.with_units', 'StructuralConsCore.exists_cons', 'PacketDivisionInduction.exists_decomposition hZ false', 'ZFArithmetic.add_exists', 'PacketVarintConstruct.terminal', 'PacketVarintConstruct.continuation', 'PacketVarintExecutionHelpers.below_property', 'theorem point'], 'PacketVarintExecutionDomain': ['PacketTokenByteBounds.small_digit_byte', 'PacketTokenByteBounds.shifted_digit_byte', 'intro_byte', 'domain_at', 'PacketVarintExecutionHelpers.below_property', 'PacketVarintExecutionHelpers.cons_input', 'theorem domain_property'], 'PacketVarintExecutionUniqueValues': ['PacketDivisionUnique.unique', 'unique_at', 'ZFArithmetic.add_unique', 'StructuralConsUnique.unique', 'StructuralNil.unique', 'PacketDivisionDescentCore.terminal_iff', 'theorem values'], 'PacketVarintExecutionUniqueCases': ['theorem small_cases', 'theorem large_cases', 'HornBinderRules.eliminate_many 4', 'PacketVarintExecutionUniqueValues.values', 'canonical_rename', 'NaturalAdditionSyntax.sum_rename'], 'PacketVarintExecutionUnique': ['PacketVarintExecutionHelpers.cases_at', 'PacketVarintExecutionUniqueValues.large_not_small', 'PacketVarintExecutionUniqueCases.large_cases', 'PacketVarintExecutionUniqueCases.small_cases', 'theorem unique_property'], 'PacketVarintExecutionInduction': ['BoundedInduction.induction_on_set PacketVarintExecutionSyntax.matrix', 'ZFContext.separation hZ PacketVarintExecutionSyntax.matrix.neg', '(ZFContext.arithmetic hZ).base.foundation', 'theorem property_from_earlier', 'theorem all_properties_at'], 'PacketVarintExecutionLiterals': ['SyntaxNumerals.exists_numeral hZ 128', 'SyntaxNumerals.exists_numeral hZ1 256', 'theorem all_properties', 'theorem exists_list', 'theorem byte_input', 'theorem list_unique'], 'PacketVarintExecutionFiberSyntax': ['def uniqueAt', 'def fiberBody', 'def fiber', 'byteList w.castSucc (Fin.last m)', 'def allLaw'], 'PacketVarintExecution': ['PacketVarintExecutionLiterals.exists_list', 'PacketVarintExecutionLiterals.byte_input', 'PacketVarintExecutionLiterals.list_unique', 'theorem fiber_iff', 'theorem exists_iff', 'theorem all_law'], 'ObjectPacketVarintExecution': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    schemas = ['packetVarintExecutionStrictQuotientAuthorizesJointIH', 'packetVarintExecutionActualSmallListConstructed', 'packetVarintExecutionActualRecursiveListConstructed', 'packetVarintExecutionExistenceJointStep', 'packetVarintExecutionAllActualCandidatesByteGuardJointStep', 'packetVarintExecutionAllActualCandidateListsUniqueJointStep', 'packetVarintExecutionJointPropertyStep', 'packetVarintExecutionOriginalFoundationSeparationAllJointIHDischarged', 'packetVarintExecutionAllJointPropertiesOnlyOmega', 'packetVarintExecutionActualListExistsOnlyOmega', 'packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuard', 'packetVarintExecutionEveryActualCanonicalCandidateListUnique', 'packetVarintExecutionExistenceExactNaturalDomain', 'packetVarintExecutionUniqueByteListFiberExactNaturalDomain', 'packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmega']
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b|PacketTokenAcceptedSyntax|PacketTokenArithmeticEquation|PacketTraceSyntax\.condition|PacketBytesTraceSyntax\.bytes'
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Canonical varint execution forbidden gap or Tok dependence: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Canonical varint execution proof drift: '+mod+': '+clause)
    signatures = [('PacketVarintExecutionHelpers', 'below_property', {'hq', 'ha', 'hi', 'hw', 'hB'}), ('PacketVarintExecutionTotal', 'point', {'hB', 'hi', 'hw', 'hn'}), ('PacketVarintExecutionDomain', 'point', {'hC', 'hc', 'hi', 'hw', 'hB'}), ('PacketVarintExecutionUnique', 'point', {'hB', 'ht', 'hi', 'hw', 'hs'}), ('PacketVarintExecutionInduction', 'all_properties_at', {'hC', 'hw', 'hB'}), ('PacketVarintExecutionLiterals', 'all_properties', {'hw'}), ('PacketVarintExecutionLiterals', 'exists_list', {'hw', 'hn'}), ('PacketVarintExecutionLiterals', 'byte_input', {'hc', 'hw'}), ('PacketVarintExecutionLiterals', 'list_unique', {'ht', 'hw', 'hs'}), ('PacketVarintExecution', 'fiber_iff', {'hw'}), ('PacketVarintExecution', 'all_law', {'hw'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Canonical varint execution hidden premise: '+mod+'.'+name)
    checks = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketVarintExecution.native_'+name not in checks: raise RuntimeError('Missing canonical varint execution fixture: '+name)
    return {'independent_Canonical_and_ByteList_definitions_preserved': True, 'fixed_Formula2_joint_existence_every_candidate_byte_domain_and_list_unique': True, 'actual_strict_base128_quotient_bounds_authorize_every_smaller_IH': True, 'real_Nil_Cons_addition_and_canonical_list_witnesses_constructed_and_eliminated': True, 'every_actual_canonical_candidate_has_full_independent_ByteList_guard': True, 'two_full_EX4_branches_division_digit_quotient_sum_suffix_and_Cons_aligned': True, 'all_four_terminal_continuation_combinations_handled': True, 'original_Foundation_full_Separation_discharge_all_joint_IH': True, 'internal_128_256_witnesses_constructed_and_object_eliminated': True, 'canonical_unique_byte_list_fiber_has_exact_internal_natural_value_domain': True, 'final_ALL1_and_scalar_interfaces_require_only_omega': True, 'all_invalid_and_nonstandard_candidates_remain_quantified': True, 'only_Canonical_implies_ByteList_no_converse_asserted': True, 'actual_Tok_iff_independent_canonical_prefix_proved': True, 'original_varint_readTokens_program_bridge_proved': False, 'full_Basic_AST_schema_Proof_Con_proved': False}


def check_Packet_actual_token_canonical_prefix_agreement() -> dict:
    modules = ['PacketBytesConsSyntax', 'PacketBytesCons', 'PacketVarintPrefixRecursionSyntax', 'PacketVarintPrefixSmall', 'PacketVarintPrefixLarge', 'PacketVarintPrefixEquation', 'PacketTokenCanonicalSyntax', 'PacketTokenCanonicalStep', 'PacketTokenCanonicalInduction', 'PacketTokenCanonicalLiterals', 'PacketTokenCanonicalLaws', 'ObjectPacketTokenCanonical']
    required = {'PacketBytesConsSyntax': ['def remaining', 'bytes w.castSucc x.castSucc t.castSucc', 'PacketAffineAcceptedSyntax.accepted true', 'theorem intro_remaining'], 'PacketBytesCons': ['PacketByteInputLaws.byte_natural', 'PacketBytesExecutionAffine.bytes_input_natural', 'StructuralConsUnique.injective', 'PacketBytesExecutionTransport.input_subst', 'PacketBytesExecutionTransport.affine_digit', 'PacketBytesExecutionTransport.affine_tail', 'theorem cons_iff', 'theorem singleton'], 'PacketVarintPrefixRecursionSyntax': ['def smallCase', 'def largeBody', 'prefixCode (old 4 w) (slot 4 1) (old 4 t) (slot 4 2)', 'def criterion', 'def allLaw', 'OriginalUniversalBlock.allMany 3'], 'PacketVarintPrefixSmall': ['PacketBytesCons.singleton', 'PacketAffineAccepted.accepted_iff', 'theorem forward'], 'PacketVarintPrefixLarge': ['PacketBytesCons.forward', 'PacketVarintExecutionHelpers.list_natural', 'PacketVarintPrefixSyntax.intro_prefix', 'PacketAffineAccepted.accepted_iff', 'theorem forward'], 'PacketVarintPrefixEquation': ['PacketVarintExecutionHelpers.cases_at', 'PacketVarintPrefixSmall.forward', 'PacketVarintPrefixLarge.forward', 'PacketVarintPrefixConstruct.terminal', 'PacketVarintPrefixConstruct.continuation', 'theorem prefix_iff', 'theorem all_law'], 'PacketTokenCanonicalSyntax': ['def agreement', 'PacketTokenAcceptedSyntax.accepted w n t a', 'prefixCode w n t a', 'def property', 'def matrix : Formula 2 := property 0 1', 'def earlier', 'OriginalUniversalBlock.allMany 2', 'OriginalUniversalBlock.allMany 3'], 'PacketTokenCanonicalStep': ['PacketDivisionDescentCore.quotient_bounds hZ false', 'earlier_at', 'PacketTokenArithmeticSyntax.intro_large', 'PacketVarintPrefixRecursionSyntax.intro_large', 'PacketTokenArithmeticEquation.accepted_iff', 'PacketVarintPrefixEquation.prefix_iff', 'theorem property_step'], 'PacketTokenCanonicalInduction': ['BoundedInduction.induction_on_set PacketTokenCanonicalSyntax.matrix', 'ZFContext.separation hZ PacketTokenCanonicalSyntax.matrix.neg', '(ZFContext.arithmetic hZ).base.foundation', 'theorem all_properties_at'], 'PacketTokenCanonicalLiterals': ['SyntaxNumerals.exists_numeral hZ 128', 'SyntaxNumerals.exists_numeral hZ1 256', 'theorem all_properties', 'theorem at_code'], 'PacketTokenCanonicalLaws': ['PacketTokenAcceptedNatural.accepted_environment', 'PacketVarintPrefixDomain.domain', 'theorem actual_iff', 'theorem all_law', 'PacketVarintExecutionLiterals.list_unique', 'theorem at_canonical_list'], 'ObjectPacketTokenCanonical': ['TheoryTransport.sentence', 'ZFReplay.replay']}
    schemas = ['packetTokenCanonicalGivenConsExactByteTailIff', 'packetTokenCanonicalActualSingletonLastCellNormalized', 'packetTokenCanonicalIndependentPrefixExactArithmeticRecursion', 'packetTokenCanonicalAllInternalIndependentPrefixRecursion', 'packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIH', 'packetTokenCanonicalFullOriginalAndIndependentCriteriaAgree', 'packetTokenCanonicalWholeActualTokenPrefixAgreementStep', 'packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischarged', 'packetTokenCanonicalAllAgreementPropertiesOnlyOmega', 'packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmega', 'packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmega', 'packetTokenCanonicalPrefixAtAnyActualCanonicalList', 'packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalList']
    texts = {}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    independent_modules = ['PacketBytesConsSyntax','PacketBytesCons','PacketVarintPrefixRecursionSyntax','PacketVarintPrefixSmall','PacketVarintPrefixLarge','PacketVarintPrefixEquation']
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden,text): raise RuntimeError('Actual Tok canonical prefix forbidden gap: '+mod)
        if mod in independent_modules and re.search(r'PacketTokenAcceptedSyntax|PacketTokenArithmeticSyntax|PacketTokenArithmeticEquation|PacketTokenCanonical',text):
            raise RuntimeError('Independent Prefix recursion depends on Tok: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Actual Tok canonical prefix proof drift: '+mod+': '+clause)
    signatures = [('PacketBytesCons', 'cons_iff', {'hx', 'hh', 'hw', 'hc'}), ('PacketBytesCons', 'forward', {'hb', 'hx', 'hh', 'hw', 'hc'}), ('PacketVarintPrefixEquation', 'prefix_iff', {'hC', 'hw', 'hB'}), ('PacketTokenCanonicalStep', 'below_agreement', {'ha', 'hq', 'hi', 'hw', 'hB'}), ('PacketTokenCanonicalStep', 'point', {'hw', 'hi', 'hC', 'hB'}), ('PacketTokenCanonicalInduction', 'all_properties_at', {'hC', 'hw', 'hB'}), ('PacketTokenCanonicalLiterals', 'all_properties', {'hw'}), ('PacketTokenCanonicalLaws', 'actual_iff', {'hw'}), ('PacketTokenCanonicalLaws', 'all_law', {'hw'}), ('PacketTokenCanonicalLaws', 'at_canonical_list', {'hw', 'hc'})]
    for mod,name,expected in signatures:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)',texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Actual Tok canonical prefix hidden premise: '+mod+'.'+name)
    checks = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketTokenCanonical.native_'+name not in checks: raise RuntimeError('Missing actual Tok canonical prefix fixture: '+name)
    return {'original_Tok_Canonical_Bytes_and_independent_Prefix_definitions_preserved': True, 'given_actual_Cons_Bytes_exact_tail_execution_bidirectional': True, 'real_field_naturality_and_original_Cons_injectivity_align_actual_witnesses': True, 'independent_Prefix_exact_arithmetic_recursion_for_all_internal_candidates': True, 'full_EX4_original_and_independent_branches_keep_all_arithmetic_guards': True, 'fixed_Formula2_compares_all_internal_tails_and_outputs': True, 'actual_strict_quotient_descent_precedes_each_smaller_agreement_IH': True, 'original_Foundation_full_Separation_discharge_all_comparison_IH': True, 'actual_128_256_and_internal_code_tail_cell_witnesses_object_eliminated': True, 'actual_Tok_iff_independent_canonical_prefix_proved': True, 'final_scalar_and_ALL3_agreement_require_only_omega': True, 'invalid_input_naturality_derived_from_actual_Tok_or_Prefix': True, 'actual_Tok_iff_Bytes_at_every_given_actual_canonical_list': True, 'original_varint_readTokens_program_bridge_proved': False, 'full_Basic_AST_schema_Proof_Con_proved': False}


def check_Packet_raw_reader_local_step() -> dict:
    modules = ['PacketReaderStepSyntax', 'PacketReaderGuards', 'PacketReaderArithmetic', 'PacketReaderContinuation', 'PacketReaderEmission', 'PacketReaderStep', 'PacketReaderStepExistence', 'ObjectPacketReaderStep']
    schemas = ['packetReaderRawGuardPartition', 'packetReaderTerminalRejectionNoStep', 'packetReaderEofExactGuardPartition', 'packetReaderUnboundedValueUpdateExists', 'packetReaderUnboundedValueUpdateRange', 'packetReaderContinuationExactNaturalDomain', 'packetReaderContinuationJointUnique', 'packetReaderContinuationActualExists', 'packetReaderEmissionActualConsExists', 'packetReaderEmissionActualConsUnique', 'packetReaderEmissionValidAccumulator', 'packetReaderLocalStepStatePreserved', 'packetReaderLocalStepJointUnique', 'packetReaderLocalStepExactSuccessorDomain', 'packetReaderOriginalLiteralLocalSuccessorDomain']
    required = {
        'PacketReaderStepSyntax': ['def state', 'StructuralListTraceSyntax.valid w l', 'def finish', '(Formula.equal s o).disj (Formula.equal b z).neg', 'def reject', 'def more', 'def eof', '(Formula.equal s o).conj (.equal v z)', 'def emission', 'consCode w.castSucc (Fin.last m) a.castSucc c.castSucc', 'def continuation', 'sum w.castSucc B.castSucc (Fin.last m) b.castSucc', 'product w.castSucc s.castSucc B.castSucc q.castSucc', 'def emitCase', 'def continueCase', 'def step'],
        'PacketReaderGuards': ['NaturalOrderBasic.compare', 'SourcePropositional.by_cases', 'theorem finish_reject_disjoint', 'theorem reject_no_step', 'NaturalOrderBasic.below_not_reverse'],
        'PacketReaderArithmetic': ['theorem exists_equation', 'mul_exists', 'add_exists', 'theorem equation_range', 'theorem equation_digit'],
        'PacketReaderContinuation': ['NaturalDifference.exists_of_below', 'NaturalDifference.unique', 'PacketAffineCore.equation_unique', 'ZFArithmetic.mul_unique', 'theorem exists_update', 'theorem domain'],
        'PacketReaderEmission': ['StructuralConsCore.exists_cons', 'StructuralListValidity.cons_valid', 'StructuralConsUnique.unique', 'PacketVarintCanonicalPieces.cons_head'],
        'PacketReaderStep': ['theorem domain', 'theorem unique', 'PacketReaderGuards.low_more_disjoint', 'PacketReaderEmission.unique', 'PacketReaderContinuation.unique'],
        'PacketReaderStepExistence': ['existsMany 4', 'theorem domain_iff', 'theorem exists_of_not_reject', 'theorem reject_no_result', 'HornBinderRules.eliminate_many 4', 'PacketReaderGuards.partition'],
        'ObjectPacketReaderStep': ['TheoryTransport.sentence', 'ZFReplay.replay', 'SyntaxNumeralSyntax.numeral 128 B', 'SyntaxNumeralSyntax.numeral 0 z', 'SyntaxNumeralSyntax.numeral 1 o', 'SyntaxNumerals.range hZ 128 w B', 'SyntaxNumerals.range hZ 0 w z', 'SyntaxNumerals.range hZ 1 w o']}
    forbidden = r'Expr\.eval|Classical\.choose|\b(sorry|admit|unsafe|native_decide|induction)\b|(?<!\.)\baxiom\b|Nat\.strongRec|WellFounded\.fix|set_option|\bModel\b'
    texts = {}
    for mod in modules:
        text = strip_comments((ROOT/'PPAC/Migration/Internal'/(mod+'.lean')).read_text(encoding='utf-8'))
        if re.search(forbidden, text): raise RuntimeError('Raw reader forbidden gap: '+mod)
        texts[mod] = text
        for clause in required[mod]:
            if clause not in text: raise RuntimeError('Raw reader proof drift: '+mod+': '+clause)
    for mod,name,expected in [('PacketReaderStep','unique',{'hw','hB','hb','hi','hc','hd'}),('PacketReaderStep','domain',{'hw','hB','hz','ho','hi','hh'}),('PacketReaderStepExistence','domain_iff',{'hw','hB','hz','ho','hb','hi'}),('PacketReaderArithmetic','exists_equation',{'hw','hb','hv','hs'})]:
        h = re.search(r'(?ms)^theorem '+name+r'\b.*?(?=:=)', texts[mod])
        if not h or set(re.findall(r'\((\w+)\s*:\s*Derives Γ \(',h.group(0))) != expected:
            raise RuntimeError('Raw reader hidden premise: '+mod+'.'+name)
    checks = (ROOT/'CheckStep4.lean').read_text(encoding='utf-8')
    for name in schemas:
        if 'Internal.ObjectPacketReaderStep.native_'+name not in checks: raise RuntimeError('Missing raw reader native fixture: '+name)
    return {'raw_state_retains_valid_remainder_value_scale_reversed_accumulator':True,
            'no_byte_256_bound_or_positive_scale_premise':True,
            'low_byte_terminal_noncanonical_zero_reject_and_high_byte_guards_partition':True,
            'continuation_uses_unbounded_internal_natural_difference_not_bounded_digit':True,
            'actual_terminal_Cons_and_continuation_value_scale_exist_and_are_unique':True,
            'local_state_preservation_and_four_output_joint_determinism':True,
            'local_typed_successor_exists_iff_not_original_reject_guard':True,
            'original_128_0_1_literals_specialized_by_object_numeral_ranges':True,
            'EOF_scale_one_value_zero_guard_retained':True,
            'full_input_Cons_decomposition_and_whole_run':False,
            'actual_EOF_accumulator_reverse':False,
            'readTokens_Bytes_Canonical_full_program_bridge':False,
            'full_Basic_AST_schema_Proof_interpretation_Con':False}


def main() -> None:
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
    Packet_affine_arithmetic = check_Packet_affine_arithmetic()
    Packet_original_affine_local_matrices = check_Packet_original_affine_local_matrices()
    Packet_affine_bounded_applications = check_Packet_affine_bounded_applications()
    Packet_explicit_table_closed_trace = check_Packet_explicit_table_closed_trace()
    Packet_relational_affine_arithmetic = check_Packet_relational_affine_arithmetic()
    Packet_internal_radix_division = check_Packet_internal_radix_division()
    Packet_quotient_descent_and_induction = check_Packet_quotient_descent_and_induction()
    Packet_original_token_applications = check_Packet_original_token_applications()
    Packet_token_exact_arithmetic_recursion = check_Packet_token_exact_arithmetic_recursion()
    Packet_actual_token_execution = check_Packet_actual_token_execution()
    Packet_actual_token_numeric_bounds = check_Packet_actual_token_numeric_bounds()
    Packet_original_structural_forward_unfolding = check_Packet_original_structural_forward_unfolding()
    Packet_specified_structural_root_recursion = check_Packet_specified_structural_root_recursion()
    Packet_joint_internal_structural_tail_bounds = check_Packet_joint_internal_structural_tail_bounds()
    Packet_structural_search_bounds_and_typed_recursion = check_Packet_structural_search_bounds_and_typed_recursion()
    Packet_actual_token_prefix_inverse = check_Packet_actual_token_prefix_inverse()
    Packet_ordered_byte_fold_trace = check_Packet_ordered_byte_fold_trace()
    Packet_exact_ordered_byte_fold_recursion = check_Packet_exact_ordered_byte_fold_recursion()
    Packet_independent_valid_byte_input = check_Packet_independent_valid_byte_input()
    Packet_actual_byte_execution = check_Packet_actual_byte_execution()
    Packet_independent_varint_prefix_construction = check_Packet_independent_varint_prefix_construction()
    Packet_exact_canonical_varint_recursion = check_Packet_exact_canonical_varint_recursion()
    Packet_canonical_varint_execution = check_Packet_canonical_varint_execution()
    Packet_actual_token_canonical_prefix_agreement = check_Packet_actual_token_canonical_prefix_agreement()
    Packet_raw_reader_local_step = check_Packet_raw_reader_local_step()
    mode_three_scope = check_mode_three_scope()
    OUT.mkdir(exist_ok=True)
    (OUT / "summary.json").unlink(missing_ok=True)
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
    fixed_exact = fixed_axiom_expected_footprints(inherited)
    for name, dependencies in footprints.items():
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
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineExistsUnique',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineOutputsUnique',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineZeroIff',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineAdvance',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineRecursiveIff',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineAllInternalRecursiveLaw',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineAllInternalFibers',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineLiteralSystemExists',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineLiteralFramesUnique',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineZeroBelowLiteralBase',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineTwoBelowLiteralBase',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineRejectDigit',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineRejectTail',
                    'PPAC.Migration.Internal.ObjectPacketAffine.native_packetAffineRejectOutput',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAddConstGraphIff',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalRadixAddConstGraphIff',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineBaseHeadIff',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineStepHeadIff',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineBaseGuardIff',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineStepPremiseIff',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineBaseMatrixAtIff',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineStepMatrixAtIff',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineBaseMatrixIff',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineStepMatrixIff',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineAllInternalBaseMatrixLaw',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineAllInternalStepMatrixLaw',
                    'PPAC.Migration.Internal.ObjectPacketHornAffine.native_packetOriginalAffineLiteralMatrixSystemExists',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineBaseHeadSearchBound',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineBaseMatrixSuppliesBoundedApplication',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineStepHeadSearchBound',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineStepMatrixSuppliesBoundedApplication',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineRowAssignmentsNatural',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineEntryAssignmentsNatural',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineBaseDigitNatural',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineStepAssignmentsNatural',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineWholeBaseApplicationIff',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineWholeStepApplicationIff',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAllInternalAffineApplicationsLaw',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_packetAffineLiteralApplicationSystemExists',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_originalRuleApplicationRowNatural',
                    'PPAC.Migration.Internal.ObjectPacketAffineApplication.native_originalRuleRejectNonNaturalRow',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_closedTraceMemberHasActualStep',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_closedTraceInsertPreservesClosure',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_closedTraceInsertAcceptsActualRoot',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_closedTraceAcceptedRootSetExists',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_closedTraceAcceptedRootMembershipIff',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_closedTraceContainsEveryInternalSubtrace',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_closedTraceAcceptedRootSetClosed',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_closedTraceAllCandidateUnfoldIff',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_closedTraceAllCandidateSystemExists',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_closedTraceRejectNonNaturalRoot',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_packetActualTenRuleAcceptedRootSetExists',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_packetActualTenRuleAcceptedRootSetClosed',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_packetActualTenRuleConditionUnfoldIff',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_packetActualTenRuleTraceSystemExists',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_packetAffineForeignRuleRejected',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_packetAffineActualTenRuleDispatch',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_packetAffineActualTenRuleStepIffOutcomes',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_packetAffineConditionIffActualOutcomes',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_packetAffineBaseConditionAccepted',
                    'PPAC.Migration.Internal.ObjectPacketClosedTrace.native_packetAffineSuccessorConditionAccepted',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineRootBaseFieldsIff',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineRootStepFieldsIff',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineExactRootStepEquation',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineExactRootMemberEquation',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineInternalEntryFromIH',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineInternalEntryConstructedFromIH',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineZeroPointMembershipIff',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineSuccessorPointMembershipIff',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineAllInternalTailIHDischarged',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineAllInternalRootMembershipIff',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineConditionExactArithmeticIff',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineAcceptedExactArithmeticIff',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineAllInternalAcceptedExactArithmetic',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineAllInternalRootExactArithmetic',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineActualLiteralExactArithmeticSystemExists',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineAcceptedOutputExists',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineAcceptedOutputsUnique',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineAcceptedRejectDigit',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineAcceptedRejectTail',
                    'PPAC.Migration.Internal.ObjectPacketAffineArithmetic.native_packetAffineAcceptedRejectOutput',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionIncrement',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionCarry',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionSuccessorExists',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionAllNaturalOutputs',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionDecompositionExists',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionLowerBand',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionUpperBand',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionQuotientUnique',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionRemainderUnique',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionPairUnique',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionExactDomain',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionQuantifiedPairUnique',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionUniqueFiberExists',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionUniqueFiberExactDomain',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionAcceptedInverseExists',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionAcceptedInverseExactDomain',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionAcceptedInverseUnique',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionAllInternalUniqueFibers',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionAllInternalAcceptedInverse',
                    'PPAC.Migration.Internal.ObjectPacketDivision.native_packetDivisionActualLiteralSystemExists',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentOneProduct',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentProductBounds',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentQuotientBounds',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentQuotientBelow',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentNonzeroOutputStrict',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentTerminalDigit',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentExactStoppingThreshold',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentZeroOutputExactFields',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentLargeOutputNonzero',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentQuotientInductionPoint',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentQuotientInductionProgressive',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentAllInternalQuotientInduction',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentAffineProperties',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentAffineTerminalRecursiveBranches',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentAcceptedProperties',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentAllInternalAcceptedLaw',
                    'PPAC.Migration.Internal.ObjectPacketDescent.native_packetDescentActualLiteralSystemExists',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenSmallExactMatrix',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenLargeExactMatrixAt',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenLargeExactMatrixWitnessesDischarged',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenLargeAssignmentNatural',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenCanonicalAffineEntryArithmetic',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenDigitBelowAffineOutput',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenAllSixActualAssignmentBoundsAt',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenAllSixActualAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenSmallApplicationIff',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenLargeApplicationIff',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenOriginalTwoRuleDispatch',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenCompleteStepEquation',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenActualConditionEquation',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenAllInternalRootEquation',
                    'PPAC.Migration.Internal.ObjectPacketToken.native_packetTokenActualTwoRadixSystemExists',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenRootSmallFieldsIff',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenRootLargeFieldsIff',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenSpecifiedRootConditionEquation',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenSpecifiedRootMemberEquation',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenCanonicalEntryActualAcceptanceIff',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenCanonicalEntryAffineIff',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenZeroGuardFromNonzeroQuotient',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenSmallExactArithmeticBridge',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenLargeExactArithmeticBridge',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenFullExactArithmeticBridge',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenActualAcceptanceNaturalFields',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenArithmeticCriterionNaturalFields',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenConditionExactArithmeticWithoutCanonicalWitness',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenActualAcceptedExactArithmeticRecursion',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenLargeBranchExcludesSmallInput',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenActualSmallBranchIff',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenActualLargeBranchIff',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenActualRejectInvalidField',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenAllInternalAcceptedArithmeticRecursion',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenAllInternalRootArithmeticRecursion',
                    'PPAC.Migration.Internal.ObjectPacketTokenArithmetic.native_packetTokenActualArithmeticRecursionSystemExists',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenFiniteNumeralSum',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenActualDouble128',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenSmallDigitByteBound',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenShiftedDigitByteBound',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenActualSmallOutputConstructed',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenActualRecursiveOutputConstructed',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenAllInternalOutputExistenceIHDischarged',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenActualOutputExistsAtRadices',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenAllInternalOutputUniquenessIHDischarged',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenActualOutputUniqueAtRadices',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenActualUniqueOutputFiberAtRadices',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenUniqueOutputFiberDomainAtRadices',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenAllInternalExactUniqueOutputFibers',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenActualUniqueOutputFiberExactDomain',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenActualOutputExistsOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenExecution.native_packetTokenActualOutputUniqueOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenTwoCoordinateSumComparison',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenTwoCoordinateProductComparison',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenActualAffineComparison',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenSmallInputTailBounds',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenAllInternalBoundsIHDischarged',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenInputTailBoundsAtRadices',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenAllNumericBoundsAtRadices',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenAllInternalNumericBoundsOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenActualInputTailBoundsOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenActualInputBelowOutput',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenActualTailBelowOutput',
                    'PPAC.Migration.Internal.ObjectPacketTokenBounds.native_packetTokenActualContainedInputTailBounds',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureTreeExactMatrix',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureForestNilExactMatrix',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureForestConsExactMatrix',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructurePacketExactMatrix',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureAllFourCompleteLocalMatrices',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureOriginalBoundedApplicationsIff',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureOriginalApplicationForward',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureOriginalThreeTagDispatch',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureActualConditionBoundedIff',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureActualConditionForward',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureActualRootLaw',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureAllInternalRootLaws',
                    'PPAC.Migration.Internal.ObjectPacketStructure.native_packetStructureActualSystemExistsOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootTreeFieldsIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootForestNilFieldsIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootForestConsFieldsIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootPacketFieldsIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootAllActualOutcomesNormalized',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootCanonicalEntryActualAcceptanceIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootCanonicalCriterionActualRecursiveCasesIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootConditionNormalizedForward',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootActualRecursiveCasesWithoutCanonicalSet',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootActualAcceptedRecursiveCasesOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootActualAcceptedAllFieldsNatural',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootAllInternalOutcomeFieldNormalization',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootAllInternalAcceptedRecursion',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootActualTreeForward',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootActualForestForward',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootActualPacketForward',
                    'PPAC.Migration.Internal.ObjectPacketStructureRoot.native_packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailActualRawPayloadStrictSubcode',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailActualConsChildrenStrictSubcodes',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailTreePointFromJointChildIH',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailForestPointFromJointChildIH',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailJointPoint',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailJointObjectProgressive',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailAllInternalJointIHDischarged',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailActualTreeBelowOutput',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailActualForestBelowOutput',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailActualTreeContained',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailActualForestContained',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailAllInternalTreeLaw',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailAllInternalForestLaw',
                    'PPAC.Migration.Internal.ObjectPacketStructureTail.native_packetStructureTailAllInternalCoupledLawsOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchAllOriginalAssignmentNaturality',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchAllOriginalAssignmentBounds',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchActualAffineTailOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchFourOriginalApplicationsIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchActualRootConditionRecursionIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchTypedActualAcceptanceBackward',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchActualAcceptanceTypedRecursionIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchActualTreeTypedRecursionIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchActualForestTypedRecursionIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchActualPacketTypedRecursionIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchAllInternalRootConditionIff',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchAllInternalActualTypedRecursion',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchAllThreeActualTypedRecursionLaws',
                    'PPAC.Migration.Internal.ObjectPacketStructureSearch.native_packetStructureSearchCanonicalRootSystemExistsOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixShiftedByteNotSmall',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixTerminalContinuationDisjoint',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixTerminalInverse',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixLargeWitnessInverse',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixAllQuotientInduction',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixAllAtRadices',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixAllInternalOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixJointInverseOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixInputOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixTailOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixActualFiberIffOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenPrefix.native_packetTokenPrefixOutputIffOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesBothSequenceRowTransport',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesBothSequenceLinksAppend',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesOriginalDualSequenceAppend',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesTraceExtensionWitnessesEliminated',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesFullConsForwardAtRadix',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesNilExactFiberAtRadix',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesFoldOriginalValidityAndNaturalDomain',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesActual256ExactGraphIff',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesActualByteDomain',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesActualNilExistsOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesActualNilIffOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesActualConsForwardOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketBytesTrace.native_packetBytesActualSingletonOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionBothSequenceRowRestriction',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionAllOldRowsRestriction',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionFullDualPrefixFromActualRestrictions',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionDualPrefixGraphsObjectEliminated',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionCompleteTerminalRowNormalized',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionTerminalWitnessesFromFullTrace',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionSuccessorFullReverseDecomposition',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionAllInternalTraceReverseDecomposition',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionAllInternalFoldReverseDecomposition',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionIndependentCriterionBackward',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionExactAllInternalRadixRecursion',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionActual256CriterionEquivalence',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionActualBytesExactRecursionOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketBytesRecursion.native_packetBytesRecursionAllInternalActualRecursionOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputCompleteFieldsToAllFieldBounds',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputAllFieldBoundsToActualGraph',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputOriginalGraphAndLengthBoundsIff',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputFullConsFieldBoundsForward',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputFirstActualFieldByteBound',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputAllSuccessorFieldsTailBounds',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputBoundsAtAnyActualLength',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputNilGuardConstructed',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputFullConsGuardConstructed',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputTypedConsHeadAndTailRecovered',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputAllInternalRadixGuardRecursion',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputActual256ExactGuardIff',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputActualByteNaturalOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputActualGuardImpliesOriginalListValidity',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputActualGuardExactRecursionOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketByteInput.native_packetByteInputAllInternalActualGuardOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionActualCellData',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionActualCellTotal',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionActualCellUnique',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionStrictInputTailProperty',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionStrictAcceptedTailProperty',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionTotalJointStep',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionDomainJointStep',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionUniqueJointStep',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionAllJointProperties',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionOutputExists',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionActualInputDomain',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionOutputUnique',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionExistsDomainIff',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionUniqueFiberIff',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionAllInternalFiberDomain',
                    'PPAC.Migration.Internal.ObjectPacketBytesExecution.native_packetBytesExecutionInvalidInputRejected',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintTerminalCellConstructed',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintNonzeroContinuationCellConstructed',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintContinuationRequiresNonzeroValue',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintTerminalContinuationDisjoint',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintZeroPriorForcesActualTerminal',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintNonemptyListForcesActualContinuation',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintEveryActualCellByteBound',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintBothOriginalGraphsRowTransport',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintFullOldRowsAndNewLastRowPreserved',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintRealDualSequenceExtension',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintEmptyTraceExactNaturalSeed',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintIndependentCanonicalAtDomain',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintIndependentActualCanonicalDomain',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintActual128ExactGraphIff',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintCanonicalTerminalActualGraphs',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintCanonicalNonzeroContinuationActualGraphs',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintCanonicalRejectsActualNil',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintIndependentPrefixExactNumericDomain',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintTerminalPrefixAllCodeWitnessesEliminated',
                    'PPAC.Migration.Internal.ObjectPacketVarintPrefix.native_packetVarintContinuationPrefixAllCodeWitnessesEliminated',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionBothGraphsFullOldRowRestriction',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionBothGraphsAllOldLinksRestriction',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionActualPrefixGraphsConstructedAndEliminated',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionCompleteActualLastRowNormalized',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionAllInternalRawFoldReverseDecomposition',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionAllInternalRawFoldExactRecursion',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionNonzeroValueForcesActualNonemptySuffix',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionCanonicalTerminalHeadAligned',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionAllInternalCanonicalReverseDecomposition',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionExactCanonicalRecursionAtNaturalRadix',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionActual128CompleteSmallerGraphAlignment',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionActual128CanonicalExactRecursion',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionActualCanonicalExactRecursionOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketVarintRecursion.native_packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionStrictQuotientAuthorizesJointIH',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionActualSmallListConstructed',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionActualRecursiveListConstructed',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionExistenceJointStep',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionAllActualCandidatesByteGuardJointStep',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionAllActualCandidateListsUniqueJointStep',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionJointPropertyStep',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionOriginalFoundationSeparationAllJointIHDischarged',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionAllJointPropertiesOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionActualListExistsOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuard',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionEveryActualCanonicalCandidateListUnique',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionExistenceExactNaturalDomain',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionUniqueByteListFiberExactNaturalDomain',
                    'PPAC.Migration.Internal.ObjectPacketVarintExecution.native_packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalGivenConsExactByteTailIff',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalActualSingletonLastCellNormalized',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalIndependentPrefixExactArithmeticRecursion',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalAllInternalIndependentPrefixRecursion',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIH',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalFullOriginalAndIndependentCriteriaAgree',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalWholeActualTokenPrefixAgreementStep',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischarged',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalAllAgreementPropertiesOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmega',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalPrefixAtAnyActualCanonicalList',
                    'PPAC.Migration.Internal.ObjectPacketTokenCanonical.native_packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalList',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderRawGuardPartition',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderTerminalRejectionNoStep',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderEofExactGuardPartition',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderUnboundedValueUpdateExists',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderUnboundedValueUpdateRange',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderContinuationExactNaturalDomain',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderContinuationJointUnique',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderContinuationActualExists',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderEmissionActualConsExists',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderEmissionActualConsUnique',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderEmissionValidAccumulator',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderLocalStepStatePreserved',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderLocalStepJointUnique',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderLocalStepExactSuccessorDomain',
                    'PPAC.Migration.Internal.ObjectPacketReaderStep.native_packetReaderOriginalLiteralLocalSuccessorDomain'} or name.startswith((
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
        "ObjectPacketReaderStep": ('packetReaderRawGuardPartition', 'packetReaderTerminalRejectionNoStep', 'packetReaderEofExactGuardPartition', 'packetReaderUnboundedValueUpdateExists', 'packetReaderUnboundedValueUpdateRange', 'packetReaderContinuationExactNaturalDomain', 'packetReaderContinuationJointUnique', 'packetReaderContinuationActualExists', 'packetReaderEmissionActualConsExists', 'packetReaderEmissionActualConsUnique', 'packetReaderEmissionValidAccumulator', 'packetReaderLocalStepStatePreserved', 'packetReaderLocalStepJointUnique', 'packetReaderLocalStepExactSuccessorDomain', 'packetReaderOriginalLiteralLocalSuccessorDomain'),
        "ObjectPacketTokenCanonical": ('packetTokenCanonicalGivenConsExactByteTailIff', 'packetTokenCanonicalActualSingletonLastCellNormalized', 'packetTokenCanonicalIndependentPrefixExactArithmeticRecursion', 'packetTokenCanonicalAllInternalIndependentPrefixRecursion', 'packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIH', 'packetTokenCanonicalFullOriginalAndIndependentCriteriaAgree', 'packetTokenCanonicalWholeActualTokenPrefixAgreementStep', 'packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischarged', 'packetTokenCanonicalAllAgreementPropertiesOnlyOmega', 'packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmega', 'packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmega', 'packetTokenCanonicalPrefixAtAnyActualCanonicalList', 'packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalList'),
        "ObjectPacketVarintExecution": ('packetVarintExecutionStrictQuotientAuthorizesJointIH', 'packetVarintExecutionActualSmallListConstructed', 'packetVarintExecutionActualRecursiveListConstructed', 'packetVarintExecutionExistenceJointStep', 'packetVarintExecutionAllActualCandidatesByteGuardJointStep', 'packetVarintExecutionAllActualCandidateListsUniqueJointStep', 'packetVarintExecutionJointPropertyStep', 'packetVarintExecutionOriginalFoundationSeparationAllJointIHDischarged', 'packetVarintExecutionAllJointPropertiesOnlyOmega', 'packetVarintExecutionActualListExistsOnlyOmega', 'packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuard', 'packetVarintExecutionEveryActualCanonicalCandidateListUnique', 'packetVarintExecutionExistenceExactNaturalDomain', 'packetVarintExecutionUniqueByteListFiberExactNaturalDomain', 'packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmega'),
        "ObjectPacketVarintRecursion": ('packetVarintRecursionBothGraphsFullOldRowRestriction', 'packetVarintRecursionBothGraphsAllOldLinksRestriction', 'packetVarintRecursionActualPrefixGraphsConstructedAndEliminated', 'packetVarintRecursionCompleteActualLastRowNormalized', 'packetVarintRecursionAllInternalRawFoldReverseDecomposition', 'packetVarintRecursionAllInternalRawFoldExactRecursion', 'packetVarintRecursionNonzeroValueForcesActualNonemptySuffix', 'packetVarintRecursionCanonicalTerminalHeadAligned', 'packetVarintRecursionAllInternalCanonicalReverseDecomposition', 'packetVarintRecursionExactCanonicalRecursionAtNaturalRadix', 'packetVarintRecursionActual128CompleteSmallerGraphAlignment', 'packetVarintRecursionActual128CanonicalExactRecursion', 'packetVarintRecursionActualCanonicalExactRecursionOnlyOmega', 'packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmega'),
        "ObjectPacketVarintPrefix": ('packetVarintTerminalCellConstructed', 'packetVarintNonzeroContinuationCellConstructed', 'packetVarintContinuationRequiresNonzeroValue', 'packetVarintTerminalContinuationDisjoint', 'packetVarintZeroPriorForcesActualTerminal', 'packetVarintNonemptyListForcesActualContinuation', 'packetVarintEveryActualCellByteBound', 'packetVarintBothOriginalGraphsRowTransport', 'packetVarintFullOldRowsAndNewLastRowPreserved', 'packetVarintRealDualSequenceExtension', 'packetVarintEmptyTraceExactNaturalSeed', 'packetVarintIndependentCanonicalAtDomain', 'packetVarintIndependentActualCanonicalDomain', 'packetVarintActual128ExactGraphIff', 'packetVarintCanonicalTerminalActualGraphs', 'packetVarintCanonicalNonzeroContinuationActualGraphs', 'packetVarintCanonicalRejectsActualNil', 'packetVarintIndependentPrefixExactNumericDomain', 'packetVarintTerminalPrefixAllCodeWitnessesEliminated', 'packetVarintContinuationPrefixAllCodeWitnessesEliminated'),
        "ObjectPacketBytesExecution": ('packetBytesExecutionActualCellData', 'packetBytesExecutionActualCellTotal', 'packetBytesExecutionActualCellUnique', 'packetBytesExecutionStrictInputTailProperty', 'packetBytesExecutionStrictAcceptedTailProperty', 'packetBytesExecutionTotalJointStep', 'packetBytesExecutionDomainJointStep', 'packetBytesExecutionUniqueJointStep', 'packetBytesExecutionAllJointProperties', 'packetBytesExecutionOutputExists', 'packetBytesExecutionActualInputDomain', 'packetBytesExecutionOutputUnique', 'packetBytesExecutionExistsDomainIff', 'packetBytesExecutionUniqueFiberIff', 'packetBytesExecutionAllInternalFiberDomain', 'packetBytesExecutionInvalidInputRejected'),
        "ObjectPacketByteInput": ('packetByteInputCompleteFieldsToAllFieldBounds', 'packetByteInputAllFieldBoundsToActualGraph', 'packetByteInputOriginalGraphAndLengthBoundsIff', 'packetByteInputFullConsFieldBoundsForward', 'packetByteInputFirstActualFieldByteBound', 'packetByteInputAllSuccessorFieldsTailBounds', 'packetByteInputBoundsAtAnyActualLength', 'packetByteInputNilGuardConstructed', 'packetByteInputFullConsGuardConstructed', 'packetByteInputTypedConsHeadAndTailRecovered', 'packetByteInputAllInternalRadixGuardRecursion', 'packetByteInputActual256ExactGuardIff', 'packetByteInputActualByteNaturalOnlyOmega', 'packetByteInputActualGuardImpliesOriginalListValidity', 'packetByteInputActualGuardExactRecursionOnlyOmega', 'packetByteInputAllInternalActualGuardOnlyOmega'),
        "ObjectPacketBytesRecursion": ('packetBytesRecursionBothSequenceRowRestriction', 'packetBytesRecursionAllOldRowsRestriction', 'packetBytesRecursionFullDualPrefixFromActualRestrictions', 'packetBytesRecursionDualPrefixGraphsObjectEliminated', 'packetBytesRecursionCompleteTerminalRowNormalized', 'packetBytesRecursionTerminalWitnessesFromFullTrace', 'packetBytesRecursionSuccessorFullReverseDecomposition', 'packetBytesRecursionAllInternalTraceReverseDecomposition', 'packetBytesRecursionAllInternalFoldReverseDecomposition', 'packetBytesRecursionIndependentCriterionBackward', 'packetBytesRecursionExactAllInternalRadixRecursion', 'packetBytesRecursionActual256CriterionEquivalence', 'packetBytesRecursionActualBytesExactRecursionOnlyOmega', 'packetBytesRecursionAllInternalActualRecursionOnlyOmega'),
        "ObjectPacketBytesTrace": ('packetBytesBothSequenceRowTransport', 'packetBytesBothSequenceLinksAppend', 'packetBytesOriginalDualSequenceAppend', 'packetBytesTraceExtensionWitnessesEliminated', 'packetBytesFullConsForwardAtRadix', 'packetBytesNilExactFiberAtRadix', 'packetBytesFoldOriginalValidityAndNaturalDomain', 'packetBytesActual256ExactGraphIff', 'packetBytesActualByteDomain', 'packetBytesActualNilExistsOnlyOmega', 'packetBytesActualNilIffOnlyOmega', 'packetBytesActualConsForwardOnlyOmega', 'packetBytesActualSingletonOnlyOmega'),
        "ObjectPacketTokenPrefix": ('packetTokenPrefixShiftedByteNotSmall', 'packetTokenPrefixTerminalContinuationDisjoint', 'packetTokenPrefixTerminalInverse', 'packetTokenPrefixLargeWitnessInverse', 'packetTokenPrefixAllQuotientInduction', 'packetTokenPrefixAllAtRadices', 'packetTokenPrefixAllInternalOnlyOmega', 'packetTokenPrefixJointInverseOnlyOmega', 'packetTokenPrefixInputOnlyOmega', 'packetTokenPrefixTailOnlyOmega', 'packetTokenPrefixActualFiberIffOnlyOmega', 'packetTokenPrefixOutputIffOnlyOmega'),
        "ObjectPacketStructureSearch": ('packetStructureSearchAllOriginalAssignmentNaturality', 'packetStructureSearchAllOriginalAssignmentBounds', 'packetStructureSearchActualAffineTailOnlyOmega', 'packetStructureSearchFourOriginalApplicationsIff', 'packetStructureSearchActualRootConditionRecursionIff', 'packetStructureSearchTypedActualAcceptanceBackward', 'packetStructureSearchActualAcceptanceTypedRecursionIff', 'packetStructureSearchActualTreeTypedRecursionIff', 'packetStructureSearchActualForestTypedRecursionIff', 'packetStructureSearchActualPacketTypedRecursionIff', 'packetStructureSearchAllInternalRootConditionIff', 'packetStructureSearchAllInternalActualTypedRecursion', 'packetStructureSearchAllThreeActualTypedRecursionLaws', 'packetStructureSearchCanonicalRootSystemExistsOnlyOmega'),
        "ObjectPacketStructureTail": ('packetStructureTailActualRawPayloadStrictSubcode', 'packetStructureTailActualConsChildrenStrictSubcodes', 'packetStructureTailTreePointFromJointChildIH', 'packetStructureTailForestPointFromJointChildIH', 'packetStructureTailJointPoint', 'packetStructureTailJointObjectProgressive', 'packetStructureTailAllInternalJointIHDischarged', 'packetStructureTailActualTreeBelowOutput', 'packetStructureTailActualForestBelowOutput', 'packetStructureTailActualTreeContained', 'packetStructureTailActualForestContained', 'packetStructureTailAllInternalTreeLaw', 'packetStructureTailAllInternalForestLaw', 'packetStructureTailAllInternalCoupledLawsOnlyOmega'),
        "ObjectPacketStructureRoot": ('packetStructureRootTreeFieldsIff', 'packetStructureRootForestNilFieldsIff', 'packetStructureRootForestConsFieldsIff', 'packetStructureRootPacketFieldsIff', 'packetStructureRootAllActualOutcomesNormalized', 'packetStructureRootCanonicalEntryActualAcceptanceIff', 'packetStructureRootCanonicalCriterionActualRecursiveCasesIff', 'packetStructureRootConditionNormalizedForward', 'packetStructureRootActualRecursiveCasesWithoutCanonicalSet', 'packetStructureRootActualAcceptedRecursiveCasesOnlyOmega', 'packetStructureRootActualAcceptedAllFieldsNatural', 'packetStructureRootAllInternalOutcomeFieldNormalization', 'packetStructureRootAllInternalAcceptedRecursion', 'packetStructureRootActualTreeForward', 'packetStructureRootActualForestForward', 'packetStructureRootActualPacketForward', 'packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmega'),
        "ObjectPacketStructure": ('packetStructureTreeExactMatrix', 'packetStructureForestNilExactMatrix', 'packetStructureForestConsExactMatrix', 'packetStructurePacketExactMatrix', 'packetStructureAllFourCompleteLocalMatrices', 'packetStructureOriginalBoundedApplicationsIff', 'packetStructureOriginalApplicationForward', 'packetStructureOriginalThreeTagDispatch', 'packetStructureActualConditionBoundedIff', 'packetStructureActualConditionForward', 'packetStructureActualRootLaw', 'packetStructureAllInternalRootLaws', 'packetStructureActualSystemExistsOnlyOmega'),
        "ObjectPacketTokenBounds": ('packetTokenTwoCoordinateSumComparison', 'packetTokenTwoCoordinateProductComparison', 'packetTokenActualAffineComparison', 'packetTokenSmallInputTailBounds', 'packetTokenAllInternalBoundsIHDischarged', 'packetTokenInputTailBoundsAtRadices', 'packetTokenAllNumericBoundsAtRadices', 'packetTokenAllInternalNumericBoundsOnlyOmega', 'packetTokenActualInputTailBoundsOnlyOmega', 'packetTokenActualInputBelowOutput', 'packetTokenActualTailBelowOutput', 'packetTokenActualContainedInputTailBounds'),
        "ObjectPacketTokenExecution": ('packetTokenFiniteNumeralSum', 'packetTokenActualDouble128', 'packetTokenSmallDigitByteBound', 'packetTokenShiftedDigitByteBound', 'packetTokenActualSmallOutputConstructed', 'packetTokenActualRecursiveOutputConstructed', 'packetTokenAllInternalOutputExistenceIHDischarged', 'packetTokenActualOutputExistsAtRadices', 'packetTokenAllInternalOutputUniquenessIHDischarged', 'packetTokenActualOutputUniqueAtRadices', 'packetTokenActualUniqueOutputFiberAtRadices', 'packetTokenUniqueOutputFiberDomainAtRadices', 'packetTokenAllInternalExactUniqueOutputFibers', 'packetTokenActualUniqueOutputFiberExactDomain', 'packetTokenActualOutputExistsOnlyOmega', 'packetTokenActualOutputUniqueOnlyOmega'),
        "ObjectPacketTokenArithmetic": ('packetTokenRootSmallFieldsIff', 'packetTokenRootLargeFieldsIff', 'packetTokenSpecifiedRootConditionEquation', 'packetTokenSpecifiedRootMemberEquation', 'packetTokenCanonicalEntryActualAcceptanceIff', 'packetTokenCanonicalEntryAffineIff', 'packetTokenZeroGuardFromNonzeroQuotient', 'packetTokenSmallExactArithmeticBridge', 'packetTokenLargeExactArithmeticBridge', 'packetTokenFullExactArithmeticBridge', 'packetTokenActualAcceptanceNaturalFields', 'packetTokenArithmeticCriterionNaturalFields', 'packetTokenConditionExactArithmeticWithoutCanonicalWitness', 'packetTokenActualAcceptedExactArithmeticRecursion', 'packetTokenLargeBranchExcludesSmallInput', 'packetTokenActualSmallBranchIff', 'packetTokenActualLargeBranchIff', 'packetTokenActualRejectInvalidField', 'packetTokenAllInternalAcceptedArithmeticRecursion', 'packetTokenAllInternalRootArithmeticRecursion', 'packetTokenActualArithmeticRecursionSystemExists'),
        "ObjectPacketToken": ('packetTokenSmallExactMatrix', 'packetTokenLargeExactMatrixAt', 'packetTokenLargeExactMatrixWitnessesDischarged', 'packetTokenLargeAssignmentNatural', 'packetTokenCanonicalAffineEntryArithmetic', 'packetTokenDigitBelowAffineOutput', 'packetTokenAllSixActualAssignmentBoundsAt', 'packetTokenAllSixActualAssignmentBounds', 'packetTokenSmallApplicationIff', 'packetTokenLargeApplicationIff', 'packetTokenOriginalTwoRuleDispatch', 'packetTokenCompleteStepEquation', 'packetTokenActualConditionEquation', 'packetTokenAllInternalRootEquation', 'packetTokenActualTwoRadixSystemExists'),
        "ObjectPacketDescent": ('packetDescentOneProduct', 'packetDescentProductBounds', 'packetDescentQuotientBounds', 'packetDescentQuotientBelow', 'packetDescentNonzeroOutputStrict', 'packetDescentTerminalDigit', 'packetDescentExactStoppingThreshold', 'packetDescentZeroOutputExactFields', 'packetDescentLargeOutputNonzero', 'packetDescentQuotientInductionPoint', 'packetDescentQuotientInductionProgressive', 'packetDescentAllInternalQuotientInduction', 'packetDescentAffineProperties', 'packetDescentAffineTerminalRecursiveBranches', 'packetDescentAcceptedProperties', 'packetDescentAllInternalAcceptedLaw', 'packetDescentActualLiteralSystemExists'),
        "ObjectPacketDivision": ('packetDivisionIncrement', 'packetDivisionCarry', 'packetDivisionSuccessorExists', 'packetDivisionAllNaturalOutputs', 'packetDivisionDecompositionExists', 'packetDivisionLowerBand', 'packetDivisionUpperBand', 'packetDivisionQuotientUnique', 'packetDivisionRemainderUnique', 'packetDivisionPairUnique', 'packetDivisionExactDomain', 'packetDivisionQuantifiedPairUnique', 'packetDivisionUniqueFiberExists', 'packetDivisionUniqueFiberExactDomain', 'packetDivisionAcceptedInverseExists', 'packetDivisionAcceptedInverseExactDomain', 'packetDivisionAcceptedInverseUnique', 'packetDivisionAllInternalUniqueFibers', 'packetDivisionAllInternalAcceptedInverse', 'packetDivisionActualLiteralSystemExists'),
        "ObjectPacketAffineArithmetic": ('packetAffineRootBaseFieldsIff', 'packetAffineRootStepFieldsIff', 'packetAffineExactRootStepEquation', 'packetAffineExactRootMemberEquation', 'packetAffineInternalEntryFromIH', 'packetAffineInternalEntryConstructedFromIH', 'packetAffineZeroPointMembershipIff', 'packetAffineSuccessorPointMembershipIff', 'packetAffineAllInternalTailIHDischarged', 'packetAffineAllInternalRootMembershipIff', 'packetAffineConditionExactArithmeticIff', 'packetAffineAcceptedExactArithmeticIff', 'packetAffineAllInternalAcceptedExactArithmetic', 'packetAffineAllInternalRootExactArithmetic', 'packetAffineActualLiteralExactArithmeticSystemExists', 'packetAffineAcceptedOutputExists', 'packetAffineAcceptedOutputsUnique', 'packetAffineAcceptedRejectDigit', 'packetAffineAcceptedRejectTail', 'packetAffineAcceptedRejectOutput'),
        "ObjectPacketClosedTrace": ('closedTraceMemberHasActualStep', 'closedTraceInsertPreservesClosure', 'closedTraceInsertAcceptsActualRoot', 'closedTraceAcceptedRootSetExists', 'closedTraceAcceptedRootMembershipIff', 'closedTraceContainsEveryInternalSubtrace', 'closedTraceAcceptedRootSetClosed', 'closedTraceAllCandidateUnfoldIff', 'closedTraceAllCandidateSystemExists', 'closedTraceRejectNonNaturalRoot', 'packetActualTenRuleAcceptedRootSetExists', 'packetActualTenRuleAcceptedRootSetClosed', 'packetActualTenRuleConditionUnfoldIff', 'packetActualTenRuleTraceSystemExists', 'packetAffineForeignRuleRejected', 'packetAffineActualTenRuleDispatch', 'packetAffineActualTenRuleStepIffOutcomes', 'packetAffineConditionIffActualOutcomes', 'packetAffineBaseConditionAccepted', 'packetAffineSuccessorConditionAccepted'),
        "ObjectPacketAffineApplication": ('packetAffineBaseHeadSearchBound', 'packetAffineBaseMatrixSuppliesBoundedApplication', 'packetAffineStepHeadSearchBound', 'packetAffineStepMatrixSuppliesBoundedApplication', 'packetAffineRowAssignmentsNatural', 'packetAffineEntryAssignmentsNatural', 'packetAffineBaseDigitNatural', 'packetAffineStepAssignmentsNatural', 'packetAffineWholeBaseApplicationIff', 'packetAffineWholeStepApplicationIff', 'packetAllInternalAffineApplicationsLaw', 'packetAffineLiteralApplicationSystemExists', 'originalRuleApplicationRowNatural', 'originalRuleRejectNonNaturalRow'),
        "ObjectPacketHornAffine": ('packetOriginalAddConstGraphIff', 'packetOriginalRadixAddConstGraphIff', 'packetOriginalAffineBaseHeadIff', 'packetOriginalAffineStepHeadIff', 'packetOriginalAffineBaseGuardIff', 'packetOriginalAffineStepPremiseIff', 'packetOriginalAffineBaseMatrixAtIff', 'packetOriginalAffineStepMatrixAtIff', 'packetOriginalAffineBaseMatrixIff', 'packetOriginalAffineStepMatrixIff', 'packetOriginalAffineAllInternalBaseMatrixLaw', 'packetOriginalAffineAllInternalStepMatrixLaw', 'packetOriginalAffineLiteralMatrixSystemExists'),
        "ObjectPacketAffine": ('packetAffineExistsUnique', 'packetAffineOutputsUnique', 'packetAffineZeroIff', 'packetAffineAdvance', 'packetAffineRecursiveIff', 'packetAffineAllInternalRecursiveLaw', 'packetAffineAllInternalFibers', 'packetAffineLiteralSystemExists', 'packetAffineLiteralFramesUnique', 'packetAffineZeroBelowLiteralBase', 'packetAffineTwoBelowLiteralBase', 'packetAffineRejectDigit', 'packetAffineRejectTail', 'packetAffineRejectOutput'),
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
    hashed = sources + sorted(ROOT.glob("third_party/openai/*.txt")) + [ROOT / x for x in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "scripts/verify.py", "scripts/check_source_rules.py", "scripts/check_source_theory.py", "docs/SOURCE_THEORY_LOCK.json", "docs/SOURCE_RULES_LOCK.json", "docs/TRUST_BASELINE.json", "docs/CHOICE_TRUST_BASELINE.json", "docs/MODE3_CHECKER_SCOPE.json"]]
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
        "original_openai_build_run": False,
        "relative_consistency_proved": False,
        "internal_explicit_declaration_audit_coverage_complete": True,
        "internal_explicit_declarations_coverage_checked": len(internal_explicit),
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
        "Packet_affine_arithmetic_guard": Packet_affine_arithmetic,
        "Packet_original_affine_local_matrices_guard": Packet_original_affine_local_matrices,
        "Packet_affine_bounded_applications_guard": Packet_affine_bounded_applications,
        "Packet_explicit_table_closed_trace_guard": Packet_explicit_table_closed_trace,
        "Packet_raw_reader_local_step_guard": Packet_raw_reader_local_step,
        'object_Packet_raw_readTokens_local_step_domain_and_determinism_proved': True,
        "Packet_actual_token_canonical_prefix_agreement_guard": Packet_actual_token_canonical_prefix_agreement,
        'object_Packet_given_actual_Cons_Bytes_exact_tail_execution_proved': True,
        'object_Packet_independent_Prefix_full_exact_arithmetic_recursion_proved': True,
        'object_Packet_actual_Tok_canonical_prefix_ALL3_requires_only_omega': True,
        'object_Packet_actual_Tok_agreement_quotient_IH_and_128_256_witnesses_discharged': True,
        'object_Packet_actual_Tok_iff_Bytes_at_any_actual_canonical_list_proved': True,
        "Packet_canonical_varint_execution_guard": Packet_canonical_varint_execution,
        'object_Packet_varint_joint_Formula2_existence_byte_domain_unique_implemented': True,
        'object_Packet_varint_joint_internal_IH_and_128_256_witnesses_discharged': True,
        'object_Packet_varint_all_actual_candidates_independent_byte_input_guard_proved': True,
        'object_Packet_varint_unique_list_fiber_exact_natural_domain_only_omega': True,
        "Packet_exact_canonical_varint_recursion_guard": Packet_exact_canonical_varint_recursion,
        'object_Packet_varint_full_dual_graph_prefix_restriction_proved': True,
        'object_Packet_varint_all_internal_raw_fold_recursion_proved': True,
        'object_Packet_varint_nonzero_tail_value_proves_smaller_canonical_nonempty': True,
        'object_Packet_varint_canonical_exact_recursion_final_ALL2_requires_only_omega': True,
        'object_Packet_varint_canonical_actual_128_smaller_graph_alignment_proved': True,
        "Packet_independent_varint_prefix_construction_guard": Packet_independent_varint_prefix_construction,
        'object_Packet_actual_Tok_iff_independent_canonical_prefix_proved': True,
        'object_Packet_independent_varint_zero_seeded_dual_graph_constructed': True,
        'object_Packet_varint_cells_terminal_nonzero_continuation_disjoint_proved': True,
        'object_Packet_varint_actual_cell_byte_bounds_proved': True,
        'object_Packet_independent_varint_terminal_and_continuation_graph_closure_proved': True,
        'object_Packet_independent_varint_prefix_constructors_exact_tail_proved': True,
        'object_Packet_independent_varint_all_internal_exact_reverse_recursion_proved': True,
        'object_Packet_independent_varint_full_total_unique_and_byte_input_domain_proved': True,
        "Packet_actual_byte_execution_guard": Packet_actual_byte_execution,
        'object_Packet_actual_byte_execution_exact_independent_input_domain_proved': True,
        'object_Packet_actual_byte_execution_joint_internal_IH_discharged': True,
        'object_Packet_actual_byte_execution_unique_fiber_domain_only_omega_proved': True,
        "Packet_independent_valid_byte_input_guard": Packet_independent_valid_byte_input,
        'object_Packet_independent_byte_input_guard_uses_original_full_Fields_graph': True,
        'object_Packet_byte_input_guard_graph_pointwise_bounds_equivalence_proved': True,
        'object_Packet_byte_input_guard_all_internal_Nil_Cons_recursion_proved': True,
        'object_Packet_byte_input_guard_actual_head_and_tail_bounds_derived': True,
        'object_Packet_byte_input_guard_length_graph_and_radix_witnesses_eliminated': True,
        'object_Packet_byte_input_guard_final_interfaces_require_only_omega': True,
        'object_Packet_byte_input_guard_independent_of_Bytes_execution_proved': True,
        "Packet_exact_ordered_byte_fold_recursion_guard": Packet_exact_ordered_byte_fold_recursion,
        'object_Packet_ordered_byte_fold_dual_restricted_prefix_graphs_constructed': True,
        'object_Packet_ordered_byte_fold_full_terminal_row_normalization_proved': True,
        'object_Packet_ordered_byte_fold_all_internal_exact_recursion_iff_proved': True,
        'object_Packet_ordered_byte_fold_exact_recursion_ALL3_requires_only_omega': True,
        'object_Packet_ordered_byte_fold_reverse_prefix_and_radix_witnesses_eliminated': True,
        'object_Packet_ordered_byte_fold_exact_recursion_Nil_tail_natural_guard_preserved': True,
        "Packet_ordered_byte_fold_trace_guard": Packet_ordered_byte_fold_trace,
        'object_Packet_independent_ordered_byte_fold_trace_constructed': True,
        'object_Packet_ordered_byte_fold_exact_typed_Nil_fiber_proved': True,
        'object_Packet_ordered_byte_fold_Cons_forward_constructed': True,
        'object_Packet_ordered_byte_fold_closure_sequence_and_radix_witnesses_eliminated': True,
        'object_Packet_ordered_byte_fold_all_internal_trace_lengths_preserved': True,
        'object_Packet_ordered_byte_fold_global_total_unique_proved': True,
        'object_Packet_ordered_byte_fold_full_Cons_recursion_iff_proved': True,
        "Packet_actual_token_prefix_inverse_guard": Packet_actual_token_prefix_inverse,
        'object_Packet_actual_token_numeric_prefix_inverse_proved': True,
        'object_Packet_actual_token_joint_input_remaining_tail_unique_proved': True,
        'object_Packet_actual_token_terminal_continuation_disjoint_proved': True,
        'object_Packet_actual_token_prefix_ALL5_requires_only_omega': True,
        'object_Packet_actual_token_prefix_all_internal_IH_discharged': True,
        'object_Packet_actual_token_prefix_exact_accepted_fiber_proved': True,
        "Packet_structural_search_bounds_and_typed_recursion_guard": Packet_structural_search_bounds_and_typed_recursion,
        'object_Packet_structural_all_original_assignment_naturality_proved': True,
        'object_Packet_structural_four_full_original_application_equivalences_proved': True,
        'object_Packet_structural_actual_all_internal_typed_recursion_iff_proved': True,
        'object_Packet_structural_actual_recursion_iff_requires_only_omega': True,
        'object_Packet_structural_actual_Nil_tail_naturality_guard_preserved': True,
        "Packet_joint_internal_structural_tail_bounds_guard": Packet_joint_internal_structural_tail_bounds,
        'object_Packet_structural_actual_tree_tail_le_output_proved': True,
        'object_Packet_structural_actual_forest_tail_le_output_proved': True,
        'object_Packet_structural_tail_all_internal_IH_discharged': True,
        'object_Packet_structural_tail_bounds_require_only_omega': True,
        'object_Packet_structural_actual_child_subcode_descent_proved': True,
        "Packet_specified_structural_root_recursion_guard": Packet_specified_structural_root_recursion,
        'object_Packet_structural_actual_acceptance_independently_defined': True,
        'object_Packet_structural_canonical_entries_actual_acceptance_iff_proved': True,
        'object_Packet_structural_all_internal_actual_forward_recursion_proved': True,
        'object_Packet_structural_actual_forward_requires_only_omega': True,
        'object_Packet_structural_actual_acceptance_all_field_naturality_proved': True,
        "Packet_original_structural_forward_unfolding_guard": Packet_original_structural_forward_unfolding,
        'object_Packet_structural_four_original_local_matrices_proved': True,
        'object_Packet_structural_four_exact_bounded_applications_proved': True,
        'object_Packet_structural_four_forward_applications_proved': True,
        'object_Packet_structural_three_tag_dispatch_proved': True,
        'object_Packet_structural_all_internal_forward_root_system_proved': True,
        'object_Packet_structural_unbounded_reverse_search_bounds_discharged': True,
        'object_Packet_structural_joint_internal_tail_bound_proved': True,
        'object_Packet_structural_specified_root_fields_normalized': True,
        "Packet_actual_token_numeric_bounds_guard": Packet_actual_token_numeric_bounds,
        'object_Packet_token_numeric_input_tail_bounds_internal_IH_discharged': True,
        'object_Packet_token_actual_input_le_output_proved': True,
        'object_Packet_token_actual_tail_le_output_proved': True,
        'object_Packet_token_all_internal_numeric_bounds_proved': True,
        'object_Packet_token_final_numeric_bounds_requires_only_omega': True,
        "Packet_actual_token_execution_guard": Packet_actual_token_execution,
        'object_Packet_token_shifted_byte_bound_proved': True,
        'object_Packet_token_output_existence_internal_IH_discharged': True,
        'object_Packet_token_output_uniqueness_internal_IH_discharged': True,
        'object_Packet_token_exact_internal_unique_output_domain_proved': True,
        'object_Packet_token_final_execution_requires_only_omega': True,
        "Packet_token_exact_arithmetic_recursion_guard": Packet_token_exact_arithmetic_recursion,
        'object_Packet_token_specified_root_fields_normalized': True,
        'object_Packet_token_exact_arithmetic_recursive_equation_proved': True,
        'object_Packet_token_canonical_and_root_witnesses_eliminated': True,
        'object_Packet_token_all_internal_acceptance_recursive_iff_proved': True,
        'object_Packet_token_actual_small_large_branch_test_proved': True,
        'object_Packet_token_literal_arithmetic_recursion_system_constructed': True,
        'object_Packet_token_invalid_natural_field_rejection_proved': True,
        "Packet_original_token_applications_guard": Packet_original_token_applications,
        'object_Packet_token_original_rule_matrices_proved': True,
        'object_Packet_token_all_six_assignment_search_bounds_proved': True,
        'object_Packet_token_canonical_bounded_application_equivalence_proved': True,
        'object_Packet_token_actual_table_dispatch_proved': True,
        'object_Packet_token_relational_condition_recursive_equation_proved': True,
        'object_Packet_token_actual_two_radix_system_constructed': True,
        'object_Packet_token_all_internal_canonical_arithmetic_proved': False,
        'object_Packet_token_actual_execution_total_unique_proved': True,
        "Packet_quotient_descent_and_induction_guard": Packet_quotient_descent_and_induction,
        'object_Packet_internal_quotient_weak_and_strict_descent_proved': True,
        'object_Packet_internal_quotient_exact_stopping_threshold_proved': True,
        'object_Packet_internal_quotient_zero_output_exact_fields_proved': True,
        'object_Packet_internal_quotient_recursion_induction_schema_proved': True,
        'object_Packet_relational_affine_all_internal_descent_contract_proved': True,
        'object_Packet_internal_quotient_descent_literal_system_constructed': True,
        "Packet_internal_radix_division_guard": Packet_internal_radix_division,
        'object_Packet_radix_division_all_internal_output_exists_proved': True,
        'object_Packet_radix_division_internal_quotient_bands_disjoint_proved': True,
        'object_Packet_radix_division_unique_inverse_fiber_proved': True,
        'object_Packet_radix_division_exact_internal_domain_proved': True,
        'object_Packet_relational_affine_inverse_exists_unique_proved': True,
        'object_Packet_radix_division_actual_literal_system_constructed': True,
        "Packet_relational_affine_arithmetic_guard": Packet_relational_affine_arithmetic,
        'object_Packet_affine_exact_root_predecessor_equation_proved': True,
        'object_Packet_relational_affine_internal_omega_IH_discharged': True,
        'object_Packet_relational_affine_condition_exact_arithmetic_proved': True,
        'object_Packet_relational_affine_all_internal_acceptance_iff_proved': True,
        'object_Packet_relational_affine_literal_arithmetic_system_constructed': True,
        'object_Packet_relational_affine_execution_total_unique_proved': True,

        'object_Horn_explicit_table_internal_closed_trace_value_constructed': True,
        'object_Packet_actual_ten_rule_relational_trace_system_constructed': True,
        'object_Packet_actual_ten_rule_affine_root_dispatch_proved': True,
        'object_Packet_relational_condition_all_internal_unfold_proved': True,
        'object_Packet_relational_affine_base_successor_acceptance_proved': True,
        'object_Packet_original_Basic_AST_condition_translation_proved': False,

        'object_Packet_original_affine_head_search_bounds_proved': True,
        'object_Packet_original_affine_full_arity_application_iff_proved': True,
        'object_Packet_original_affine_all_internal_application_law_proved': True,
        'object_Packet_original_affine_literal_application_system_constructed': True,

        'object_Packet_original_addConst_graph_addition_correspondence_proved': True,
        'object_Packet_original_affine_local_matrix_equivalence_proved': True,
        'object_Packet_original_affine_all_internal_local_laws_proved': True,
        'object_Packet_original_affine_literal_matrix_system_constructed': True,

        'object_Packet_128_256_affine_arithmetic_total_unique_proved': True,
        'object_Packet_affine_all_internal_recursive_equation_proved': True,
        'object_Packet_actual_literal_radix_systems_constructed': True,
        'object_Packet_actual_Horn_affine_condition_correspondence_proved': False,
        'object_full_NatPacket_byte_tree_bridge_proved': False,
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
        "sha256": {str(path.relative_to(ROOT)).replace("\\", "/"): hashlib.sha256(path.read_bytes()).hexdigest() for path in hashed},
    }
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    print(f"PASS: {len(footprints)} audited declarations; "
          f"{summary['declarations_without_axioms']} without axioms; "
          f"{summary['declarations_with_allowed_axioms']} with recorded dependencies; "
          f"{summary['warning_lines']} warning lines; inherited native certificate axioms recorded.")


if __name__ == "__main__":
    main()

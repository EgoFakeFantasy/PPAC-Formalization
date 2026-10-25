import PPAC
open PPAC.Migration
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.SetTheory
example : FirstOrder.Sentence ℒ := PP
example : FirstOrder.Sentence ℒ := ACwo
example : FirstOrder.Theory ℒ := nativeZF
example : FirstOrder.Derives targetTheory [] PP := target_derives_PP
example : FirstOrder.Derives targetTheory [] (.neg AC) := target_derives_notAC
example : Consistent targetTheory → ¬ FirstOrder.Derives targetTheory [] AC :=
  no_AC_of_target_consistent
-- 新 binder 在原生列表头，源原有变量退后一格。
example : Translation.lift (fun _ : Fin 1 => (.here :
    FirstOrder.Variable [SetSort.set] SetSort.set)) (Fin.last 1) =
    FirstOrder.Variable.here := rfl
example : Translation.lift (fun _ : Fin 1 => (.here :
    FirstOrder.Variable [SetSort.set] SetSort.set)) (0 : Fin 2) =
    FirstOrder.Variable.there FirstOrder.Variable.here := rfl

-- Exact inherited native recursion certificates; finite Bool checks, no new proof axiom.
open Lean Elab Command
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
run_cmd do
  let names : List Name := [
    `YesMetaZFC.SetTheory.Structure.IsOrdinal.classify._native.prove_auto_native_dag_clause_compile.ax_1_18,
    `YesMetaZFC.SetTheory.Structure.IsOrdinal.classify._native.prove_auto_native_preprocessing.ax_1_16,
    `YesMetaZFC.SetTheory.Structure.IsOrdinal.classify._native.prove_auto_native_replay_material.ax_1_17,
    `YesMetaZFC.SetTheory.Structure.IsRecursiveSequence.restriction._native.prove_auto_native_dag_clause_compile.ax_1_3,
    `YesMetaZFC.SetTheory.Structure.IsRecursiveSequence.restriction._native.prove_auto_native_dag_clause_compile.ax_1_6,
    `YesMetaZFC.SetTheory.Structure.IsRecursiveSequence.restriction._native.prove_auto_native_preprocessing.ax_1_1,
    `YesMetaZFC.SetTheory.Structure.IsRecursiveSequence.restriction._native.prove_auto_native_preprocessing.ax_1_4,
    `YesMetaZFC.SetTheory.Structure.IsRecursiveSequence.restriction._native.prove_auto_native_replay_material.ax_1_2,
    `YesMetaZFC.SetTheory.Structure.IsRecursiveSequence.restriction._native.prove_auto_native_replay_material.ax_1_5,
    `YesMetaZFC.SetTheory.Structure.IsSuccessorLengthSequenceWithLast.not_limitLength._native.prove_auto_native_dag_clause_compile.ax_1_3,
    `YesMetaZFC.SetTheory.Structure.IsSuccessorLengthSequenceWithLast.not_limitLength._native.prove_auto_native_preprocessing.ax_1_1,
    `YesMetaZFC.SetTheory.Structure.IsSuccessorLengthSequenceWithLast.not_limitLength._native.prove_auto_native_replay_material.ax_1_2,
    `YesMetaZFC.SetTheory.Structure.IsZeroLengthSequence.not_successorLength._native.prove_auto_native_dag_clause_compile.ax_1_3,
    `YesMetaZFC.SetTheory.Structure.IsZeroLengthSequence.not_successorLength._native.prove_auto_native_preprocessing.ax_1_1,
    `YesMetaZFC.SetTheory.Structure.IsZeroLengthSequence.not_successorLength._native.prove_auto_native_replay_material.ax_1_2]
  for name in names do
    let info ← getConstInfo name
    let args := info.type.getAppArgs
    unless info.type.isAppOfArity ``Eq 3 && args[0]! == mkConst ``Bool do
      throwError "Unexpected native recursion certificate type: {name}"
    let left ← liftTermElabM (Meta.evalExpr Bool (mkConst ``Bool) args[1]!)
    let right ← liftTermElabM (Meta.evalExpr Bool (mkConst ``Bool) args[2]!)
    unless left && right do throwError "False native recursion certificate: {name}"
  logInfo m!"Rechecked {names.length} pinned native recursion Bool certificates"

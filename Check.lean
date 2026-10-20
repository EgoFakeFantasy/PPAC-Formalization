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

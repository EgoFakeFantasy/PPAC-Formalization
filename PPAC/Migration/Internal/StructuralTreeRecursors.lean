import PPAC.Migration.Internal.StructuralTreeOperatorStep

/-! 具体树前段算子的总单值前提实际消去，取得全部内部序数上的唯一完整递归图。 -/
namespace PPAC.Migration.Internal.StructuralTreeRecursors
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralTreeOperatorSyntax
open NaturalAdditionTransport (params3)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem all_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e : Fin m) : Derives Γ (recursors w z e) := by
  have hc := ZFContext.closed hZ (ObjectTransfiniteRecursion.source_uniqueness matrix)
  have hi := specialize_close
    ((OrdinalRecursionTotal.total matrix (id : Fin 3 → Fin 3)).imp
      ((OrdinalRecursionDeterminism.deterministic matrix id).imp (OrdinalRecursionExistenceSyntax.allUnique matrix id)))
    (params3 w z e) hc
  have h : Derives Γ ((OrdinalRecursionTotal.total matrix (params3 w z e)).imp
      ((OrdinalRecursionDeterminism.deterministic matrix (params3 w z e)).imp (recursors w z e))) := by
    simpa only [Formula.rename, OrdinalRecursionTotal.total_rename, OrdinalRecursionDeterminism.deterministic_rename,
      OrdinalRecursionExistenceSyntax.allUnique_rename, id_eq, recursors] using hi
  exact .impE (.impE h (StructuralTreeOperatorStep.total (params3 w z e))) (StructuralTreeOperatorStep.deterministic (params3 w z e))

theorem at_ordinal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e a : Fin m)
    (ha : Derives Γ (OrdinalSyntax.ordinal a)) : Derives Γ (OrdinalRecursionExistenceSyntax.fiber matrix (params3 w z e) a) := by
  have h : Derives Γ ((OrdinalSyntax.ordinal a).imp (OrdinalRecursionExistenceSyntax.fiber matrix (params3 w z e) a)) := by
    simpa only [recursors, OrdinalRecursionExistenceSyntax.allUnique, Formula.instantiate, Formula.rename,
      OrdinalSyntax.ordinal_rename, OrdinalRecursionExistenceSyntax.fiber_rename, ReplacementPredicates.paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE a (all_unique hZ w z e)
  exact .impE h ha

theorem actual_units_recursors {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (actualRecursors w) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hr := all_unique hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  have hout : Derives Δ (actualRecursors w.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc
    apply Derives.exI (Fin.last (m+1))
    simp only [Formula.instantiate, Formula.rename, empty_rename, successor_rename, recursors_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hU hr
  simpa only [Formula.raise, actualRecursors_rename] using hout
end PPAC.Migration.Internal.StructuralTreeRecursors

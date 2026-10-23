import PPAC.Migration.Internal.SyntaxMixedFormulaRecursionStep

/-! 全11类具体混合替换状态算子的原递归图实际存在唯一；原幂集提供真实集合值载体。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaRecursors
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic SyntaxMixedFormulaRecursionSyntax SyntaxMixedFormulaQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem all_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) : Derives Γ (recursors w) := by
  have hc := ZFContext.closed hZ (ObjectTransfiniteRecursion.source_uniqueness matrix)
  have hi := specialize_close
    ((OrdinalRecursionTotal.total matrix (id : Fin 1 → Fin 1)).imp
      ((OrdinalRecursionDeterminism.deterministic matrix id).imp (OrdinalRecursionExistenceSyntax.allUnique matrix id)))
    (one w) hc
  have hh : Derives Γ ((OrdinalRecursionTotal.total matrix (one w)).imp
      ((OrdinalRecursionDeterminism.deterministic matrix (one w)).imp (recursors w))) := by
    simpa only [Formula.rename, OrdinalRecursionTotal.total_rename, OrdinalRecursionDeterminism.deterministic_rename,
      OrdinalRecursionExistenceSyntax.allUnique_rename, id_eq, recursors] using hi
  exact .impE (.impE hh (SyntaxMixedFormulaRecursionStep.total hZ (one w))) (SyntaxMixedFormulaRecursionStep.deterministic hZ (one w))

theorem at_ordinal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d : Fin m)
    (hd : Derives Γ (OrdinalSyntax.ordinal d)) : Derives Γ (OrdinalRecursionExistenceSyntax.fiber matrix (one w) d) := by
  have hh : Derives Γ ((OrdinalSyntax.ordinal d).imp (OrdinalRecursionExistenceSyntax.fiber matrix (one w) d)) := by
    simpa only [recursors, OrdinalRecursionExistenceSyntax.allUnique, Formula.instantiate, Formula.rename,
      OrdinalSyntax.ordinal_rename, OrdinalRecursionExistenceSyntax.fiber_rename, ReplacementPredicates.paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE d (all_unique hZ w)
  exact .impE hh hd

theorem exists_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d : Fin m)
    (hd : Derives Γ (OrdinalSyntax.ordinal d)) : Derives Γ (graphExists w d) := by
  have hf := at_ordinal hZ w d hd
  let F := (graph w.castSucc (Fin.last m) d.castSucc).conj
    (OrdinalRecursionExistenceSyntax.uniqueAt matrix (one w.castSucc) d.castSucc (Fin.last m))
  let Δ := Context.add F (Context.image Formula.raise Γ)
  have hρ : ReplacementPredicates.paramsUp (one w) = one w.castSucc := rfl
  have he : Derives Γ (.ex F) := by simpa only [F, OrdinalRecursionExistenceSyntax.fiber, graph, hρ] using hf
  apply Derives.exE (p := F) he
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hout : Derives Δ (graphExists w.castSucc d.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, graph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjL hF
  exact of_eq (graphExists_rename w d Fin.castSucc).symm hout

theorem actual_carrier_recursors {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) :
    Derives Γ (actualRecursors w) := by
  have he := PowerSetSyntax.power_instance w (Derives.hyp (hZ _ ⟨_, Source.SetLanguage.IsZFAxiom.powerSet, rfl⟩))
  let P := PowerSetSyntax.powerOf (Fin.last m) w.castSucc
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hp : Derives Δ P := .hyp (Or.inl rfl)
  have hr := all_unique (ZFContext.under hZ P) w.castSucc
  have ho : Derives Δ (actualRecursors w.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, PowerSetSyntax.powerOf_rename, recursors_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hp hr
  exact of_eq (actualRecursors_rename w Fin.castSucc).symm ho
theorem existence {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) :
    Derives Γ (existsSystem.rename Fin.elim0) := by
  have he := ZFContext.closed hZ ObjectOmega.source_ZF_existence
  let W := OmegaSyntax.omega (Fin.last m)
  let Δ := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at he
  apply Derives.exE (p := W) he
  have hW : Derives Δ W := .hyp (Or.inl rfl)
  have hs := actual_carrier_recursors (ZFContext.under hZ W) (Fin.last m)
  have ho : Derives Δ (existsSystem.rename Fin.elim0) := by
    simp only [existsSystem, Formula.rename, OmegaSyntax.omega_rename, actualRecursors_rename, Formula.liftRen, Fin.lastCases_last]
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [W, Formula.instantiate, Formula.rename, OmegaSyntax.omega_rename, actualRecursors_rename,
      Fin.lastCases_last]) (.conjI hW hs)
  exact of_eq (closed_rename existsSystem Fin.castSucc).symm ho
end PPAC.Migration.Internal.SyntaxMixedFormulaRecursors

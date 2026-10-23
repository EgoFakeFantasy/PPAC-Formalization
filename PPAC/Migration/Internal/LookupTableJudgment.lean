import PPAC.Migration.Internal.LookupTableExecutionSyntax

/-! 独立表码递归执行与真实状态成员、历史边查询的全内部对应。 -/
namespace PPAC.Migration.Internal.LookupTableJudgment
open Source SourceAlgebra SourceLogic OmegaSyntax LookupTableProgramSyntax LookupTableEvaluationSyntax LookupTableExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem parameters_legal {m} {Γ : Context m} (w n i y : Fin m) (he : Derives Γ (executed w n i y)) :
    Derives Γ (legal w i y) := by
  let B := LookupTableExecutionSyntax.body w n i y
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (.conjR he)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (legal_rename w i y Fin.castSucc).symm (LookupTableState.contains_legal w.castSucc (Fin.last m) i.castSucc y.castSucc (.conjR hB))

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y v : Fin m)
    (hn : Derives Γ (OrdinalSyntax.ordinal n)) (hnw : Derives Γ (.mem n w)) (hv : Derives Γ (evaluation w n v)) :
    Derives Γ ((executed w n i y).iff (contains w v i y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let C := executed w n i y
    let B := LookupTableExecutionSyntax.body w n i y
    let Δ := Context.add B (Context.image Formula.raise (Context.add C Γ))
    apply Derives.exE (p := B) (.conjR (.hyp (Or.inl rfl)))
    have hn1 : Derives Δ (OrdinalSyntax.ordinal n.castSucc) := of_eq (OrdinalSyntax.ordinal_rename n Fin.castSucc) (under (add hn C) B)
    have hv1 : Derives Δ (evaluation w.castSucc n.castSucc v.castSucc) := of_eq (evaluation_rename w n v Fin.castSucc) (under (add hv C) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hEq := LookupTableEvaluationUnique.unique (ZFContext.under (ZFContext.add hZ C) B) w.castSucc n.castSucc (Fin.last m) v.castSucc hn1 (.conjL hB) hv1
    exact of_eq (contains_rename w v i y Fin.castSucc).symm (contains_subst_set w.castSucc (Fin.last m) v.castSucc i.castSucc y.castSucc hEq (.conjR hB))
  · apply Derives.impI
    exact intro_executed w n i y v (add hnw _) (add hv _) (.hyp (Or.inl rfl))

theorem read_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h d n i y : Fin m)
    (hd : Derives Γ (OrdinalSyntax.ordinal d)) (hn : Derives Γ (.mem n d)) (hnw : Derives Γ (.mem n w))
    (hg : Derives Γ (LookupTableRecursionSyntax.graph w h d)) :
    Derives Γ ((read w h n i y).iff (executed w n i y)) := by
  have hh : Derives Γ ((read w h n i y).iff (.ex
      ((evaluation w.castSucc n.castSucc (Fin.last m)).conj (contains w.castSucc (Fin.last m) i.castSucc y.castSucc)))) := by
    apply FormulaCodeCongruence.ex_congr
    have hd1 : Derives (Context.image Formula.raise Γ) (OrdinalSyntax.ordinal d.castSucc) := of_eq (OrdinalSyntax.ordinal_rename d Fin.castSucc) (Derives.rename Fin.castSucc hd)
    have hg1 : Derives (Context.image Formula.raise Γ) (LookupTableRecursionSyntax.graph w.castSucc h.castSucc d.castSucc) := of_eq (LookupTableRecursionSyntax.graph_rename w h d Fin.castSucc) (Derives.rename Fin.castSucc hg)
    exact FormulaCodeCongruence.conj_congr
      (LookupTableGraphValues.edge_iff_value (ZFContext.rename hZ Fin.castSucc) w.castSucc h.castSucc d.castSucc n.castSucc (Fin.last m) hd1 (Derives.rename Fin.castSucc hn) hg1)
      (SyntaxTypeLocalTransfer.iff_refl _)
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (add hnw _) (.impE (add (.conjL hh) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hh) _) (.conjR (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.LookupTableJudgment

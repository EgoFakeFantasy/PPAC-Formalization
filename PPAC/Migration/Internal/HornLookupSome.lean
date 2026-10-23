import PPAC.Migration.Internal.HornLookupSomeSyntax

/-! 全部内部运行时候选的原全表编译轨迹成功图与真实查找执行及无输出双向对应。 -/
namespace PPAC.Migration.Internal.HornLookupSome
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax HornLookupSomeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem execution_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((returned w n i y).iff (LookupTableExecutionSyntax.executed w n i y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := returned w n i y
    let B := (row w.castSucc n.castSucc i.castSucc y.castSucc (Fin.last m)).conj (HornLookupSearchCondition.condition w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (.conjL (HornLookupSearchCondition.execution_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ _ hw1 (.conjL hB))) (.conjR hB)
    exact of_eq (LookupTableExecutionSyntax.executed_rename w n i y Fin.castSucc).symm ho
  · apply Derives.impI
    let E := LookupTableExecutionSyntax.executed w n i y
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ0 := ZFContext.add hZ E
    have hi := LookupTableJudgment.parameters_legal w n i y hE
    have hex := exists_row hZ0 w n i y (add hw E) (.conjL hE) (.conjL hi) (.conjR hi)
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (row w.castSucc n.castSucc i.castSucc y.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) hex
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have he1 : Derives Δ (LookupTableExecutionSyntax.executed w.castSucc n.castSucc i.castSucc y.castSucc) := of_eq (LookupTableExecutionSyntax.executed_rename w n i y Fin.castSucc) (under hE B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hc := Derives.impE (.conjR (HornLookupSearchCondition.execution_iff (ZFContext.under hZ0 B) _ _ _ _ _ hw1 (.conjR hB))) he1
    have ho := intro_returned _ _ _ _ _ (.conjR hB) hc
    exact of_eq (returned_rename w n i y Fin.castSucc).symm ho

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((returned w n i y).iff (StrictLookupSyntax.checked w n i y)) :=
  SyntaxTypeLocalTransfer.iff_trans (execution_iff hZ w n i y hw) (LookupTableCorrectness.execution_iff_checked hZ w n i y hw)

theorem has_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((hasOutput w n i).iff (LookupTableOutcomeSyntax.hasOutput w n i)) := by
  apply FormulaCodeCongruence.ex_congr
  exact execution_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc n.castSucc i.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw))

theorem no_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((noOutput w n i).iff (LookupTableOutcomeSyntax.noOutput w n i)) :=
  FormulaTransformCongruence.imp_congr (has_output_iff hZ w n i hw) (SyntaxTypeLocalTransfer.iff_refl .bot)

theorem strict_no_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((noOutput w n i).iff (StrictLookupSyntax.rejected w n i)) :=
  SyntaxTypeLocalTransfer.iff_trans (no_output_iff hZ w n i hw) (LookupTableOutcome.no_output_iff hZ w n i hw hn hi)

end PPAC.Migration.Internal.HornLookupSome

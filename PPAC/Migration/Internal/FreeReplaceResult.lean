import PPAC.Migration.Internal.FreeReplaceResultRows

/-! 原mode3自由变量成功图对任意内部候选的精确域与执行双条件。 -/
namespace PPAC.Migration.Internal.FreeReplaceResult
open Source SourceAlgebra SourceLogic OmegaSyntax FreeReplaceResultSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem returned_guard {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (returned w d p x idx y)) : Derives Γ (guard w d x idx) := by
  let B := (root w.castSucc d.castSucc p.castSucc x.castSucc y.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (.conjR hr)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc idx.castSucc x.castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w idx x Fin.castSucc) (under (.conjL hr) B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hd := FreeReplaceResultRows.depth_natural (ZFContext.under hZ B) _ _ _ _ _ _ hw1 (.conjL hB)
  exact of_eq (guard_rename w d x idx Fin.castSucc).symm (.conjI hd hv1)

theorem returned_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (returned w d p x idx y)) :
    Derives Γ (LookupTableExecutionSyntax.executed w p idx y) := by
  let B := (root w.castSucc d.castSucc p.castSucc x.castSucc y.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (.conjR hr)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc idx.castSucc x.castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w idx x Fin.castSucc) (under (.conjL hr) B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := Derives.impE (.conjL (FreeReplaceResultRows.trace_iff_execution (ZFContext.under hZ B) _ _ _ _ _ _ _ hw1 hv1 (.conjL hB))) (.conjR hB)
  exact of_eq (LookupTableExecutionSyntax.executed_rename w p idx y Fin.castSucc).symm ho

theorem execution_returned {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d x idx))
    (he : Derives Γ (LookupTableExecutionSyntax.executed w p idx y)) : Derives Γ (returned w d p x idx y) := by
  have hvar := Derives.conjR hg
  have hx := HornVariableValue.code_natural hZ false w idx x hw hvar
  have hy := Derives.conjR (LookupTableJudgment.parameters_legal w p idx y he)
  have hex := FreeReplaceResultRows.exists_root hZ w d p x y hw (.conjL hg) (.conjL he) hx hy
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (root w.castSucc d.castSucc p.castSucc x.castSucc y.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hex
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc idx.castSucc x.castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w idx x Fin.castSucc) (under hvar B)
  have he1 : Derives Δ (LookupTableExecutionSyntax.executed w.castSucc p.castSucc idx.castSucc y.castSucc) := of_eq (LookupTableExecutionSyntax.executed_rename w p idx y Fin.castSucc) (under he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := Derives.impE (.conjR (FreeReplaceResultRows.trace_iff_execution (ZFContext.under hZ B) _ _ _ _ _ _ _ hw1 hv1 (.conjR hB))) he1
  have ho := Derives.conjI hv1 (intro_run _ _ _ _ _ _ (.conjR hB) ht)
  exact of_eq (returned_rename w d p x idx y Fin.castSucc).symm ho

theorem returned_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((returned w d p x idx y).iff ((guard w d x idx).conj (LookupTableExecutionSyntax.executed w p idx y))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (returned_guard (ZFContext.add hZ _) w d p x idx y (add hw _) (.hyp (Or.inl rfl)))
      (returned_execution (ZFContext.add hZ _) w d p x idx y (add hw _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact execution_returned (ZFContext.add hZ _) w d p x idx y (add hw _) (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl)))

theorem under_guard_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d x idx)) :
    Derives Γ ((returned w d p x idx y).iff (LookupTableExecutionSyntax.executed w p idx y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact returned_execution (ZFContext.add hZ _) w d p x idx y (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact execution_returned (ZFContext.add hZ _) w d p x idx y (add hw _) (add hg _) (.hyp (Or.inl rfl))

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((returned w d p x idx y).iff ((guard w d x idx).conj (StrictLookupSyntax.checked w p idx y))) :=
  SyntaxTypeLocalTransfer.iff_trans (returned_iff hZ w d p x idx y hw)
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl (guard w d x idx)) (LookupTableCorrectness.execution_iff_checked hZ w p idx y hw))

theorem strict_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d x idx)) (hp : Derives Γ (.mem p w)) :
    Derives Γ ((returned w d p x idx y).iff (StrictLookupSyntax.returned w p idx y)) :=
  SyntaxTypeLocalTransfer.iff_trans (under_guard_iff hZ w d p x idx y hw hg)
    (LookupTableCorrectnessInduction.execution_iff_at_natural hZ w p idx y hw hp (SyntaxVariableDecode.index_natural false w idx x (.conjR hg)))

theorem rejected_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((returned w d p x idx y).neg.iff ((guard w d x idx).conj (LookupTableExecutionSyntax.executed w p idx y)).neg) :=
  FormulaTransformCongruence.imp_congr (returned_iff hZ w d p x idx y hw) (SyntaxTypeLocalTransfer.iff_refl .bot)

end PPAC.Migration.Internal.FreeReplaceResult

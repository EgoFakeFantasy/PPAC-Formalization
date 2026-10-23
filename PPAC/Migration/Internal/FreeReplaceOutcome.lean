import PPAC.Migration.Internal.FreeReplaceResult

/-! 原mode3自由替换的全部内部有输出／无输出、非法域拒绝和单值性。 -/
namespace PPAC.Migration.Internal.FreeReplaceOutcome
open Source SourceAlgebra SourceLogic OmegaSyntax FreeReplaceResultSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem intro_has_output {m} {Γ : Context m} (w d p x idx y : Fin m)
    (hr : Derives Γ (returned w d p x idx y)) : Derives Γ (hasOutput w d p x idx) := by
  apply Derives.exI y
  exact of_eq (by simp only [Formula.instantiate, returned_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr

theorem has_output_iff_guarded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((hasOutput w d p x idx).iff ((guard w d x idx).conj (LookupTableOutcomeSyntax.hasOutput w p idx))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := hasOutput w d p x idx
    let B := returned w.castSucc d.castSucc p.castSucc x.castSucc idx.castSucc (Fin.last m)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hg := FreeReplaceResult.returned_guard hZ1 _ _ _ _ _ _ hw1 hB
    have he := FreeReplaceResult.returned_execution hZ1 _ _ _ _ _ _ hw1 hB
    have hh : Derives Δ (LookupTableOutcomeSyntax.hasOutput w.castSucc p.castSucc idx.castSucc) := by
      apply Derives.exI (Fin.last m)
      exact of_eq (by simp only [Formula.instantiate, LookupTableExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he
    have ho := Derives.conjI hg hh
    simpa only [Formula.raise, Formula.rename, guard_rename, LookupTableOutcomeSyntax.hasOutput_rename] using ho
  · apply Derives.impI
    let E := (guard w d x idx).conj (LookupTableOutcomeSyntax.hasOutput w p idx)
    let B := LookupTableExecutionSyntax.executed w.castSucc p.castSucc idx.castSucc (Fin.last m)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.conjR (.hyp (Or.inl rfl)))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hg1 : Derives Δ (guard w.castSucc d.castSucc x.castSucc idx.castSucc) := of_eq (guard_rename w d x idx Fin.castSucc)
      (under (Derives.conjL (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl))) B)
    have hr := FreeReplaceResult.execution_returned hZ1 _ _ _ _ _ _ hw1 hg1 (.hyp (Or.inl rfl))
    exact of_eq (hasOutput_rename w d p x idx Fin.castSucc).symm (intro_has_output _ _ _ _ _ _ hr)

theorem no_output_iff_guarded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((noOutput w d p x idx).iff ((guard w d x idx).conj (LookupTableOutcomeSyntax.hasOutput w p idx)).neg) :=
  FormulaTransformCongruence.imp_congr (has_output_iff_guarded hZ w d p x idx hw) (SyntaxTypeLocalTransfer.iff_refl .bot)

theorem has_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d x idx)) :
    Derives Γ ((hasOutput w d p x idx).iff (LookupTableOutcomeSyntax.hasOutput w p idx)) := by
  have hh := has_output_iff_guarded hZ w d p x idx hw
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL hh) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hh) _) (.conjI (add hg _) (.hyp (Or.inl rfl)))

theorem no_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d x idx)) :
    Derives Γ ((noOutput w d p x idx).iff (LookupTableOutcomeSyntax.noOutput w p idx)) :=
  FormulaTransformCongruence.imp_congr (has_output_iff hZ w d p x idx hw hg) (SyntaxTypeLocalTransfer.iff_refl .bot)

theorem strict_no_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d x idx)) (hp : Derives Γ (.mem p w)) :
    Derives Γ ((noOutput w d p x idx).iff (StrictLookupSyntax.rejected w p idx)) :=
  SyntaxTypeLocalTransfer.iff_trans (no_output_iff hZ w d p x idx hw hg)
    (LookupTableOutcome.no_output_iff hZ w p idx hw hp (SyntaxVariableDecode.index_natural false w idx x (.conjR hg)))

theorem invalid_guard_no_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d x idx).neg) : Derives Γ (noOutput w d p x idx) := by
  have hh := has_output_iff_guarded hZ w d p x idx hw
  apply Derives.impI
  exact .impE (add hg _) (.conjL (.impE (add (.conjL hh) _) (.hyp (Or.inl rfl))))

theorem invalid_output_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (Formula.mem y w).neg) : Derives Γ (returned w d p x idx y).neg := by
  apply Derives.impI
  have he := FreeReplaceResult.returned_execution (ZFContext.add hZ _) w d p x idx y (add hw _) (.hyp (Or.inl rfl))
  exact .impE (add hy _) (.conjR (LookupTableJudgment.parameters_legal w p idx y he))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (returned w d p x idx y)) (hz : Derives Γ (returned w d p x idx z)) :
    Derives Γ (.equal y z) := LookupTableOutcome.unique hZ w p idx y z hw
      (FreeReplaceResult.returned_execution hZ w d p x idx y hw hy) (FreeReplaceResult.returned_execution hZ w d p x idx z hw hz)

end PPAC.Migration.Internal.FreeReplaceOutcome
